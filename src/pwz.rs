use crate::{
    core::{CoreGrammar, CoreProduction, CoreSymbol},
    grammar::{Grammar, Symbol, TerminalId},
    grammar_flow::{GrammarFlowAnalysis, TerminalSet},
};

use thiserror::Error;

const NO_INDEX: u32 = u32::MAX;
const NO_POSITION: usize = usize::MAX;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PwzStats {
    /// Successful PwZ derivatives executed so far.
    ///
    /// Calls made after the recognizer reaches its absorbing dead state do not
    /// execute another derivative and therefore do not increase this value.
    pub derivatives: usize,
    pub events: usize,
    pub memo_records: usize,
}

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum PwzError {
    #[error("start nonterminal {start} is outside 0..{nonterminal_count}")]
    InvalidStart {
        start: usize,
        nonterminal_count: usize,
    },
    #[error("production {production} has invalid left-hand side {lhs}")]
    InvalidProductionLhs { production: usize, lhs: usize },
    #[error("production {production} references invalid nonterminal {nonterminal}")]
    InvalidNonterminal {
        production: usize,
        nonterminal: usize,
    },
    #[error("production {production} references invalid terminal {terminal}")]
    InvalidTerminal { production: usize, terminal: usize },
    #[error("the compiled grammar exceeds the recognizer's arena-ID capacity")]
    GrammarTooLarge,
    #[error("the streaming recognizer exhausted its compact arena-ID capacity")]
    ArenaCapacityExceeded,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExprId(u32);

impl ExprId {
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MemoId(u32);

impl MemoId {
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ContextId(u32);

impl ContextId {
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
enum Lookahead {
    Empty,
    One(u32),
    Many(Box<[u64]>),
}

impl Lookahead {
    fn from_set(set: &TerminalSet) -> Result<Self, PwzError> {
        let mut only = None;
        let mut count = 0usize;
        for (word_index, &word) in set.words().iter().enumerate() {
            let mut remaining = word;
            while remaining != 0 {
                let bit = remaining.trailing_zeros() as usize;
                count += 1;
                if count > 1 {
                    return Ok(Self::Many(set.words().into()));
                }
                only = Some(
                    u32::try_from(word_index * 64 + bit).map_err(|_| PwzError::GrammarTooLarge)?,
                );
                remaining &= remaining - 1;
            }
        }
        Ok(match only {
            Some(terminal) => Self::One(terminal),
            None => Self::Empty,
        })
    }

    #[inline]
    fn contains(&self, terminal: usize) -> bool {
        match self {
            Self::Empty => false,
            Self::One(expected) => *expected as usize == terminal,
            Self::Many(words) => words
                .get(terminal / 64)
                .is_some_and(|word| word & (1u64 << (terminal % 64)) != 0),
        }
    }
}

#[derive(Clone, Debug)]
enum ExprKind {
    Terminal(usize),
    /// A range in `edges` containing the productive productions.
    Alternative {
        edge_start: u32,
        edge_len: u32,
    },
    /// A range in `edges` containing the production right-hand side.
    Sequence {
        edge_start: u32,
        edge_len: u32,
        lookahead: Lookahead,
    },
}

#[derive(Clone, Debug)]
struct Expr {
    kind: ExprKind,
    /// PwZ's mutable memo cell. The pair is valid exactly at `memo_position`.
    memo_position: usize,
    memo: MemoId,
}

#[derive(Clone, Copy, Debug)]
enum Context {
    Top,
    /// The result of an alternative's child flows to the alternative memo.
    Alternative(MemoId),
    /// Resume a production at `next` when the current child finishes.
    Sequence {
        memo: MemoId,
        sequence: ExprId,
        next: u32,
    },
}

#[derive(Clone, Copy, Debug)]
struct ParentLink {
    context: ContextId,
    next: u32,
}

#[derive(Clone, Copy, Debug)]
struct Memo {
    parent_head: u32,
    completed_end: usize,
}

#[derive(Clone, Copy, Debug)]
enum Event {
    Down {
        expression: ExprId,
        context: ContextId,
    },
    Eval {
        expression: ExprId,
        memo: MemoId,
    },
    Up(MemoId),
    Apply(ContextId),
}

/// Recognition-only Parsing with Zippers state over a normalized CFG.
///
/// Expression nodes are immutable except for the one-entry PwZ memo cell.
/// Parse-tree values are erased: a memo records only whether the expression
/// completed at the current end position. That is sufficient for prefix
/// recognition and turns all recursive calls in the presentation of PwZ into
/// the `events` arena-backed work stack below.
pub(crate) struct PwzCore {
    expressions: Vec<Expr>,
    edges: Vec<ExprId>,
    start: ExprId,
    terminal_count: usize,

    memos: Vec<Memo>,
    contexts: Vec<Context>,
    parent_links: Vec<ParentLink>,
    events: Vec<Event>,
    frontier: Vec<MemoId>,
    next_frontier: Vec<MemoId>,

    position: usize,
    live: bool,
    arena_exhausted: bool,
    stats: PwzStats,
}

impl PwzCore {
    pub(crate) fn compile(grammar: &CoreGrammar) -> Result<Self, PwzError> {
        validate(grammar)?;

        let flow = GrammarFlowAnalysis::compute(grammar);
        let production_is_productive = flow.productive_productions();

        let productive_count = production_is_productive
            .iter()
            .filter(|productive| **productive)
            .count();
        let expression_count = grammar
            .nonterminal_count
            .checked_add(grammar.terminal_count)
            .and_then(|count| count.checked_add(productive_count))
            .ok_or(PwzError::GrammarTooLarge)?;
        if expression_count >= NO_INDEX as usize {
            return Err(PwzError::GrammarTooLarge);
        }
        let rhs_edge_count = grammar
            .productions
            .iter()
            .zip(production_is_productive)
            .filter(|(_, productive)| **productive)
            .try_fold(0usize, |total, (production, _)| {
                total.checked_add(production.rhs.len())
            })
            .ok_or(PwzError::GrammarTooLarge)?;
        let edge_count = rhs_edge_count
            .checked_add(productive_count)
            .ok_or(PwzError::GrammarTooLarge)?;
        if edge_count >= NO_INDEX as usize
            || grammar
                .productions
                .iter()
                .any(|production| production.rhs.len() >= NO_INDEX as usize)
        {
            return Err(PwzError::GrammarTooLarge);
        }

        let mut expressions = Vec::with_capacity(expression_count);
        for _ in 0..grammar.nonterminal_count {
            expressions.push(Expr {
                kind: ExprKind::Alternative {
                    edge_start: 0,
                    edge_len: 0,
                },
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
        }
        for terminal in 0..grammar.terminal_count {
            expressions.push(Expr {
                kind: ExprKind::Terminal(terminal),
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
        }

        let mut edges = Vec::with_capacity(edge_count);
        let mut alternatives = vec![Vec::<ExprId>::new(); grammar.nonterminal_count];
        for (production_index, production) in grammar.productions.iter().enumerate() {
            if !production_is_productive[production_index] {
                continue;
            }
            let edge_start = u32::try_from(edges.len()).map_err(|_| PwzError::GrammarTooLarge)?;
            for symbol in &production.rhs {
                let expression = match *symbol {
                    CoreSymbol::Nonterminal(nonterminal) => {
                        ExprId(u32::try_from(nonterminal).map_err(|_| PwzError::GrammarTooLarge)?)
                    }
                    CoreSymbol::Terminal(terminal) => ExprId(
                        u32::try_from(grammar.nonterminal_count + terminal)
                            .map_err(|_| PwzError::GrammarTooLarge)?,
                    ),
                };
                edges.push(expression);
            }

            let expression =
                ExprId(u32::try_from(expressions.len()).map_err(|_| PwzError::GrammarTooLarge)?);
            expressions.push(Expr {
                kind: ExprKind::Sequence {
                    edge_start,
                    edge_len: u32::try_from(production.rhs.len())
                        .map_err(|_| PwzError::GrammarTooLarge)?,
                    lookahead: Lookahead::from_set(flow.select(production_index))?,
                },
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
            alternatives[production.lhs].push(expression);
        }

        for (nonterminal, children) in alternatives.into_iter().enumerate() {
            let edge_start = u32::try_from(edges.len()).map_err(|_| PwzError::GrammarTooLarge)?;
            let edge_len = u32::try_from(children.len()).map_err(|_| PwzError::GrammarTooLarge)?;
            edges.extend(children);
            expressions[nonterminal].kind = ExprKind::Alternative {
                edge_start,
                edge_len,
            };
        }

        let start = ExprId(u32::try_from(grammar.start).map_err(|_| PwzError::GrammarTooLarge)?);
        let live = production_is_productive
            .iter()
            .enumerate()
            .any(|(index, productive)| {
                *productive && grammar.productions[index].lhs == grammar.start
            });
        let mut contexts = Vec::with_capacity(64);
        contexts.push(Context::Top);

        Ok(Self {
            expressions,
            edges,
            start,
            terminal_count: grammar.terminal_count,
            memos: Vec::with_capacity(64),
            contexts,
            parent_links: Vec::with_capacity(64),
            events: Vec::with_capacity(64),
            frontier: Vec::with_capacity(4),
            next_frontier: Vec::with_capacity(4),
            position: 0,
            live,
            arena_exhausted: false,
            stats: PwzStats::default(),
        })
    }

    /// Consumes one normalized terminal and returns membership in the prefix
    /// closure of the grammar language.
    pub(crate) fn push_raw(&mut self, terminal: usize) -> Result<bool, PwzError> {
        if self.arena_exhausted {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        if !self.live {
            return Ok(false);
        }
        if terminal >= self.terminal_count || self.position == NO_POSITION {
            self.kill();
            return Ok(false);
        }

        self.events.clear();
        self.next_frontier.clear();
        if self.position == 0 {
            self.events.push(Event::Down {
                expression: self.start,
                context: ContextId(0),
            });
        } else {
            for &memo in &self.frontier {
                self.events.push(Event::Up(memo));
            }
        }

        while let Some(event) = self.events.pop() {
            self.stats.events = self.stats.events.saturating_add(1);
            match event {
                Event::Down {
                    expression,
                    context,
                } => self.down(expression, context),
                Event::Eval { expression, memo } => self.eval(expression, memo, terminal),
                Event::Up(memo) => self.up(memo),
                Event::Apply(context) => self.apply(context),
            }
            if self.arena_exhausted {
                self.kill();
                return Err(PwzError::ArenaCapacityExceeded);
            }
        }

        self.position += 1;
        std::mem::swap(&mut self.frontier, &mut self.next_frontier);
        self.live = !self.frontier.is_empty();
        Ok(self.live)
    }

    #[inline]
    pub(crate) fn is_live(&self) -> bool {
        self.live
    }

    #[inline]
    pub(crate) fn stats(&self) -> PwzStats {
        PwzStats {
            derivatives: self.position,
            ..self.stats
        }
    }

    fn down(&mut self, expression: ExprId, context: ContextId) {
        let expression_index = expression.index();
        let is_new = self.expressions[expression_index].memo_position != self.position;
        let memo = if is_new {
            let Some(memo) = self.alloc_memo() else {
                return;
            };
            let node = &mut self.expressions[expression_index];
            node.memo_position = self.position;
            node.memo = memo;
            memo
        } else {
            self.expressions[expression_index].memo
        };

        if !self.add_parent(memo, context) {
            return;
        }
        if is_new {
            self.events.push(Event::Eval { expression, memo });
        } else if self.memos[memo.index()].completed_end == self.position {
            self.events.push(Event::Apply(context));
        }
    }

    fn eval(&mut self, expression: ExprId, memo: MemoId, terminal: usize) {
        enum Shape {
            Terminal(usize),
            Alternative(u32, u32),
            Sequence(u32, u32),
        }
        let shape = match &self.expressions[expression.index()].kind {
            ExprKind::Terminal(expected) => Shape::Terminal(*expected),
            ExprKind::Alternative {
                edge_start,
                edge_len,
            } => Shape::Alternative(*edge_start, *edge_len),
            ExprKind::Sequence {
                edge_start,
                edge_len,
                ..
            } => Shape::Sequence(*edge_start, *edge_len),
        };

        match shape {
            Shape::Terminal(expected) => {
                if expected == terminal {
                    self.next_frontier.push(memo);
                }
            }
            Shape::Alternative(edge_start, edge_len) => {
                let end = edge_start + edge_len;
                let mut selected = false;
                for edge in edge_start..end {
                    let child = self.edges[edge as usize];
                    let accepts = match &self.expressions[child.index()].kind {
                        ExprKind::Sequence { lookahead, .. } => lookahead.contains(terminal),
                        _ => false,
                    };
                    if accepts {
                        selected = true;
                        break;
                    }
                }
                if !selected {
                    return;
                }
                let Some(parent) = self.alloc_context(Context::Alternative(memo)) else {
                    return;
                };
                for edge in edge_start..end {
                    let child = self.edges[edge as usize];
                    let accepts = match &self.expressions[child.index()].kind {
                        ExprKind::Sequence { lookahead, .. } => lookahead.contains(terminal),
                        _ => false,
                    };
                    if accepts {
                        self.events.push(Event::Down {
                            expression: child,
                            context: parent,
                        });
                    }
                }
            }
            Shape::Sequence(edge_start, edge_len) => {
                if edge_len == 0 {
                    self.events.push(Event::Up(memo));
                    return;
                }
                let Some(context) = self.alloc_context(Context::Sequence {
                    memo,
                    sequence: expression,
                    next: 1,
                }) else {
                    return;
                };
                self.events.push(Event::Down {
                    expression: self.edges[edge_start as usize],
                    context,
                });
            }
        }
    }

    fn up(&mut self, memo: MemoId) {
        let memo_index = memo.index();
        if self.memos[memo_index].completed_end == self.position {
            return;
        }
        self.memos[memo_index].completed_end = self.position;

        // Capture the current immutable linked-list head. A recursive `Down`
        // may add a new parent to this memo; it schedules that new parent
        // directly, exactly matching the persistent-list snapshot in PwZ.
        let mut link = self.memos[memo_index].parent_head;
        while link != NO_INDEX {
            let parent_link = self.parent_links[link as usize];
            self.events.push(Event::Apply(parent_link.context));
            link = parent_link.next;
        }
    }

    fn apply(&mut self, context: ContextId) {
        match self.contexts[context.index()] {
            Context::Top => {}
            Context::Alternative(memo) => self.events.push(Event::Up(memo)),
            Context::Sequence {
                memo,
                sequence,
                next,
            } => {
                let (edge_start, edge_len) = match self.expressions[sequence.index()].kind {
                    ExprKind::Sequence {
                        edge_start,
                        edge_len,
                        ..
                    } => (edge_start, edge_len),
                    _ => return,
                };
                if next == edge_len {
                    self.events.push(Event::Up(memo));
                    return;
                }
                let Some(next_context) = self.alloc_context(Context::Sequence {
                    memo,
                    sequence,
                    next: next + 1,
                }) else {
                    return;
                };
                self.events.push(Event::Down {
                    expression: self.edges[(edge_start + next) as usize],
                    context: next_context,
                });
            }
        }
    }

    fn alloc_memo(&mut self) -> Option<MemoId> {
        let Ok(raw) = u32::try_from(self.memos.len()) else {
            self.arena_exhausted = true;
            return None;
        };
        if raw == NO_INDEX {
            self.arena_exhausted = true;
            return None;
        }
        self.memos.push(Memo {
            parent_head: NO_INDEX,
            completed_end: NO_POSITION,
        });
        self.stats.memo_records = self.stats.memo_records.saturating_add(1);
        Some(MemoId(raw))
    }

    fn alloc_context(&mut self, context: Context) -> Option<ContextId> {
        let Ok(raw) = u32::try_from(self.contexts.len()) else {
            self.arena_exhausted = true;
            return None;
        };
        if raw == NO_INDEX {
            self.arena_exhausted = true;
            return None;
        }
        self.contexts.push(context);
        Some(ContextId(raw))
    }

    fn add_parent(&mut self, memo: MemoId, context: ContextId) -> bool {
        let Ok(raw) = u32::try_from(self.parent_links.len()) else {
            self.arena_exhausted = true;
            return false;
        };
        if raw == NO_INDEX {
            self.arena_exhausted = true;
            return false;
        }
        let previous = self.memos[memo.index()].parent_head;
        self.parent_links.push(ParentLink {
            context,
            next: previous,
        });
        self.memos[memo.index()].parent_head = raw;
        true
    }

    fn kill(&mut self) {
        self.live = false;
        self.frontier.clear();
        self.next_frontier.clear();
        self.events.clear();
    }
}

fn validate(grammar: &CoreGrammar) -> Result<(), PwzError> {
    if grammar.start >= grammar.nonterminal_count {
        return Err(PwzError::InvalidStart {
            start: grammar.start,
            nonterminal_count: grammar.nonterminal_count,
        });
    }
    for (production_index, production) in grammar.productions.iter().enumerate() {
        if production.lhs >= grammar.nonterminal_count {
            return Err(PwzError::InvalidProductionLhs {
                production: production_index,
                lhs: production.lhs,
            });
        }
        for symbol in &production.rhs {
            match *symbol {
                CoreSymbol::Nonterminal(nonterminal)
                    if nonterminal >= grammar.nonterminal_count =>
                {
                    return Err(PwzError::InvalidNonterminal {
                        production: production_index,
                        nonterminal,
                    });
                }
                CoreSymbol::Terminal(terminal) if terminal >= grammar.terminal_count => {
                    return Err(PwzError::InvalidTerminal {
                        production: production_index,
                        terminal,
                    });
                }
                _ => {}
            }
        }
    }
    Ok(())
}

pub struct PwzRecognizer {
    core: PwzCore,
}

impl PwzRecognizer {
    pub fn compile(grammar: &Grammar) -> Result<Self, PwzError> {
        let core_grammar = CoreGrammar {
            start: grammar.start().index(),
            nonterminal_count: grammar.nonterminal_count(),
            terminal_count: grammar.terminal_count(),
            productions: grammar
                .productions()
                .iter()
                .map(|production| CoreProduction {
                    lhs: production.lhs.index(),
                    rhs: production
                        .rhs
                        .iter()
                        .map(|symbol| match *symbol {
                            Symbol::Nonterminal(nonterminal) => {
                                CoreSymbol::Nonterminal(nonterminal.index())
                            }
                            Symbol::Terminal(terminal) => CoreSymbol::Terminal(terminal.index()),
                        })
                        .collect(),
                })
                .collect(),
        };
        Self::compile_core(&core_grammar)
    }

    pub(crate) fn compile_core(grammar: &CoreGrammar) -> Result<Self, PwzError> {
        Ok(Self {
            core: PwzCore::compile(grammar)?,
        })
    }

    #[inline]
    pub fn push(&mut self, terminal: TerminalId) -> Result<bool, PwzError> {
        self.core.push_raw(terminal.index())
    }

    #[inline]
    pub(crate) fn push_index(&mut self, terminal: usize) -> Result<bool, PwzError> {
        self.core.push_raw(terminal)
    }

    #[inline]
    pub fn has_completion(&self) -> bool {
        self.core.is_live()
    }

    #[inline]
    pub fn stats(&self) -> PwzStats {
        self.core.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn grammar(
        nonterminal_count: usize,
        terminal_count: usize,
        start: usize,
        productions: &[(usize, &[CoreSymbol])],
    ) -> CoreGrammar {
        CoreGrammar {
            start,
            nonterminal_count,
            terminal_count,
            productions: productions
                .iter()
                .map(|(lhs, rhs)| CoreProduction {
                    lhs: *lhs,
                    rhs: rhs.to_vec(),
                })
                .collect(),
        }
    }

    fn accepts_prefix(parser: &mut PwzRecognizer, input: &[usize]) -> bool {
        input
            .iter()
            .copied()
            .all(|terminal| parser.push_index(terminal).unwrap())
    }

    #[test]
    fn right_recursive_nullable_ll1_path_is_linear() {
        // S -> I; I -> x I | epsilon.
        let grammar = grammar(
            2,
            1,
            0,
            &[
                (0, &[CoreSymbol::Nonterminal(1)]),
                (1, &[CoreSymbol::Terminal(0), CoreSymbol::Nonterminal(1)]),
                (1, &[]),
            ],
        );
        let mut parser = PwzRecognizer::compile_core(&grammar).unwrap();
        for _ in 0..50_000 {
            assert!(parser.push_index(0).unwrap());
        }
        assert!(parser.stats().events <= 50_000 * 20 + 64);
        assert!(parser.stats().memo_records <= 50_000 * 8 + 64);
    }

    #[test]
    fn productive_pruning_rejects_a_locally_matching_dead_branch() {
        // S -> a U | b; U -> U.  The `a` branch matches a token but has no
        // complete word and therefore is not a member of the prefix closure.
        let grammar = grammar(
            2,
            2,
            0,
            &[
                (0, &[CoreSymbol::Terminal(0), CoreSymbol::Nonterminal(1)]),
                (0, &[CoreSymbol::Terminal(1)]),
                (1, &[CoreSymbol::Nonterminal(1)]),
            ],
        );
        let mut dead = PwzRecognizer::compile_core(&grammar).unwrap();
        assert!(dead.has_completion());
        assert!(!dead.push_index(0).unwrap());
        assert!(
            !dead.push_index(1).unwrap(),
            "a dead prefix must remain dead"
        );

        let mut live = PwzRecognizer::compile_core(&grammar).unwrap();
        assert!(live.push_index(1).unwrap());
    }

    #[test]
    fn nullable_left_recursion_terminates_and_streams() {
        // S -> S a | epsilon.
        let grammar = grammar(
            1,
            1,
            0,
            &[
                (0, &[CoreSymbol::Nonterminal(0), CoreSymbol::Terminal(0)]),
                (0, &[]),
            ],
        );
        let mut parser = PwzRecognizer::compile_core(&grammar).unwrap();
        assert!(parser.has_completion());
        assert!(accepts_prefix(&mut parser, &[0, 0, 0, 0, 0]));
    }

    #[test]
    fn epsilon_and_unit_cycles_terminate() {
        // S -> A; A -> S | epsilon | a.
        let grammar = grammar(
            2,
            1,
            0,
            &[
                (0, &[CoreSymbol::Nonterminal(1)]),
                (1, &[CoreSymbol::Nonterminal(0)]),
                (1, &[]),
                (1, &[CoreSymbol::Terminal(0)]),
            ],
        );
        let mut parser = PwzRecognizer::compile_core(&grammar).unwrap();
        assert!(parser.has_completion());
        assert!(parser.push_index(0).unwrap());
        assert!(!parser.push_index(0).unwrap());
    }

    #[test]
    fn a_non_ll_language_keeps_all_viable_zippers() {
        // Palindromes: S -> a S a | b S b | epsilon. Every a/b prefix has a
        // completion (append its reverse), exercising simultaneous zippers.
        let grammar = grammar(
            1,
            2,
            0,
            &[
                (
                    0,
                    &[
                        CoreSymbol::Terminal(0),
                        CoreSymbol::Nonterminal(0),
                        CoreSymbol::Terminal(0),
                    ],
                ),
                (
                    0,
                    &[
                        CoreSymbol::Terminal(1),
                        CoreSymbol::Nonterminal(0),
                        CoreSymbol::Terminal(1),
                    ],
                ),
                (0, &[]),
            ],
        );
        let mut parser = PwzRecognizer::compile_core(&grammar).unwrap();
        assert!(accepts_prefix(&mut parser, &[0, 1, 1, 0, 1, 0, 0, 1]));
    }

    #[test]
    fn invalid_core_indices_are_reported_at_compile_time() {
        let invalid_start = grammar(1, 1, 1, &[]);
        assert!(matches!(
            PwzRecognizer::compile_core(&invalid_start),
            Err(PwzError::InvalidStart { .. })
        ));

        let invalid_terminal = grammar(1, 1, 0, &[(0, &[CoreSymbol::Terminal(1)])]);
        assert!(matches!(
            PwzRecognizer::compile_core(&invalid_terminal),
            Err(PwzError::InvalidTerminal { .. })
        ));
    }

    #[test]
    fn arena_exhaustion_is_an_error_not_language_rejection() {
        let grammar = grammar(1, 1, 0, &[(0, &[CoreSymbol::Terminal(0)])]);
        let mut parser = PwzRecognizer::compile_core(&grammar).unwrap();
        parser.core.arena_exhausted = true;
        assert_eq!(parser.push_index(0), Err(PwzError::ArenaCapacityExceeded));
    }
}
