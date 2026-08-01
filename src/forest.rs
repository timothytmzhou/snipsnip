use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;

use crate::{
    grammar::{Action, Grammar, Symbol, TerminalId},
    grammar_flow::{GrammarFlowAnalysis, TerminalSet},
    pwz::{PwzError, PwzStats},
};

const NO_INDEX: u32 = u32::MAX;
const NO_POSITION: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct SpaceId(u32);

impl SpaceId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    #[cfg(test)]
    pub(crate) const fn from_u32_for_test(value: u32) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum SpaceFact {
    Alias {
        output: SpaceId,
        child: SpaceId,
    },
    Constructor {
        constructor: u32,
        output: SpaceId,
        children: SmallVec<[SpaceId; 4]>,
    },
    TokenAny {
        output: SpaceId,
        terminal: TerminalId,
    },
    TokenExact {
        output: SpaceId,
        terminal: TerminalId,
    },
}

pub(crate) struct SpaceArena {
    next_state: u32,
    pending_facts: Vec<SpaceFact>,
    fact_count: usize,
    seen_aliases: HashSet<(SpaceId, SpaceId)>,
    applications: HashMap<(u32, SmallVec<[SpaceId; 4]>), SpaceId>,
    exact_tokens: Vec<Option<HashMap<String, SpaceId>>>,
    full_nonterminals: Vec<SpaceId>,
    full_terminals: Vec<SpaceId>,
}

impl SpaceArena {
    fn compile(
        grammar: &Grammar,
        productive: &[bool],
        production_constructors: &[Option<u32>],
        selected_terminals: &[bool],
    ) -> Result<Self, PwzError> {
        debug_assert_eq!(selected_terminals.len(), grammar.terminal_count());
        let state_count = grammar
            .nonterminal_count()
            .checked_add(grammar.terminal_count())
            .ok_or(PwzError::GrammarTooLarge)?;
        let next_state = u32::try_from(state_count).map_err(|_| PwzError::GrammarTooLarge)?;
        if next_state == NO_INDEX {
            return Err(PwzError::GrammarTooLarge);
        }
        let full_nonterminals = (0..grammar.nonterminal_count())
            .map(|index| SpaceId(index as u32))
            .collect::<Vec<_>>();
        let full_terminals = (0..grammar.terminal_count())
            .map(|index| SpaceId((grammar.nonterminal_count() + index) as u32))
            .collect::<Vec<_>>();
        let mut arena = Self {
            next_state,
            pending_facts: Vec::new(),
            fact_count: 0,
            seen_aliases: HashSet::default(),
            applications: HashMap::default(),
            exact_tokens: selected_terminals
                .iter()
                .map(|selected| selected.then(HashMap::default))
                .collect(),
            full_nonterminals,
            full_terminals,
        };
        for terminal in 0..grammar.terminal_count() {
            arena.add_fact(SpaceFact::TokenAny {
                output: arena.full_terminals[terminal],
                terminal: TerminalId(terminal),
            });
        }
        let mut seen_static_constructors = HashSet::default();
        for (production_index, production) in grammar.productions().iter().enumerate() {
            if !productive[production_index] {
                continue;
            }
            let output = arena.full_nonterminals[production.lhs.index()];
            match &production.action {
                Action::Construct {
                    constructor: _,
                    arguments,
                } => {
                    let children = arguments
                        .iter()
                        .map(|position| arena.full_symbol(production.rhs[*position - 1]))
                        .collect();
                    let fact = SpaceFact::Constructor {
                        constructor: production_constructors[production_index]
                            .expect("construct action has an interned constructor"),
                        output,
                        children,
                    };
                    if seen_static_constructors.insert(fact.clone()) {
                        arena.add_fact(fact);
                    }
                }
                Action::Project { position } => {
                    arena.alias(output, arena.full_symbol(production.rhs[*position - 1]));
                }
            }
        }
        Ok(arena)
    }

    fn full_symbol(&self, symbol: Symbol) -> SpaceId {
        match symbol {
            Symbol::Nonterminal(nonterminal) => self.full_nonterminals[nonterminal.index()],
            Symbol::Terminal(terminal) => self.full_terminals[terminal.index()],
        }
    }

    pub(crate) fn full_start(&self, grammar: &Grammar) -> SpaceId {
        self.full_nonterminals[grammar.start().index()]
    }

    fn allocate(&mut self) -> Result<SpaceId, PwzError> {
        if self.next_state == NO_INDEX {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        let id = SpaceId(self.next_state);
        self.next_state = self
            .next_state
            .checked_add(1)
            .ok_or(PwzError::ArenaCapacityExceeded)?;
        Ok(id)
    }

    fn add_fact(&mut self, fact: SpaceFact) {
        self.fact_count = self.fact_count.saturating_add(1);
        self.pending_facts.push(fact);
    }

    fn alias(&mut self, output: SpaceId, child: SpaceId) {
        if self.seen_aliases.insert((output, child)) {
            self.add_fact(SpaceFact::Alias { output, child });
        }
    }

    /// Records the first edge out of a freshly allocated union space.
    ///
    /// The output cannot already have an alias, so retaining this pair in the
    /// general duplicate-suppression table only adds one hash-table entry per
    /// deterministic completion. If a later completion makes the space truly
    /// ambiguous, subsequent edges use [`Self::alias`] as usual.
    fn alias_fresh_output(&mut self, output: SpaceId, child: SpaceId) {
        debug_assert_eq!(output.0.checked_add(1), Some(self.next_state));
        self.add_fact(SpaceFact::Alias { output, child });
    }

    fn exact_token(&mut self, terminal: TerminalId, lexeme: &str) -> Result<SpaceId, PwzError> {
        let terminal_index = terminal.index();
        let Some(exact_tokens) = &self.exact_tokens[terminal_index] else {
            return Ok(self.full_terminals[terminal.index()]);
        };
        if let Some(state) = exact_tokens.get(lexeme) {
            return Ok(*state);
        }
        let state = self.allocate()?;
        self.add_fact(SpaceFact::TokenExact {
            output: state,
            terminal,
        });
        self.exact_tokens[terminal_index]
            .as_mut()
            .expect("selected terminal has an exact-token table")
            .insert(lexeme.to_owned(), state);
        Ok(state)
    }

    fn apply(
        &mut self,
        action: &Action,
        constructor_id: Option<u32>,
        selected: &[SpaceId],
    ) -> Result<SpaceId, PwzError> {
        let Action::Construct {
            constructor: _,
            arguments,
        } = action
        else {
            let Action::Project { position: _ } = action else {
                unreachable!()
            };
            debug_assert_eq!(selected.len(), 1);
            return Ok(selected[0]);
        };
        debug_assert_eq!(selected.len(), arguments.len());
        let constructor_id = constructor_id.expect("construct action has an interned constructor");
        let children = selected.iter().copied().collect::<SmallVec<_>>();
        let key = (constructor_id, children.clone());
        if let Some(state) = self.applications.get(&key) {
            return Ok(*state);
        }
        let state = self.allocate()?;
        self.add_fact(SpaceFact::Constructor {
            constructor: constructor_id,
            output: state,
            children,
        });
        self.applications.insert(key, state);
        Ok(state)
    }

    pub(crate) fn swap_facts(&mut self, output: &mut Vec<SpaceFact>) {
        debug_assert!(output.is_empty());
        std::mem::swap(&mut self.pending_facts, output);
    }

    pub(crate) fn fact_count(&self) -> usize {
        self.fact_count
    }

    pub(crate) fn state_count(&self) -> usize {
        self.next_state as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExprId(u32);

impl ExprId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct MemoId(u32);

impl MemoId {
    fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) const fn from_u32_for_test(value: u32) -> Self {
        Self(value)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ContextId(u32);

impl ContextId {
    fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) const fn from_u32_for_test(value: u32) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ZipperFact {
    Parent {
        memo: MemoId,
        context: ContextId,
    },
    Alternative {
        context: ContextId,
        memo: MemoId,
    },
    ConstructHole {
        constructor: u32,
        context: ContextId,
        memo: MemoId,
        hole_argument: usize,
        fixed_children: SmallVec<[SpaceId; 4]>,
    },
    ConstructIgnored {
        constructor: u32,
        context: ContextId,
        memo: MemoId,
        children: SmallVec<[SpaceId; 4]>,
    },
    ProjectHole {
        context: ContextId,
        memo: MemoId,
    },
    ProjectFixed {
        context: ContextId,
        memo: MemoId,
        child: SpaceId,
    },
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
    Terminal(TerminalId),
    Alternative {
        edge_start: u32,
        edge_len: u32,
    },
    Sequence {
        edge_start: u32,
        edge_len: u32,
        production: usize,
        lookahead: Lookahead,
    },
}

#[derive(Clone, Debug)]
struct Expr {
    kind: ExprKind,
    memo_position: u32,
    memo: MemoId,
}

#[derive(Clone, Copy, Debug)]
enum Context {
    Top,
    Alternative(MemoId),
    Sequence {
        memo: MemoId,
        sequence: ExprId,
        next: u32,
        values: u32,
    },
}

#[derive(Clone, Copy, Debug)]
struct ParentLink {
    context: ContextId,
    next: u32,
}

#[derive(Clone, Copy, Debug)]
struct ValueLink {
    space: SpaceId,
    next: u32,
}

#[derive(Clone, Copy, Debug)]
struct Memo {
    parent_head: u32,
    completed_end: u32,
    completed_space: u32,
}

impl Memo {
    fn completed_space(self) -> SpaceId {
        debug_assert_ne!(self.completed_space, NO_INDEX);
        SpaceId(self.completed_space)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Frontier {
    pub(crate) memo: MemoId,
    pub(crate) space: SpaceId,
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
    Complete {
        memo: MemoId,
        space: SpaceId,
    },
    Apply {
        context: ContextId,
        space: SpaceId,
    },
}

/// Value-producing PwZ. Its immutable space and zipper facts form a compact,
/// persistent representation of every continuation reached so far. A current
/// frontier refers into that history instead of eagerly plugging its whole
/// context chain, which would copy a linear AST spine at every prefix.
pub(crate) struct ForestPwz {
    grammar: Grammar,
    production_constructors: Vec<Option<u32>>,
    expressions: Vec<Expr>,
    edges: Vec<ExprId>,
    expression_full_spaces: Vec<Option<SpaceId>>,
    start: ExprId,
    spaces: SpaceArena,

    memos: Vec<Memo>,
    contexts: Vec<Context>,
    parent_links: Vec<ParentLink>,
    value_links: Vec<ValueLink>,
    pending_zipper_facts: Vec<ZipperFact>,
    zipper_fact_count: usize,
    events: Vec<Event>,
    frontier: Vec<Frontier>,
    next_frontier: Vec<Frontier>,

    position: u32,
    direct_completions: bool,
    live: bool,
    stats: PwzStats,
}

impl ForestPwz {
    pub(crate) fn compile(
        grammar: &Grammar,
        constructor_id: impl Fn(&str) -> u32,
        selected_terminals: &[bool],
    ) -> Result<Self, PwzError> {
        debug_assert_eq!(selected_terminals.len(), grammar.terminal_count());
        let flow = GrammarFlowAnalysis::compute(grammar);
        let productive = flow.productive_productions();
        let direct_completions = flow.is_ll1();
        let production_constructors = grammar
            .productions()
            .iter()
            .map(|production| match &production.action {
                Action::Construct { constructor, .. } => Some(constructor_id(constructor)),
                Action::Project { .. } => None,
            })
            .collect::<Vec<_>>();
        let spaces = SpaceArena::compile(
            grammar,
            productive,
            &production_constructors,
            selected_terminals,
        )?;

        let productive_count = productive.iter().filter(|value| **value).count();
        let expression_count = grammar
            .nonterminal_count()
            .checked_add(grammar.terminal_count())
            .and_then(|count| count.checked_add(productive_count))
            .ok_or(PwzError::GrammarTooLarge)?;
        if expression_count >= NO_INDEX as usize {
            return Err(PwzError::GrammarTooLarge);
        }
        let mut expressions = Vec::with_capacity(expression_count);
        let mut expression_full_spaces = Vec::with_capacity(expression_count);
        for nonterminal in 0..grammar.nonterminal_count() {
            expressions.push(Expr {
                kind: ExprKind::Alternative {
                    edge_start: 0,
                    edge_len: 0,
                },
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
            expression_full_spaces.push(Some(spaces.full_nonterminals[nonterminal]));
        }
        for terminal in 0..grammar.terminal_count() {
            expressions.push(Expr {
                kind: ExprKind::Terminal(TerminalId(terminal)),
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
            expression_full_spaces.push(Some(spaces.full_terminals[terminal]));
        }

        let mut edges = Vec::new();
        let mut alternatives = vec![Vec::<ExprId>::new(); grammar.nonterminal_count()];
        for (production_index, production) in grammar.productions().iter().enumerate() {
            if !productive[production_index] {
                continue;
            }
            let edge_start = u32::try_from(edges.len()).map_err(|_| PwzError::GrammarTooLarge)?;
            for symbol in &production.rhs {
                let raw = match symbol {
                    Symbol::Nonterminal(id) => id.index(),
                    Symbol::Terminal(id) => grammar.nonterminal_count() + id.index(),
                };
                edges.push(ExprId(
                    u32::try_from(raw).map_err(|_| PwzError::GrammarTooLarge)?,
                ));
            }
            let expression =
                ExprId(u32::try_from(expressions.len()).map_err(|_| PwzError::GrammarTooLarge)?);
            expressions.push(Expr {
                kind: ExprKind::Sequence {
                    edge_start,
                    edge_len: u32::try_from(production.rhs.len())
                        .map_err(|_| PwzError::GrammarTooLarge)?,
                    production: production_index,
                    lookahead: Lookahead::from_set(flow.select(production_index))?,
                },
                memo_position: NO_POSITION,
                memo: MemoId(NO_INDEX),
            });
            expression_full_spaces.push(None);
            alternatives[production.lhs.index()].push(expression);
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
        let start =
            ExprId(u32::try_from(grammar.start().index()).map_err(|_| PwzError::GrammarTooLarge)?);
        let live = productive
            .iter()
            .enumerate()
            .any(|(index, value)| *value && grammar.productions()[index].lhs == grammar.start());
        Ok(Self {
            grammar: grammar.clone(),
            production_constructors,
            expressions,
            edges,
            expression_full_spaces,
            start,
            spaces,
            memos: Vec::new(),
            contexts: vec![Context::Top],
            parent_links: Vec::new(),
            value_links: Vec::new(),
            pending_zipper_facts: Vec::new(),
            zipper_fact_count: 0,
            events: Vec::new(),
            frontier: Vec::new(),
            next_frontier: Vec::new(),
            position: 0,
            direct_completions,
            live,
            stats: PwzStats::default(),
        })
    }

    pub(crate) fn push(&mut self, terminal: TerminalId, lexeme: &str) -> Result<bool, PwzError> {
        if !self.live {
            return Ok(false);
        }
        if terminal.index() >= self.grammar.terminal_count() || self.position == NO_POSITION {
            self.live = false;
            self.frontier.clear();
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
            for item in self.frontier.iter().copied() {
                self.events.push(Event::Complete {
                    memo: item.memo,
                    space: item.space,
                });
            }
        }
        while let Some(event) = self.events.pop() {
            self.stats.events = self.stats.events.saturating_add(1);
            match event {
                Event::Down {
                    expression,
                    context,
                } => self.down(expression, context)?,
                Event::Eval { expression, memo } => {
                    self.eval(expression, memo, terminal, lexeme)?
                }
                Event::Complete { memo, space } => self.complete(memo, space)?,
                Event::Apply { context, space } => self.apply(context, space)?,
            }
        }
        self.position = self
            .position
            .checked_add(1)
            .filter(|position| *position != NO_POSITION)
            .ok_or(PwzError::ArenaCapacityExceeded)?;
        std::mem::swap(&mut self.frontier, &mut self.next_frontier);
        self.live = !self.frontier.is_empty();
        Ok(self.live)
    }

    pub(crate) fn initial_root(&self) -> Option<SpaceId> {
        self.live.then(|| self.spaces.full_start(&self.grammar))
    }

    pub(crate) fn current_frontier(&self) -> &[Frontier] {
        &self.frontier
    }

    pub(crate) fn is_live(&self) -> bool {
        self.live
    }

    pub(crate) fn swap_space_facts(&mut self, output: &mut Vec<SpaceFact>) {
        self.spaces.swap_facts(output);
    }

    pub(crate) fn swap_zipper_facts(&mut self, output: &mut Vec<ZipperFact>) {
        debug_assert!(output.is_empty());
        std::mem::swap(&mut self.pending_zipper_facts, output);
    }

    pub(crate) fn representation_state_count(&self) -> usize {
        self.spaces.state_count() + self.memos.len() + self.contexts.len()
    }

    pub(crate) fn representation_fact_count(&self) -> usize {
        self.spaces.fact_count() + self.zipper_fact_count
    }

    pub(crate) fn stats(&self) -> PwzStats {
        PwzStats {
            derivatives: self.position as usize,
            ..self.stats
        }
    }

    fn down(&mut self, expression: ExprId, context: ContextId) -> Result<(), PwzError> {
        let index = expression.index();
        let is_new = self.expressions[index].memo_position != self.position;
        let memo = if is_new {
            let memo = self.allocate_memo()?;
            self.expressions[index].memo_position = self.position;
            self.expressions[index].memo = memo;
            memo
        } else {
            self.expressions[index].memo
        };
        self.add_parent(memo, context)?;
        if is_new {
            self.events.push(Event::Eval { expression, memo });
        } else if self.memos[memo.index()].completed_end == self.position {
            let space = self.memos[memo.index()].completed_space();
            self.events.push(Event::Apply { context, space });
        }
        Ok(())
    }

    fn eval(
        &mut self,
        expression: ExprId,
        memo: MemoId,
        terminal: TerminalId,
        lexeme: &str,
    ) -> Result<(), PwzError> {
        enum Shape {
            Terminal(TerminalId),
            Alternative(u32, u32),
            Sequence(u32, u32, usize),
        }
        let shape = match &self.expressions[expression.index()].kind {
            ExprKind::Terminal(value) => Shape::Terminal(*value),
            ExprKind::Alternative {
                edge_start,
                edge_len,
            } => Shape::Alternative(*edge_start, *edge_len),
            ExprKind::Sequence {
                edge_start,
                edge_len,
                production,
                ..
            } => Shape::Sequence(*edge_start, *edge_len, *production),
        };
        match shape {
            Shape::Terminal(expected) => {
                if expected == terminal {
                    let space = self.spaces.exact_token(terminal, lexeme)?;
                    self.next_frontier.push(Frontier { memo, space });
                }
            }
            Shape::Alternative(edge_start, edge_len) => {
                let edge_end = edge_start + edge_len;
                let Some(first_edge) = (edge_start..edge_end)
                    .find(|edge| self.sequence_accepts(self.edges[*edge as usize], terminal))
                else {
                    return Ok(());
                };
                let parent = self.allocate_context(Context::Alternative(memo))?;
                for edge in first_edge..edge_end {
                    let child = self.edges[edge as usize];
                    if self.sequence_accepts(child, terminal) {
                        self.events.push(Event::Down {
                            expression: child,
                            context: parent,
                        });
                    }
                }
            }
            Shape::Sequence(edge_start, edge_len, production) => {
                if edge_len == 0 {
                    let space = self.spaces.apply(
                        &self.grammar.productions()[production].action,
                        self.production_constructors[production],
                        &[],
                    )?;
                    self.events.push(Event::Complete { memo, space });
                } else {
                    let context = self.allocate_context(Context::Sequence {
                        memo,
                        sequence: expression,
                        next: 1,
                        values: NO_INDEX,
                    })?;
                    self.events.push(Event::Down {
                        expression: self.edges[edge_start as usize],
                        context,
                    });
                }
            }
        }
        Ok(())
    }

    fn sequence_accepts(&self, expression: ExprId, terminal: TerminalId) -> bool {
        matches!(
            &self.expressions[expression.index()].kind,
            ExprKind::Sequence { lookahead, .. } if lookahead.contains(terminal.index())
        )
    }

    fn complete(&mut self, memo: MemoId, incoming: SpaceId) -> Result<(), PwzError> {
        let index = memo.index();
        if self.memos[index].completed_end == self.position {
            let completed = self.memos[index].completed_space();
            if self.direct_completions {
                // Pairwise-disjoint SELECT sets prove that this memo has at
                // most one parse at one input position. Duplicate work can
                // still report that parse more than once, but hash-consing
                // must give it the same semantic space.
                assert_eq!(
                    completed, incoming,
                    "LL(1) memo completed with two distinct semantic spaces"
                );
            } else {
                self.spaces.alias(completed, incoming);
            }
            return Ok(());
        }
        let space = if self.direct_completions {
            incoming
        } else {
            let output = self.spaces.allocate()?;
            self.spaces.alias_fresh_output(output, incoming);
            output
        };
        self.memos[index].completed_end = self.position;
        self.memos[index].completed_space = space.0;
        let mut link = self.memos[index].parent_head;
        while link != NO_INDEX {
            let parent = self.parent_links[link as usize];
            self.events.push(Event::Apply {
                context: parent.context,
                space,
            });
            link = parent.next;
        }
        Ok(())
    }

    fn apply(&mut self, context: ContextId, child: SpaceId) -> Result<(), PwzError> {
        match self.contexts[context.index()] {
            Context::Top => {}
            Context::Alternative(memo) => {
                self.events.push(Event::Complete { memo, space: child });
            }
            Context::Sequence {
                memo,
                sequence,
                next,
                values,
            } => {
                let values = self.allocate_value(child, values)?;
                let (edge_start, edge_len, production) = self.sequence_shape(sequence);
                if next == edge_len {
                    let action = &self.grammar.productions()[production].action;
                    let values = self.collect_action_values(action, values, edge_len as usize);
                    let space = self.spaces.apply(
                        action,
                        self.production_constructors[production],
                        &values,
                    )?;
                    self.events.push(Event::Complete { memo, space });
                } else {
                    let next_context = self.allocate_context(Context::Sequence {
                        memo,
                        sequence,
                        next: next + 1,
                        values,
                    })?;
                    self.events.push(Event::Down {
                        expression: self.edges[(edge_start + next) as usize],
                        context: next_context,
                    });
                }
            }
        }
        Ok(())
    }

    fn sequence_shape(&self, sequence: ExprId) -> (u32, u32, usize) {
        match self.expressions[sequence.index()].kind {
            ExprKind::Sequence {
                edge_start,
                edge_len,
                production,
                ..
            } => (edge_start, edge_len, production),
            _ => unreachable!(),
        }
    }

    fn allocate_memo(&mut self) -> Result<MemoId, PwzError> {
        let raw = u32::try_from(self.memos.len()).map_err(|_| PwzError::ArenaCapacityExceeded)?;
        if raw == NO_INDEX {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        self.memos.push(Memo {
            parent_head: NO_INDEX,
            completed_end: NO_POSITION,
            completed_space: NO_INDEX,
        });
        self.stats.memo_records = self.stats.memo_records.saturating_add(1);
        Ok(MemoId(raw))
    }

    fn allocate_context(&mut self, context: Context) -> Result<ContextId, PwzError> {
        let raw =
            u32::try_from(self.contexts.len()).map_err(|_| PwzError::ArenaCapacityExceeded)?;
        if raw == NO_INDEX {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        let id = ContextId(raw);
        self.contexts.push(context);
        self.record_context(id, context);
        Ok(id)
    }

    fn add_parent(&mut self, memo: MemoId, context: ContextId) -> Result<(), PwzError> {
        #[cfg(debug_assertions)]
        {
            let mut existing = self.memos[memo.index()].parent_head;
            while existing != NO_INDEX {
                let parent = self.parent_links[existing as usize];
                debug_assert_ne!(parent.context, context, "duplicate PwZ parent edge");
                existing = parent.next;
            }
        }
        let raw =
            u32::try_from(self.parent_links.len()).map_err(|_| PwzError::ArenaCapacityExceeded)?;
        if raw == NO_INDEX {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        let previous = self.memos[memo.index()].parent_head;
        self.parent_links.push(ParentLink {
            context,
            next: previous,
        });
        self.memos[memo.index()].parent_head = raw;
        self.add_zipper_fact(ZipperFact::Parent { memo, context });
        Ok(())
    }

    fn record_context(&mut self, context_id: ContextId, context: Context) {
        match context {
            Context::Top => {}
            Context::Alternative(memo) => {
                self.add_zipper_fact(ZipperFact::Alternative {
                    context: context_id,
                    memo,
                });
            }
            Context::Sequence {
                memo,
                sequence,
                next,
                values,
            } => {
                let (edge_start, _, production) = self.sequence_shape(sequence);
                let fact = match &self.grammar.productions()[production].action {
                    Action::Construct {
                        constructor: _,
                        arguments,
                    } => {
                        if let Some(hole_argument) = arguments
                            .iter()
                            .position(|position| *position == next as usize)
                        {
                            let fixed_children = arguments
                                .iter()
                                .enumerate()
                                .filter(|(index, _)| *index != hole_argument)
                                .map(|(_, position)| {
                                    self.fixed_context_space(edge_start, next, values, *position)
                                })
                                .collect();
                            ZipperFact::ConstructHole {
                                constructor: self.production_constructors[production]
                                    .expect("construct action has an interned constructor"),
                                context: context_id,
                                memo,
                                hole_argument,
                                fixed_children,
                            }
                        } else {
                            let children = arguments
                                .iter()
                                .map(|position| {
                                    self.fixed_context_space(edge_start, next, values, *position)
                                })
                                .collect();
                            ZipperFact::ConstructIgnored {
                                constructor: self.production_constructors[production]
                                    .expect("construct action has an interned constructor"),
                                context: context_id,
                                memo,
                                children,
                            }
                        }
                    }
                    Action::Project { position } if *position == next as usize => {
                        ZipperFact::ProjectHole {
                            context: context_id,
                            memo,
                        }
                    }
                    Action::Project { position } => ZipperFact::ProjectFixed {
                        context: context_id,
                        memo,
                        child: self.fixed_context_space(edge_start, next, values, *position),
                    },
                };
                self.add_zipper_fact(fact);
            }
        }
    }

    fn add_zipper_fact(&mut self, fact: ZipperFact) {
        self.zipper_fact_count = self.zipper_fact_count.saturating_add(1);
        self.pending_zipper_facts.push(fact);
    }

    fn allocate_value(&mut self, space: SpaceId, next: u32) -> Result<u32, PwzError> {
        let raw =
            u32::try_from(self.value_links.len()).map_err(|_| PwzError::ArenaCapacityExceeded)?;
        if raw == NO_INDEX {
            return Err(PwzError::ArenaCapacityExceeded);
        }
        self.value_links.push(ValueLink { space, next });
        Ok(raw)
    }

    fn collect_action_values(
        &self,
        action: &Action,
        head: u32,
        rhs_len: usize,
    ) -> SmallVec<[SpaceId; 4]> {
        action
            .arguments()
            .iter()
            .map(|position| {
                let mut value = head;
                for _ in 0..rhs_len - *position {
                    value = self.value_links[value as usize].next;
                }
                self.value_links[value as usize].space
            })
            .collect()
    }

    fn fixed_context_space(
        &self,
        edge_start: u32,
        next: u32,
        mut values: u32,
        position: usize,
    ) -> SpaceId {
        debug_assert_ne!(position, next as usize);
        if position >= next as usize {
            let expression = self.edges[edge_start as usize + position - 1];
            return self.expression_full_spaces[expression.index()]
                .expect("RHS edges are terminals or nonterminals");
        }
        let steps = next as usize - 1 - position;
        for _ in 0..steps {
            values = self.value_links[values as usize].next;
        }
        self.value_links[values as usize].space
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{ForestPwz, Memo, SpaceFact};
    use crate::grammar::Grammar;

    fn is_ll1(grammar: &Grammar) -> bool {
        crate::grammar_flow::GrammarFlowAnalysis::compute(grammar).is_ll1()
    }

    #[test]
    fn memo_is_three_packed_u32_fields() {
        assert_eq!(size_of::<Memo>(), 12);
    }

    #[test]
    fn select_test_accepts_predictive_nullable_choice() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token X
            %%
            start: items { Root(1) };
            items: X items { Cons(2) }
                 | { Nil() }
                 ;
            "#,
        )
        .unwrap();
        assert!(is_ll1(&grammar));
    }

    #[test]
    fn select_test_rejects_nullable_follow_conflict() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token X
            %%
            start: choice X { Root(1) };
            choice: X { One() }
                  | { Empty() }
                  ;
            "#,
        )
        .unwrap();
        assert!(!is_ll1(&grammar));
    }

    #[test]
    fn select_test_rejects_two_nullable_productions_without_follow_tokens() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %%
            start: { Left() }
                 | { Right() }
                 ;
            "#,
        )
        .unwrap();
        assert!(!is_ll1(&grammar));
    }

    #[test]
    fn direct_completion_reuses_the_incoming_space_without_aliases() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token X
            %%
            start: X { Leaf() };
            "#,
        )
        .unwrap();
        let mut forest =
            ForestPwz::compile(&grammar, |_| 0, &vec![true; grammar.terminal_count()]).unwrap();
        assert!(forest.direct_completions);
        let mut initial = Vec::new();
        forest.swap_space_facts(&mut initial);

        let memo = forest.allocate_memo().unwrap();
        let incoming = forest.spaces.full_start(&grammar);
        forest.complete(memo, incoming).unwrap();
        forest.complete(memo, incoming).unwrap();

        let mut delta = Vec::new();
        forest.swap_space_facts(&mut delta);
        assert!(
            !delta
                .iter()
                .any(|fact| matches!(fact, SpaceFact::Alias { .. }))
        );
        assert_eq!(forest.memos[memo.index()].completed_space(), incoming);
    }

    #[test]
    fn first_ambiguous_completion_does_not_enter_the_alias_dedup_table() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token X
            %%
            start: X { Left() }
                 | X { Right() }
                 ;
            "#,
        )
        .unwrap();
        let mut forest =
            ForestPwz::compile(&grammar, |_| 0, &vec![true; grammar.terminal_count()]).unwrap();
        assert!(!forest.direct_completions);
        let mut initial = Vec::new();
        forest.swap_space_facts(&mut initial);

        let memo = forest.allocate_memo().unwrap();
        let incoming = forest.spaces.full_start(&grammar);
        forest.complete(memo, incoming).unwrap();

        let mut delta = Vec::new();
        forest.swap_space_facts(&mut delta);
        assert_eq!(
            delta
                .iter()
                .filter(|fact| matches!(fact, SpaceFact::Alias { .. }))
                .count(),
            1
        );
        assert!(forest.spaces.seen_aliases.is_empty());
    }

    #[test]
    fn left_factored_nullable_ll1_streams_without_dynamic_aliases() {
        let grammar = Grammar::from_yacc(
            r#"
            %start root
            %token X Y Z
            %%
            root: item Z { Root(1) };
            item: X tail { Item(1,2) };
            tail: Y { Present(1) }
                | { Empty() }
                ;
            "#,
        )
        .unwrap();
        assert!(is_ll1(&grammar));

        // The first stream takes the non-nullable Tail branch; the second
        // takes epsilon when Z is the lookahead in FOLLOW(Tail).
        let streams: &[&[(&str, &str)]] = &[
            &[("X", "x"), ("Y", "y"), ("Z", "z")],
            &[("X", "x"), ("Z", "z")],
        ];
        for stream in streams {
            let mut forest = ForestPwz::compile(
                &grammar,
                |constructor| match constructor {
                    "Root" => 0,
                    "Item" => 1,
                    "Present" => 2,
                    "Empty" => 3,
                    _ => unreachable!(),
                },
                &vec![true; grammar.terminal_count()],
            )
            .unwrap();
            assert!(forest.direct_completions);

            let mut facts = Vec::new();
            forest.swap_space_facts(&mut facts);
            facts.clear();
            for (terminal, lexeme) in *stream {
                assert!(
                    forest
                        .push(grammar.terminal_by_name(terminal).unwrap(), lexeme)
                        .unwrap()
                );
                forest.swap_space_facts(&mut facts);
                assert!(
                    facts
                        .iter()
                        .all(|fact| !matches!(fact, SpaceFact::Alias { .. })),
                    "LL(1) stream emitted a dynamic ambiguity alias: {facts:?}"
                );
                facts.clear();
            }
        }
    }
}
