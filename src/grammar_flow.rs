use crate::{
    core::{CoreGrammar, CoreSymbol},
    dataflow::{DeltaEngine, IncrementalReachability},
    grammar::{Grammar, Symbol},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FlowSymbol {
    Nonterminal(usize),
    Terminal(usize),
}

pub(crate) trait GrammarView {
    fn nonterminal_count(&self) -> usize;
    fn terminal_count(&self) -> usize;
    fn production_count(&self) -> usize;
    fn production_lhs(&self, production: usize) -> usize;
    fn production_len(&self, production: usize) -> usize;
    fn production_symbol(&self, production: usize, position: usize) -> FlowSymbol;
}

impl GrammarView for CoreGrammar {
    fn nonterminal_count(&self) -> usize {
        self.nonterminal_count
    }

    fn terminal_count(&self) -> usize {
        self.terminal_count
    }

    fn production_count(&self) -> usize {
        self.productions.len()
    }

    fn production_lhs(&self, production: usize) -> usize {
        self.productions[production].lhs
    }

    fn production_len(&self, production: usize) -> usize {
        self.productions[production].rhs.len()
    }

    fn production_symbol(&self, production: usize, position: usize) -> FlowSymbol {
        match self.productions[production].rhs[position] {
            CoreSymbol::Nonterminal(nonterminal) => FlowSymbol::Nonterminal(nonterminal),
            CoreSymbol::Terminal(terminal) => FlowSymbol::Terminal(terminal),
        }
    }
}

impl GrammarView for Grammar {
    fn nonterminal_count(&self) -> usize {
        self.nonterminal_count()
    }

    fn terminal_count(&self) -> usize {
        self.terminal_count()
    }

    fn production_count(&self) -> usize {
        self.productions().len()
    }

    fn production_lhs(&self, production: usize) -> usize {
        self.productions()[production].lhs.index()
    }

    fn production_len(&self, production: usize) -> usize {
        self.productions()[production].rhs.len()
    }

    fn production_symbol(&self, production: usize, position: usize) -> FlowSymbol {
        match self.productions()[production].rhs[position] {
            Symbol::Nonterminal(nonterminal) => FlowSymbol::Nonterminal(nonterminal.index()),
            Symbol::Terminal(terminal) => FlowSymbol::Terminal(terminal.index()),
        }
    }
}

/// Dense terminal set shared by recognition-only and semantic PwZ compilers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TerminalSet {
    words: Box<[u64]>,
}

impl TerminalSet {
    fn new(terminal_count: usize) -> Self {
        Self {
            words: vec![0; terminal_count.div_ceil(64)].into_boxed_slice(),
        }
    }

    fn insert(&mut self, terminal: usize) -> bool {
        let word = &mut self.words[terminal / 64];
        let mask = 1u64 << (terminal % 64);
        let new = *word & mask == 0;
        *word |= mask;
        new
    }

    fn union_with(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (word, other) in self.words.iter_mut().zip(other.words.iter().copied()) {
            let merged = *word | other;
            changed |= merged != *word;
            *word = merged;
        }
        changed
    }

    #[cfg(test)]
    fn contains(&self, terminal: usize) -> bool {
        self.words
            .get(terminal / 64)
            .is_some_and(|word| word & (1u64 << (terminal % 64)) != 0)
    }

    pub(crate) fn words(&self) -> &[u64] {
        &self.words
    }

    fn intersects(&self, other: &Self) -> bool {
        self.words
            .iter()
            .zip(&other.words)
            .any(|(left, right)| left & right != 0)
    }

    fn terminals(&self) -> impl Iterator<Item = usize> + '_ {
        self.words
            .iter()
            .enumerate()
            .flat_map(|(word_index, word)| {
                let mut remaining = *word;
                std::iter::from_fn(move || {
                    if remaining == 0 {
                        return None;
                    }
                    let bit = remaining.trailing_zeros() as usize;
                    remaining &= remaining - 1;
                    Some(word_index * 64 + bit)
                })
            })
    }
}

/// Productive, nullable, FIRST, FOLLOW, and production SELECT facts for a CFG.
///
/// Productivity and nullability use occurrence-counted agendas. FIRST and
/// FOLLOW are instances of the shared event-driven propagation closure.
pub(crate) struct GrammarFlowAnalysis {
    productive_productions: Box<[bool]>,
    #[cfg(test)]
    nullable: Box<[bool]>,
    #[cfg(test)]
    first: Box<[TerminalSet]>,
    #[cfg(test)]
    follow: Box<[TerminalSet]>,
    selects: Box<[TerminalSet]>,
    #[cfg(test)]
    production_nullable: Box<[bool]>,
    ll1: bool,
}

impl GrammarFlowAnalysis {
    pub(crate) fn compute(grammar: &impl GrammarView) -> Self {
        let productive_productions = productive_productions(grammar);
        let nullable = nullable_nonterminals(grammar, &productive_productions);
        let first = first_sets(grammar, &productive_productions, &nullable);
        let follow = follow_sets(grammar, &productive_productions, &nullable, &first);

        let mut selects = Vec::with_capacity(grammar.production_count());
        let mut production_nullable = Vec::with_capacity(grammar.production_count());
        for production in 0..grammar.production_count() {
            let (mut select, nullable_rhs) =
                first_of_production(grammar, production, &nullable, &first);
            if nullable_rhs {
                select.union_with(&follow[grammar.production_lhs(production)]);
            }
            selects.push(select);
            production_nullable.push(nullable_rhs);
        }

        let mut seen = (0..grammar.nonterminal_count())
            .map(|_| TerminalSet::new(grammar.terminal_count()))
            .collect::<Vec<_>>();
        let mut seen_nullable = vec![false; grammar.nonterminal_count()];
        let mut ll1 = true;
        for production in 0..grammar.production_count() {
            if !productive_productions[production] {
                continue;
            }
            let lhs = grammar.production_lhs(production);
            if seen[lhs].intersects(&selects[production])
                || (production_nullable[production] && seen_nullable[lhs])
            {
                ll1 = false;
                break;
            }
            seen[lhs].union_with(&selects[production]);
            seen_nullable[lhs] |= production_nullable[production];
        }

        Self {
            productive_productions: productive_productions.into_boxed_slice(),
            #[cfg(test)]
            nullable: nullable.into_boxed_slice(),
            #[cfg(test)]
            first: first.into_boxed_slice(),
            #[cfg(test)]
            follow: follow.into_boxed_slice(),
            selects: selects.into_boxed_slice(),
            #[cfg(test)]
            production_nullable: production_nullable.into_boxed_slice(),
            ll1,
        }
    }

    pub(crate) fn productive_productions(&self) -> &[bool] {
        &self.productive_productions
    }

    #[cfg(test)]
    pub(crate) fn nullable(&self) -> &[bool] {
        &self.nullable
    }

    #[cfg(test)]
    pub(crate) fn first(&self) -> &[TerminalSet] {
        &self.first
    }

    #[cfg(test)]
    pub(crate) fn follow(&self) -> &[TerminalSet] {
        &self.follow
    }

    pub(crate) fn select(&self, production: usize) -> &TerminalSet {
        &self.selects[production]
    }

    #[cfg(test)]
    pub(crate) fn production_nullable(&self, production: usize) -> bool {
        self.production_nullable[production]
    }

    pub(crate) fn is_ll1(&self) -> bool {
        self.ll1
    }
}

fn productive_productions(grammar: &impl GrammarView) -> Vec<bool> {
    let mut remaining = vec![0usize; grammar.production_count()];
    let mut dependents = vec![Vec::<usize>::new(); grammar.nonterminal_count()];
    for (production, remaining) in remaining.iter_mut().enumerate() {
        for position in 0..grammar.production_len(production) {
            if let FlowSymbol::Nonterminal(nonterminal) =
                grammar.production_symbol(production, position)
            {
                *remaining += 1;
                // Keep repeated occurrences: A -> B B has two obligations.
                dependents[nonterminal].push(production);
            }
        }
    }

    let mut productive_production = vec![false; grammar.production_count()];
    let mut productive_nonterminal = vec![false; grammar.nonterminal_count()];
    let mut agenda = DeltaEngine::default();
    for (production, count) in remaining.iter().copied().enumerate() {
        if count == 0 {
            productive_production[production] = true;
            let lhs = grammar.production_lhs(production);
            if !productive_nonterminal[lhs] {
                productive_nonterminal[lhs] = true;
                agenda.enqueue_new(lhs);
            }
        }
    }
    agenda.close(|nonterminal, agenda| {
        for &production in &dependents[nonterminal] {
            remaining[production] -= 1;
            if remaining[production] == 0 {
                productive_production[production] = true;
                let lhs = grammar.production_lhs(production);
                if !productive_nonterminal[lhs] {
                    productive_nonterminal[lhs] = true;
                    agenda.enqueue_new(lhs);
                }
            }
        }
    });
    productive_production
}

fn nullable_nonterminals(grammar: &impl GrammarView, productive: &[bool]) -> Vec<bool> {
    let blocked = usize::MAX;
    let mut remaining = vec![blocked; grammar.production_count()];
    let mut dependents = vec![Vec::<usize>::new(); grammar.nonterminal_count()];
    for production in 0..grammar.production_count() {
        if !productive[production] {
            continue;
        }
        let mut count = 0usize;
        let mut has_terminal = false;
        for position in 0..grammar.production_len(production) {
            match grammar.production_symbol(production, position) {
                FlowSymbol::Terminal(_) => has_terminal = true,
                FlowSymbol::Nonterminal(nonterminal) => {
                    count += 1;
                    dependents[nonterminal].push(production);
                }
            }
        }
        if !has_terminal {
            remaining[production] = count;
        }
    }

    let mut nullable = vec![false; grammar.nonterminal_count()];
    let mut agenda = DeltaEngine::default();
    for (production, count) in remaining.iter().copied().enumerate() {
        if count == 0 {
            let lhs = grammar.production_lhs(production);
            if !nullable[lhs] {
                nullable[lhs] = true;
                agenda.enqueue_new(lhs);
            }
        }
    }
    agenda.close(|nonterminal, agenda| {
        for &production in &dependents[nonterminal] {
            if remaining[production] == blocked {
                continue;
            }
            remaining[production] -= 1;
            if remaining[production] == 0 {
                let lhs = grammar.production_lhs(production);
                if !nullable[lhs] {
                    nullable[lhs] = true;
                    agenda.enqueue_new(lhs);
                }
            }
        }
    });
    nullable
}

fn first_sets(
    grammar: &impl GrammarView,
    productive: &[bool],
    nullable: &[bool],
) -> Vec<TerminalSet> {
    let mut flow = IncrementalReachability::<usize, usize>::default();
    for (production, &is_productive) in productive.iter().enumerate() {
        if !is_productive {
            continue;
        }
        let lhs = grammar.production_lhs(production);
        for position in 0..grammar.production_len(production) {
            match grammar.production_symbol(production, position) {
                FlowSymbol::Terminal(terminal) => {
                    flow.add_fact(lhs, terminal);
                    break;
                }
                FlowSymbol::Nonterminal(nonterminal) => {
                    flow.add_edge(nonterminal, lhs);
                    if !nullable[nonterminal] {
                        break;
                    }
                }
            }
        }
    }
    let mut first = (0..grammar.nonterminal_count())
        .map(|_| TerminalSet::new(grammar.terminal_count()))
        .collect::<Vec<_>>();
    for (nonterminal, terminal) in flow.close() {
        first[nonterminal].insert(terminal);
    }
    first
}

fn follow_sets(
    grammar: &impl GrammarView,
    productive: &[bool],
    nullable: &[bool],
    first: &[TerminalSet],
) -> Vec<TerminalSet> {
    let mut flow = IncrementalReachability::<usize, usize>::default();
    for (production, &is_productive) in productive.iter().enumerate() {
        if !is_productive {
            continue;
        }
        let lhs = grammar.production_lhs(production);
        for position in 0..grammar.production_len(production) {
            let FlowSymbol::Nonterminal(current) = grammar.production_symbol(production, position)
            else {
                continue;
            };
            let mut suffix_nullable = true;
            for suffix in position + 1..grammar.production_len(production) {
                match grammar.production_symbol(production, suffix) {
                    FlowSymbol::Terminal(terminal) => {
                        flow.add_fact(current, terminal);
                        suffix_nullable = false;
                        break;
                    }
                    FlowSymbol::Nonterminal(nonterminal) => {
                        for terminal in first[nonterminal].terminals() {
                            flow.add_fact(current, terminal);
                        }
                        if !nullable[nonterminal] {
                            suffix_nullable = false;
                            break;
                        }
                    }
                }
            }
            if suffix_nullable {
                flow.add_edge(lhs, current);
            }
        }
    }
    let mut follow = (0..grammar.nonterminal_count())
        .map(|_| TerminalSet::new(grammar.terminal_count()))
        .collect::<Vec<_>>();
    for (nonterminal, terminal) in flow.close() {
        follow[nonterminal].insert(terminal);
    }
    follow
}

fn first_of_production(
    grammar: &impl GrammarView,
    production: usize,
    nullable: &[bool],
    first: &[TerminalSet],
) -> (TerminalSet, bool) {
    let mut result = TerminalSet::new(grammar.terminal_count());
    for position in 0..grammar.production_len(production) {
        match grammar.production_symbol(production, position) {
            FlowSymbol::Terminal(terminal) => {
                result.insert(terminal);
                return (result, false);
            }
            FlowSymbol::Nonterminal(nonterminal) => {
                result.union_with(&first[nonterminal]);
                if !nullable[nonterminal] {
                    return (result, false);
                }
            }
        }
    }
    (result, true)
}

#[cfg(test)]
mod tests {
    use crate::core::{CoreGrammar, CoreProduction, CoreSymbol};

    use super::GrammarFlowAnalysis;

    fn n(id: usize) -> CoreSymbol {
        CoreSymbol::Nonterminal(id)
    }

    fn t(id: usize) -> CoreSymbol {
        CoreSymbol::Terminal(id)
    }

    #[test]
    fn occurrence_counting_handles_repeated_dependencies() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 2,
            terminal_count: 1,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![n(1), n(1)],
                },
                CoreProduction {
                    lhs: 1,
                    rhs: vec![t(0)],
                },
            ],
        };
        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert_eq!(flow.productive_productions(), [true, true]);
        assert!(flow.select(0).contains(0));
    }

    #[test]
    fn unproductive_cycles_do_not_contribute_first_or_select() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 3,
            terminal_count: 2,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![n(1)],
                },
                CoreProduction {
                    lhs: 1,
                    rhs: vec![n(0)],
                },
                CoreProduction {
                    lhs: 2,
                    rhs: vec![t(1)],
                },
            ],
        };
        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert_eq!(flow.productive_productions(), [false, false, true]);
        assert!(!flow.select(0).contains(0));
        assert!(!flow.select(0).contains(1));
    }

    #[test]
    fn nullable_first_and_follow_propagate_through_cycles() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 3,
            terminal_count: 2,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![n(1), t(1)],
                },
                CoreProduction {
                    lhs: 1,
                    rhs: vec![n(2)],
                },
                CoreProduction {
                    lhs: 2,
                    rhs: vec![n(1)],
                },
                CoreProduction {
                    lhs: 2,
                    rhs: vec![],
                },
                CoreProduction {
                    lhs: 1,
                    rhs: vec![t(0)],
                },
            ],
        };
        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert!(flow.nullable()[1]);
        assert!(flow.nullable()[2]);
        assert!(flow.first()[1].contains(0));
        assert!(flow.first()[2].contains(0));
        assert!(flow.follow()[1].contains(1));
        assert!(flow.follow()[2].contains(1));
        assert!(flow.select(0).contains(0));
        assert!(flow.select(0).contains(1));
    }

    #[test]
    fn nullable_end_marker_conflict_is_not_lost_when_follow_is_empty() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 1,
            terminal_count: 0,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![],
                },
                CoreProduction {
                    lhs: 0,
                    rhs: vec![],
                },
            ],
        };
        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert!(!flow.is_ll1());
        assert!(flow.production_nullable(0));
        assert!(flow.production_nullable(1));
    }

    #[test]
    fn nullable_flags_remain_aligned_after_a_nonnullable_alternative() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 1,
            terminal_count: 1,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![t(0)],
                },
                CoreProduction {
                    lhs: 0,
                    rhs: vec![],
                },
                CoreProduction {
                    lhs: 0,
                    rhs: vec![],
                },
            ],
        };
        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert!(!flow.production_nullable(0));
        assert!(flow.production_nullable(1));
        assert!(flow.production_nullable(2));
        assert!(!flow.is_ll1());
    }

    #[test]
    fn large_first_and_follow_chain_reaches_a_fixed_point() {
        const DEPTH: usize = 4_096;
        let mut productions = Vec::with_capacity(DEPTH + 1);
        // N0 -> N1 t1 gives every nonterminal below N0 the same FOLLOW
        // obligation. The remaining unit chain stresses long-distance FIRST
        // and FOLLOW propagation through the shared dataflow kernel.
        productions.push(CoreProduction {
            lhs: 0,
            rhs: vec![n(1), t(1)],
        });
        for lhs in 1..DEPTH {
            productions.push(CoreProduction {
                lhs,
                rhs: vec![n(lhs + 1)],
            });
        }
        productions.push(CoreProduction {
            lhs: DEPTH,
            rhs: vec![t(0)],
        });
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: DEPTH + 1,
            terminal_count: 2,
            productions,
        };

        let flow = GrammarFlowAnalysis::compute(&grammar);
        assert!(
            flow.productive_productions()
                .iter()
                .all(|productive| *productive)
        );
        assert!(flow.first()[0].contains(0));
        assert!(flow.first()[DEPTH].contains(0));
        assert!(flow.follow()[1].contains(1));
        assert!(flow.follow()[DEPTH].contains(1));
        assert!(flow.is_ll1());
    }
}
