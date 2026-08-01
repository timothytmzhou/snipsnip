use std::collections::{HashMap, HashSet, VecDeque};

use thiserror::Error;

use crate::{
    automaton::{RegularTreeGrammar, StateId},
    core::{CoreGrammar, CoreProduction, CoreSymbol},
    grammar::{Action, Grammar, Symbol},
};

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("target state {0:?} does not belong to this tree grammar")]
    InvalidTarget(StateId),
    #[error("compiled grammar is too large")]
    GrammarTooLarge,
}

pub(crate) fn constrained(
    grammar: &Grammar,
    automaton: &RegularTreeGrammar,
    target: StateId,
) -> Result<CoreGrammar, CompileError> {
    if target.index() >= automaton.state_count() {
        return Err(CompileError::InvalidTarget(target));
    }
    let base_count = grammar.nonterminal_count();
    let state_count = automaton.state_count();
    let nonterminal_count = base_count
        .checked_add(
            base_count
                .checked_mul(state_count)
                .ok_or(CompileError::GrammarTooLarge)?,
        )
        .ok_or(CompileError::GrammarTooLarge)?;

    let specialized = |nonterminal: usize, state: StateId| -> usize {
        base_count + nonterminal * state_count + state.index()
    };

    let mut productions = Vec::new();
    let mut seen = HashSet::new();
    let mut transitions_by_signature =
        HashMap::<(&str, usize), Vec<&crate::automaton::TreeTransition>>::new();
    for transition in automaton.transitions() {
        transitions_by_signature
            .entry((&transition.constructor, transition.children.len()))
            .or_default()
            .push(transition);
    }

    // A^top: the original syntax with no semantic restrictions.
    for production in grammar.productions() {
        let rule = CoreProduction {
            lhs: production.lhs.index(),
            rhs: production
                .rhs
                .iter()
                .map(|symbol| match symbol {
                    Symbol::Nonterminal(id) => CoreSymbol::Nonterminal(id.index()),
                    Symbol::Terminal(id) => CoreSymbol::Terminal(id.index()),
                })
                .collect(),
        };
        if seen.insert(rule.clone()) {
            productions.push(rule);
        }
    }

    for production in grammar.productions() {
        match &production.action {
            Action::Construct {
                constructor,
                arguments,
            } => {
                let signature = (constructor.as_str(), arguments.len());
                for transition in transitions_by_signature
                    .get(&signature)
                    .into_iter()
                    .flat_map(|transitions| transitions.iter().copied())
                {
                    let mut rhs = unconstrained_rhs(production);
                    let mut supported = true;
                    for (&position, &state) in arguments.iter().zip(&transition.children) {
                        let Symbol::Nonterminal(child) = production.rhs[position - 1] else {
                            // The frozen RTG frontend has no representation for
                            // lexeme-valued terminal leaves. The live monitor does.
                            supported = false;
                            break;
                        };
                        rhs[position - 1] =
                            CoreSymbol::Nonterminal(specialized(child.index(), state));
                    }
                    if !supported {
                        continue;
                    }
                    let rule = CoreProduction {
                        lhs: specialized(production.lhs.index(), transition.output),
                        rhs,
                    };
                    if seen.insert(rule.clone()) {
                        productions.push(rule);
                    }
                }
            }
            Action::Project { position } => {
                let Symbol::Nonterminal(child) = production.rhs[*position - 1] else {
                    continue;
                };
                for state_index in 0..state_count {
                    let state = StateId(u32::try_from(state_index).unwrap());
                    let mut rhs = unconstrained_rhs(production);
                    rhs[*position - 1] = CoreSymbol::Nonterminal(specialized(child.index(), state));
                    let rule = CoreProduction {
                        lhs: specialized(production.lhs.index(), state),
                        rhs,
                    };
                    if seen.insert(rule.clone()) {
                        productions.push(rule);
                    }
                }
            }
        }
    }

    let start = specialized(grammar.start().index(), target);
    Ok(trim(CoreGrammar {
        start,
        nonterminal_count,
        terminal_count: grammar.terminal_count(),
        productions,
    }))
}

fn unconstrained_rhs(production: &crate::grammar::Production) -> Vec<CoreSymbol> {
    production
        .rhs
        .iter()
        .map(|symbol| match symbol {
            Symbol::Nonterminal(id) => CoreSymbol::Nonterminal(id.index()),
            Symbol::Terminal(id) => CoreSymbol::Terminal(id.index()),
        })
        .collect()
}

fn trim(grammar: CoreGrammar) -> CoreGrammar {
    let mut productive = vec![false; grammar.nonterminal_count];
    let mut pending = vec![0usize; grammar.productions.len()];
    let mut dependents = vec![Vec::new(); grammar.nonterminal_count];
    for (production_index, production) in grammar.productions.iter().enumerate() {
        for symbol in &production.rhs {
            if let CoreSymbol::Nonterminal(nonterminal) = symbol {
                pending[production_index] += 1;
                dependents[*nonterminal].push(production_index);
            }
        }
    }

    let mut productivity_queue = VecDeque::new();
    for (production_index, production) in grammar.productions.iter().enumerate() {
        if pending[production_index] == 0 && !productive[production.lhs] {
            productive[production.lhs] = true;
            productivity_queue.push_back(production.lhs);
        }
    }
    while let Some(nonterminal) = productivity_queue.pop_front() {
        for &production_index in &dependents[nonterminal] {
            pending[production_index] -= 1;
            if pending[production_index] == 0 {
                let lhs = grammar.productions[production_index].lhs;
                if !productive[lhs] {
                    productive[lhs] = true;
                    productivity_queue.push_back(lhs);
                }
            }
        }
    }

    if !productive[grammar.start] {
        return CoreGrammar {
            start: 0,
            nonterminal_count: 1,
            terminal_count: grammar.terminal_count,
            productions: Vec::new(),
        };
    }

    let productive_productions = grammar
        .productions
        .into_iter()
        .filter(|production| {
            production.rhs.iter().all(|symbol| match symbol {
                CoreSymbol::Terminal(_) => true,
                CoreSymbol::Nonterminal(id) => productive[*id],
            })
        })
        .collect::<Vec<_>>();

    let mut by_lhs = vec![Vec::new(); grammar.nonterminal_count];
    for (index, production) in productive_productions.iter().enumerate() {
        by_lhs[production.lhs].push(index);
    }
    let mut reachable = vec![false; grammar.nonterminal_count];
    let mut queue = VecDeque::from([grammar.start]);
    reachable[grammar.start] = true;
    while let Some(nonterminal) = queue.pop_front() {
        for &production_index in &by_lhs[nonterminal] {
            for symbol in &productive_productions[production_index].rhs {
                if let CoreSymbol::Nonterminal(child) = symbol
                    && !reachable[*child]
                {
                    reachable[*child] = true;
                    queue.push_back(*child);
                }
            }
        }
    }

    let mut remap = vec![None; grammar.nonterminal_count];
    let mut next = 0;
    for (old, is_reachable) in reachable.iter().copied().enumerate() {
        if is_reachable {
            remap[old] = Some(next);
            next += 1;
        }
    }
    let productions = productive_productions
        .into_iter()
        .filter(|production| reachable[production.lhs])
        .map(|production| CoreProduction {
            lhs: remap[production.lhs].unwrap(),
            rhs: production
                .rhs
                .into_iter()
                .map(|symbol| match symbol {
                    CoreSymbol::Terminal(id) => CoreSymbol::Terminal(id),
                    CoreSymbol::Nonterminal(id) => CoreSymbol::Nonterminal(remap[id].unwrap()),
                })
                .collect(),
        })
        .collect();
    CoreGrammar {
        start: remap[grammar.start].unwrap(),
        nonterminal_count: next,
        terminal_count: grammar.terminal_count,
        productions,
    }
}

#[cfg(test)]
mod tests {
    use super::trim;
    use crate::core::{CoreGrammar, CoreProduction, CoreSymbol};

    #[test]
    fn removes_terminal_frontiers_with_no_finite_completion() {
        let grammar = CoreGrammar {
            start: 0,
            nonterminal_count: 2,
            terminal_count: 1,
            productions: vec![
                CoreProduction {
                    lhs: 0,
                    rhs: vec![CoreSymbol::Terminal(0), CoreSymbol::Nonterminal(1)],
                },
                CoreProduction {
                    lhs: 1,
                    rhs: vec![CoreSymbol::Nonterminal(1)],
                },
            ],
        };
        assert!(trim(grammar).productions.is_empty());
    }
}
