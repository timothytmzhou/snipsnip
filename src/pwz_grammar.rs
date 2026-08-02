//! Conversion from the input CFG representation to the expression graph used
//! by Parsing with Zippers.

use std::sync::Arc;

use rustc_hash::FxHashMap as HashMap;

use crate::{
    grammar::{Action, Grammar as InputGrammar, GrammarError, Symbol as InputSymbol},
    paper_pwz::{ExpressionId, ExpressionNode, Grammar, Symbol},
    realizability::{ConstructorId, ConstructorSchema, Schema, SemanticAction},
};

/// Builds the cyclic expression graph consumed by `paper_pwz`.
///
/// Nonterminals are alternatives, terminals are token expressions, and each
/// productive production is one sequence. Removing productions with no
/// finite completion does not change the grammar's completed parse trees and
/// ensures that every zipper returned by a derivative has a completion. A
/// sequence's numeric label remains the index of its action in the unmodified
/// input grammar.
pub(crate) fn compile<P>(input: &InputGrammar) -> Result<Grammar<P>, GrammarError> {
    let nonterminals = input.nonterminal_count();
    let terminals = input.terminal_count();
    let production_base = nonterminals
        .checked_add(terminals)
        .expect("grammar expression count exceeds usize");
    let expression_count = production_base
        .checked_add(input.productions().len())
        .expect("grammar expression count exceeds usize");
    assert!(
        expression_count <= u32::MAX as usize,
        "grammar expression count exceeds PwZ ID capacity"
    );

    let terminal_productive = input.complete_lexeme_terminals()?;
    let productive = productive_productions(input, &terminal_productive);
    let mut alternatives = vec![Vec::new(); nonterminals];
    for (production, rule) in input.productions().iter().enumerate() {
        if productive[production] {
            alternatives[rule.lhs.index()].push(id(production_base + production));
        }
    }

    let mut expressions = HashMap::default();
    expressions.reserve(expression_count);
    for (nonterminal, children) in alternatives.into_iter().enumerate() {
        expressions.insert(id(nonterminal), ExpressionNode::Alt { children });
    }
    for terminal in 0..terminals {
        expressions.insert(
            id(nonterminals + terminal),
            ExpressionNode::Tok(as_u32(terminal)),
        );
    }
    for (production, rule) in input.productions().iter().enumerate() {
        if !productive[production] {
            continue;
        }
        let children = rule
            .rhs
            .iter()
            .map(|symbol| match symbol {
                InputSymbol::Nonterminal(nonterminal) => id(nonterminal.index()),
                InputSymbol::Terminal(terminal) => id(nonterminals + terminal.index()),
            })
            .collect();
        expressions.insert(
            id(production_base + production),
            ExpressionNode::Seq {
                symbol: Symbol::Grammar(as_u32(production)),
                children,
            },
        );
    }

    let select_sets = compute_select_sets(input, &productive);
    let select = productive
        .iter()
        .enumerate()
        .filter(|(_, productive)| **productive)
        .map(|(production, _)| {
            let terminals = (0..terminals)
                .filter(|terminal| select_sets.contains(production, *terminal))
                .map(as_u32)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            (id(production_base + production), terminals)
        })
        .collect();

    Ok(Grammar {
        root: id(input.start().index()),
        expressions,
        select,
    })
}

impl<P> TryFrom<&InputGrammar> for Grammar<P> {
    type Error = GrammarError;

    fn try_from(input: &InputGrammar) -> Result<Self, Self::Error> {
        compile(input)
    }
}

/// Resolves the grammar's symbolic annotations against one semantic backend.
pub(crate) fn semantics(
    input: &InputGrammar,
    constructor_id: impl Fn(&str) -> ConstructorId,
    constructors: Arc<[ConstructorSchema]>,
) -> Schema {
    let actions = input
        .productions()
        .iter()
        .map(|production| match &production.action {
            Action::Construct {
                constructor,
                arguments,
            } => SemanticAction::Construct {
                constructor: constructor_id(constructor),
                arguments: arguments.iter().map(|position| position - 1).collect(),
            },
            Action::Project { position } => SemanticAction::Project {
                position: position - 1,
            },
        })
        .collect::<Vec<_>>();
    Schema {
        actions: actions.into(),
        constructors,
    }
}

fn productive_productions(input: &InputGrammar, terminal_productive: &[bool]) -> Vec<bool> {
    let mut nonterminals = vec![false; input.nonterminal_count()];
    loop {
        let mut changed = false;
        for production in input.productions() {
            let productive = production.rhs.iter().all(|symbol| match symbol {
                InputSymbol::Terminal(terminal) => terminal_productive[terminal.index()],
                InputSymbol::Nonterminal(nonterminal) => nonterminals[nonterminal.index()],
            });
            if productive && !nonterminals[production.lhs.index()] {
                nonterminals[production.lhs.index()] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    input
        .productions()
        .iter()
        .map(|production| {
            production.rhs.iter().all(|symbol| match symbol {
                InputSymbol::Terminal(terminal) => terminal_productive[terminal.index()],
                InputSymbol::Nonterminal(nonterminal) => nonterminals[nonterminal.index()],
            })
        })
        .collect()
}

/// Terminal membership in each original production's SELECT set.
///
/// The storage stays private so it can be attached to the PwZ expression
/// graph without exposing a particular bit-set layout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SelectSets {
    words_per_production: usize,
    bits: Box<[u64]>,
}

impl SelectSets {
    #[inline]
    pub(crate) fn contains(&self, production: usize, terminal: usize) -> bool {
        if self.words_per_production == 0 {
            return false;
        }
        let Some(base) = production.checked_mul(self.words_per_production) else {
            return false;
        };
        let word = terminal / u64::BITS as usize;
        if word >= self.words_per_production || base + word >= self.bits.len() {
            return false;
        }
        self.bits[base + word] & (1u64 << (terminal % u64::BITS as usize)) != 0
    }
}

/// Computes SELECT over the productions which can produce a finite token
/// sequence. EOF is deliberately absent: PwZ uses these sets only when it
/// already has a terminal lookahead.
#[cfg(test)]
pub(crate) fn select_sets(input: &InputGrammar) -> Result<SelectSets, GrammarError> {
    let terminal_productive = input.complete_lexeme_terminals()?;
    let productive = productive_productions(input, &terminal_productive);
    Ok(compute_select_sets(input, &productive))
}

fn compute_select_sets(input: &InputGrammar, productive: &[bool]) -> SelectSets {
    let nullable = nullable_nonterminals(input, productive);
    let words = input.terminal_count().div_ceil(u64::BITS as usize);
    let first = first_nonterminals(input, productive, &nullable, words);
    let follow = follow_nonterminals(input, productive, &nullable, &first, words);
    let bit_count = input
        .productions()
        .len()
        .checked_mul(words)
        .expect("grammar SELECT sets exceed usize");
    let mut bits = vec![0; bit_count];

    for (index, production) in input.productions().iter().enumerate() {
        if !productive[index] {
            continue;
        }
        let row = &mut bits[index * words..(index + 1) * words];
        if add_sequence_first(&production.rhs, &nullable, &first, words, row) {
            let lhs = production.lhs.index() * words;
            union_into(row, &follow[lhs..lhs + words]);
        }
    }
    SelectSets {
        words_per_production: words,
        bits: bits.into_boxed_slice(),
    }
}

fn nullable_nonterminals(input: &InputGrammar, productive: &[bool]) -> Vec<bool> {
    let mut nullable = vec![false; input.nonterminal_count()];
    loop {
        let mut changed = false;
        for (index, production) in input.productions().iter().enumerate() {
            if productive[index]
                && !nullable[production.lhs.index()]
                && production.rhs.iter().all(|symbol| match symbol {
                    InputSymbol::Terminal(_) => false,
                    InputSymbol::Nonterminal(nonterminal) => nullable[nonterminal.index()],
                })
            {
                nullable[production.lhs.index()] = true;
                changed = true;
            }
        }
        if !changed {
            return nullable;
        }
    }
}

fn first_nonterminals(
    input: &InputGrammar,
    productive: &[bool],
    nullable: &[bool],
    words: usize,
) -> Vec<u64> {
    let mut first = vec![0; input.nonterminal_count() * words];
    loop {
        let mut changed = false;
        for (index, production) in input.productions().iter().enumerate() {
            if !productive[index] {
                continue;
            }
            let lhs = production.lhs.index();
            for symbol in &production.rhs {
                match symbol {
                    InputSymbol::Terminal(terminal) => {
                        changed |= insert_terminal(&mut first, lhs, terminal.index(), words);
                        break;
                    }
                    InputSymbol::Nonterminal(nonterminal) => {
                        changed |= union_rows(&mut first, lhs, nonterminal.index(), words);
                        if !nullable[nonterminal.index()] {
                            break;
                        }
                    }
                }
            }
        }
        if !changed {
            return first;
        }
    }
}

fn follow_nonterminals(
    input: &InputGrammar,
    productive: &[bool],
    nullable: &[bool],
    first: &[u64],
    words: usize,
) -> Vec<u64> {
    let mut follow = vec![0; input.nonterminal_count() * words];
    loop {
        let mut changed = false;
        for (index, production) in input.productions().iter().enumerate() {
            if !productive[index] {
                continue;
            }
            let lhs = production.lhs.index() * words;
            let mut trailer = follow[lhs..lhs + words].to_vec();
            for symbol in production.rhs.iter().rev() {
                match symbol {
                    InputSymbol::Terminal(terminal) => {
                        trailer.fill(0);
                        set_terminal(&mut trailer, terminal.index());
                    }
                    InputSymbol::Nonterminal(nonterminal) => {
                        let row = nonterminal.index() * words;
                        changed |= union_into(&mut follow[row..row + words], &trailer);
                        if nullable[nonterminal.index()] {
                            union_into(&mut trailer, &first[row..row + words]);
                        } else {
                            trailer.copy_from_slice(&first[row..row + words]);
                        }
                    }
                }
            }
        }
        if !changed {
            return follow;
        }
    }
}

fn add_sequence_first(
    sequence: &[InputSymbol],
    nullable: &[bool],
    first: &[u64],
    words: usize,
    output: &mut [u64],
) -> bool {
    for symbol in sequence {
        match symbol {
            InputSymbol::Terminal(terminal) => {
                set_terminal(output, terminal.index());
                return false;
            }
            InputSymbol::Nonterminal(nonterminal) => {
                let row = nonterminal.index() * words;
                union_into(output, &first[row..row + words]);
                if !nullable[nonterminal.index()] {
                    return false;
                }
            }
        }
    }
    true
}

fn insert_terminal(bits: &mut [u64], row: usize, terminal: usize, words: usize) -> bool {
    let cell = &mut bits[row * words + terminal / u64::BITS as usize];
    let before = *cell;
    *cell |= 1u64 << (terminal % u64::BITS as usize);
    *cell != before
}

fn set_terminal(bits: &mut [u64], terminal: usize) {
    bits[terminal / u64::BITS as usize] |= 1u64 << (terminal % u64::BITS as usize);
}

fn union_rows(bits: &mut [u64], destination: usize, source: usize, words: usize) -> bool {
    let mut changed = false;
    for offset in 0..words {
        let source_word = bits[source * words + offset];
        let destination_word = &mut bits[destination * words + offset];
        let before = *destination_word;
        *destination_word |= source_word;
        changed |= *destination_word != before;
    }
    changed
}

fn union_into(destination: &mut [u64], source: &[u64]) -> bool {
    let mut changed = false;
    for (destination, source) in destination.iter_mut().zip(source) {
        let before = *destination;
        *destination |= *source;
        changed |= *destination != before;
    }
    changed
}

fn id(index: usize) -> ExpressionId {
    ExpressionId(as_u32(index))
}

fn as_u32(value: usize) -> u32 {
    u32::try_from(value).expect("grammar value exceeds PwZ ID capacity")
}

#[cfg(test)]
mod tests {
    use super::{compile, select_sets};
    use crate::{
        grammar::{Grammar as InputGrammar, GrammarError},
        paper_pwz::{ExpressionId, ExpressionNode, Symbol},
    };

    #[test]
    fn preserves_recursive_cfg_shape_and_production_labels() {
        let input = InputGrammar::from_yacc(
            r#"
            %start list
            %token ITEM COMMA
            %%
            list: item                         { One(1) }
                | list COMMA item              { More(1, 3) }
                ;
            item: ITEM                         { Item() };
            "#,
        )
        .unwrap();
        let output = compile::<()>(&input).unwrap();

        assert_eq!(output.root, ExpressionId(0));
        assert_eq!(
            output.expressions[&ExpressionId(0)],
            ExpressionNode::Alt {
                children: vec![ExpressionId(4), ExpressionId(5)]
            }
        );
        assert_eq!(
            output.expressions[&ExpressionId(5)],
            ExpressionNode::Seq {
                symbol: Symbol::Grammar(1),
                children: vec![ExpressionId(0), ExpressionId(3), ExpressionId(1)],
            }
        );
        assert_eq!(output.expressions[&ExpressionId(2)], ExpressionNode::Tok(0));
        assert_eq!(output.expressions[&ExpressionId(3)], ExpressionNode::Tok(1));
    }

    #[test]
    fn epsilon_is_an_empty_sequence() {
        let input = InputGrammar::from_yacc(
            r#"
            %start start
            %%
            start: { Empty() };
            "#,
        )
        .unwrap();
        let output = compile::<()>(&input).unwrap();

        assert_eq!(
            output.expressions[&ExpressionId(1)],
            ExpressionNode::Seq {
                symbol: Symbol::Grammar(0),
                children: Vec::new(),
            }
        );
    }

    #[test]
    fn removes_branches_which_can_never_complete() {
        let input = InputGrammar::from_yacc(
            r#"
            %start start
            %token A
            %%
            start: A dead { Bad() }
                 | A      { Good() }
                 ;
            dead: dead    { $1 };
            "#,
        )
        .unwrap();
        let output = compile::<()>(&input).unwrap();

        assert_eq!(
            output.expressions[&ExpressionId(0)],
            ExpressionNode::Alt {
                children: vec![ExpressionId(4)]
            }
        );
        assert!(!output.expressions.contains_key(&ExpressionId(3)));
        assert!(!output.expressions.contains_key(&ExpressionId(5)));
    }

    #[test]
    fn removes_a_suffix_whose_rule_is_shadowed_by_equal_length_priority() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token KEEP EARLY SHADOWED
            %%
            start: fixed SHADOWED { $1 }
                 | fixed          { $1 }
                 ;
            fixed: KEEP           { Good() };
            "#,
            r#"
            %%
            k 'KEEP'
            x 'EARLY'
            x 'SHADOWED'
            "#,
        )
        .unwrap();

        let terminals = input.complete_lexeme_terminals().unwrap();
        assert!(terminals[input.terminal_by_name("EARLY").unwrap().index()]);
        assert!(!terminals[input.terminal_by_name("SHADOWED").unwrap().index()]);

        let output = compile::<()>(&input).unwrap();
        let ExpressionNode::Alt { children } = &output.expressions[&output.root] else {
            panic!("the start nonterminal must be an alternative");
        };
        assert_eq!(children.len(), 1);
        assert!(matches!(
            output.expressions[&children[0]],
            ExpressionNode::Seq {
                symbol: Symbol::Grammar(1),
                ..
            }
        ));
    }

    #[test]
    fn an_ignored_rule_can_shadow_a_terminal_completely() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token SHADOWED
            %%
            start: SHADOWED { Bad() };
            "#,
            r#"
            %%
            x ;
            x 'SHADOWED'
            "#,
        )
        .unwrap();

        let terminals = input.complete_lexeme_terminals().unwrap();
        assert!(!terminals[input.terminal_by_name("SHADOWED").unwrap().index()]);
        let output = compile::<()>(&input).unwrap();
        assert_eq!(
            output.expressions[&output.root],
            ExpressionNode::Alt {
                children: Vec::new()
            }
        );
    }

    #[test]
    fn a_longer_later_rule_survives_maximal_munch() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token EARLY LATE
            %%
            start: LATE { Good() };
            "#,
            r#"
            %%
            a|ab 'EARLY'
            ab   'LATE'
            "#,
        )
        .unwrap();

        assert_eq!(
            input.terminal_name(input.lex("ab").unwrap()[0].kind),
            "LATE"
        );
        let terminals = input.complete_lexeme_terminals().unwrap();
        assert!(terminals[input.terminal_by_name("EARLY").unwrap().index()]);
        assert!(terminals[input.terminal_by_name("LATE").unwrap().index()]);
        let output = compile::<()>(&input).unwrap();
        assert!(matches!(
            output.expressions[&output.root],
            ExpressionNode::Alt { ref children } if children.len() == 1
        ));
    }

    #[test]
    fn partial_keyword_overlap_does_not_kill_the_identifier_rule() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token IF IDENT
            %%
            start: IDENT { Name() };
            "#,
            r#"
            %%
            if      'IF'
            [a-z]+  'IDENT'
            "#,
        )
        .unwrap();

        let terminals = input.complete_lexeme_terminals().unwrap();
        assert!(terminals[input.terminal_by_name("IF").unwrap().index()]);
        assert!(terminals[input.terminal_by_name("IDENT").unwrap().index()]);
    }

    #[test]
    fn unsupported_unicode_fallback_is_an_explicit_error() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token WORD
            %%
            start: WORD { Word() };
            "#,
            r#"
            %%
            [a-z]+\b 'WORD'
            "#,
        )
        .unwrap();

        assert!(matches!(
            compile::<()>(&input),
            Err(GrammarError::LexicalProductivity(_))
        ));
    }

    #[test]
    fn select_uses_first_and_follow_for_a_nullable_alternative() {
        let input = InputGrammar::from_yacc(
            r#"
            %start start
            %token A B
            %%
            start: prefix B { Pair(1) };
            prefix: A { ANode() }
                  |   { Empty() }
                  ;
            "#,
        )
        .unwrap();
        let select = select_sets(&input).unwrap();
        let a = input.terminal_by_name("A").unwrap().index();
        let b = input.terminal_by_name("B").unwrap().index();

        assert!(select.contains(0, a));
        assert!(select.contains(0, b));
        assert!(select.contains(1, a));
        assert!(!select.contains(1, b));
        assert!(!select.contains(2, a));
        assert!(select.contains(2, b));
    }

    #[test]
    fn select_closes_recursive_follow_and_ignores_unproductive_rules() {
        let input = InputGrammar::from_yacc(
            r#"
            %start start
            %token A B
            %%
            start: choice B { Pair(1) };
            choice: choice A { $1 }
                  |          { Empty() }
                  | dead     { $1 }
                  ;
            dead: dead       { $1 };
            "#,
        )
        .unwrap();
        let select = select_sets(&input).unwrap();
        let a = input.terminal_by_name("A").unwrap().index();
        let b = input.terminal_by_name("B").unwrap().index();

        assert!(select.contains(0, a));
        assert!(select.contains(0, b));
        assert!(select.contains(1, a));
        assert!(!select.contains(1, b));
        assert!(select.contains(2, a));
        assert!(select.contains(2, b));
        for production in [3, 4] {
            assert!(!select.contains(production, a));
            assert!(!select.contains(production, b));
        }
    }

    #[test]
    fn select_excludes_a_lexically_shadowed_production() {
        let input = InputGrammar::from_yacc_lex(
            r#"
            %start start
            %token GOOD EARLY SHADOWED
            %%
            start: GOOD     { Good() }
                 | SHADOWED { Bad() }
                 ;
            "#,
            r#"
            %%
            g 'GOOD'
            x 'EARLY'
            x 'SHADOWED'
            "#,
        )
        .unwrap();
        let select = select_sets(&input).unwrap();
        let good = input.terminal_by_name("GOOD").unwrap().index();
        let shadowed = input.terminal_by_name("SHADOWED").unwrap().index();

        assert!(select.contains(0, good));
        assert!(!select.contains(1, shadowed));
    }
}
