//! Conversion from the input CFG representation to the expression graph used
//! by Parsing with Zippers.

use rustc_hash::FxHashMap as HashMap;

use crate::{
    grammar::{Grammar as InputGrammar, Symbol as InputSymbol},
    paper_pwz::{ExpressionId, ExpressionNode, Grammar, Symbol},
};

/// Builds the cyclic expression graph consumed by `paper_pwz`.
///
/// Nonterminals are alternatives, terminals are token expressions, and each
/// production is one sequence. Its numeric label is the index of the
/// production's semantic action in the input grammar.
pub(crate) fn compile<P>(input: &InputGrammar) -> Grammar<P> {
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

    let mut alternatives = vec![Vec::new(); nonterminals];
    for (production, rule) in input.productions().iter().enumerate() {
        alternatives[rule.lhs.index()].push(id(production_base + production));
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

    Grammar {
        root: id(input.start().index()),
        expressions,
    }
}

fn id(index: usize) -> ExpressionId {
    ExpressionId(as_u32(index))
}

fn as_u32(value: usize) -> u32 {
    u32::try_from(value).expect("grammar value exceeds PwZ ID capacity")
}

#[cfg(test)]
mod tests {
    use super::compile;
    use crate::{
        grammar::Grammar as InputGrammar,
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
        let output = compile::<()>(&input);

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
        let output = compile::<()>(&input);

        assert_eq!(
            output.expressions[&ExpressionId(1)],
            ExpressionNode::Seq {
                symbol: Symbol::Grammar(0),
                children: Vec::new(),
            }
        );
    }
}
