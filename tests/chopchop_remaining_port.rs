// Remaining cases ported from ChopChop's `tests/test_egraph.py` at commit
// 681083a6fd921ac9cbaf984db628cf92eb019a3f (MIT).
//
// ChopChop asks at character boundaries. This crate consumes complete
// lexemes, so the syntax assertions below ask at the final lexeme boundary,
// and the e-graph cases check epsilon plus every complete-lexeme boundary.

#[path = "support/chopchop_let.rs"]
mod chopchop_let;

use prefixspace::Monitor;

const MATH_DATATYPE: &str = r#"
(datatype Math
  (Num i64)
  (Var String)
  (Add Math Math)
  (Sub Math Math)
  (Neg Math)
  (Mul Math Math)
  (Div Math Math)
  (App Math Math)
  (Let Math Math Math))
"#;

fn target_program(target_term: &str) -> String {
    format!(
        r#"
        {MATH_DATATYPE}
        (let $root (Num 6))
        (union $root {target_term})
        "#
    )
}

fn assert_every_lexeme_prefix_viable(source: &str, target_term: &str) {
    let grammar = chopchop_let::grammar();
    let tokens = grammar.lex(source).unwrap();
    let program = target_program(target_term);
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();
    assert_eq!(
        monitor.realizability(),
        Some(true),
        "target has no completion at epsilon for {source:?}"
    );
    for token in tokens {
        let terminal = grammar.terminal_name(token.kind);
        assert_eq!(
            monitor.push_token_name(terminal, &token.lexeme).unwrap(),
            Some(true),
            "target has no completion after {:?} in {source:?}",
            &source[..token.end]
        );
    }
}

#[test]
fn nested_let_has_a_target_completion_at_every_lexeme_boundary() {
    assert_every_lexeme_prefix_viable(
        "let u = 3 in let v = 2 in u * v",
        r#"(Let (Var "u") (Num 3)
             (Let (Var "v") (Num 2) (Mul (Var "u") (Var "v"))))"#,
    );
}

#[test]
fn duplicate_name_case_has_no_completion_in_the_single_binding_target_class() {
    let grammar = chopchop_let::grammar();
    let source = "let y = 6 in let y = 6 in y";
    let program = target_program(r#"(Let (Var "y") (Num 6) (Var "y"))"#);
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();
    for token in grammar.lex(source).unwrap() {
        let terminal = grammar.terminal_name(token.kind);
        monitor.push_token_name(terminal, &token.lexeme).unwrap();
    }
    assert_eq!(monitor.realizability(), None);
}
