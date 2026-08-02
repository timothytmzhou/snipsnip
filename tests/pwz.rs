// Syntax-only cases ported from ChopChop's `tests/test_egraph.py` at commit
// 681083a6fd921ac9cbaf984db628cf92eb019a3f (MIT). ChopChop asks at character
// boundaries; this port asks after complete lexemes.

#[path = "support/chopchop_let.rs"]
mod chopchop_let;

use prefixspace::paper_pwz::{Grammar, Pwz, Token};

fn prefix_has_completion(source: &str) -> bool {
    let grammar = chopchop_let::grammar();
    let compiled: Grammar<()> = (&grammar).try_into().unwrap();
    let mut parser = Pwz::new(compiled);
    for token in grammar.lex(source).unwrap() {
        parser.derive(Token {
            terminal: token.kind.index() as u32,
            payload: (),
        });
    }
    !parser.zippers().is_empty()
}

#[test]
fn chopchop_expression_grammar_at_lexeme_boundaries() {
    for source in [
        "",
        "x",
        "42",
        "(x)",
        "x + y",
        "x * y",
        "x + y * z",
        "(x + y) * z",
        "f x",
        "f x y",
        "f x + g y",
        "let x = 1 in x",
        "let x = f y in x * z",
        "let x = 1 in let y = 2 in x + y",
        "x +",
        "let",
        "let x =",
        "let x = 1 in",
        "(x + y",
    ] {
        assert!(
            prefix_has_completion(source),
            "expected a syntactic completion for {source:?}"
        );
    }
    for source in ["+ x", "let =", ")", "()"] {
        assert!(
            !prefix_has_completion(source),
            "unexpected syntactic completion for {source:?}"
        );
    }
}
