// Remaining cases ported from ChopChop's `tests/test_egraph.py` at commit
// 681083a6fd921ac9cbaf984db628cf92eb019a3f (MIT).
//
// ChopChop asks at character boundaries. This crate consumes complete
// lexemes, so the syntax assertions below ask at the final lexeme boundary,
// and the e-graph cases check epsilon plus every complete-lexeme boundary.

use prefixspace::{Grammar, LivePrefixMonitor, PwzRecognizer};

const LET_YACC: &str = r#"
%start start
%token LET IN ID EQ INT PLUS MINUS STAR SLASH LPAREN RPAREN
%%
start: scoped                         { $1 }
     ;
scoped: add                           { $1 }
      | LET id EQ add IN scoped       { Let(2, 4, 6) }
      ;
add: mul                              { $1 }
   | add PLUS mul                     { Add(1, 3) }
   | add MINUS mul                    { Sub(1, 3) }
   ;
mul: app                              { $1 }
   | mul STAR app                     { Mul(1, 3) }
   | mul SLASH app                    { Div(1, 3) }
   ;
app: atom                             { $1 }
   | app non_neg_atom                 { App(1, 2) }
   ;
atom: non_neg_atom                    { $1 }
    | MINUS atom                      { Neg(2) }
    ;
non_neg_atom: id                      { $1 }
            | num                     { $1 }
            | LPAREN add RPAREN       { $2 }
            ;
id: ID                                { Var(1) }
  ;
num: INT                              { Num(1) }
   ;
"#;

const LET_LEX: &str = r#"
%%
let                        'LET'
in                         'IN'
=                          'EQ'
\+                         'PLUS'
-                          'MINUS'
\*                         'STAR'
/                          'SLASH'
\(                         'LPAREN'
\)                         'RPAREN'
[0-9]+                     'INT'
[a-zA-Z_][a-zA-Z0-9_]*     'ID'
[ \t\r\n]+                 ;
"#;

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

fn grammar() -> Grammar {
    Grammar::from_yacc_lex(LET_YACC, LET_LEX).unwrap()
}

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
    let grammar = grammar();
    let tokens = grammar.lex(source).unwrap();
    let program = target_program(target_term);
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, &program, "$root").unwrap();
    assert!(
        !monitor.intersection_is_empty(),
        "target has no completion at epsilon for {source:?}"
    );
    for token in tokens {
        let terminal = grammar.terminal_name(token.kind);
        assert!(
            !monitor.push_token_name(terminal, &token.lexeme).unwrap(),
            "target has no completion after {:?} in {source:?}",
            &source[..token.end]
        );
    }
}

#[test]
fn remaining_dynamic_let_cases_have_target_completions_at_every_lexeme_boundary() {
    // The first upstream query is a prefix rather than a complete target AST:
    // appending `+ 3` gives the represented target completion.
    assert_every_lexeme_prefix_viable(
        "let y = 3 in 3",
        r#"(Let (Var "y") (Num 3) (Add (Num 3) (Num 3)))"#,
    );
    assert_every_lexeme_prefix_viable("let y = 6 in y", r#"(Let (Var "y") (Num 6) (Var "y"))"#);
    assert_every_lexeme_prefix_viable(
        "let z = 3 * 2 in z",
        r#"(Let (Var "z") (Mul (Num 3) (Num 2)) (Var "z"))"#,
    );
    assert_every_lexeme_prefix_viable(
        "let u = 3 in let v = 2 in u * v",
        r#"(Let (Var "u") (Num 3)
             (Let (Var "v") (Num 2) (Mul (Var "u") (Var "v"))))"#,
    );
}

#[test]
fn duplicate_name_case_has_no_completion_in_the_single_binding_target_class() {
    let grammar = grammar();
    let source = "let y = 6 in let y = 6 in y";
    let program = target_program(r#"(Let (Var "y") (Num 6) (Var "y"))"#);
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, &program, "$root").unwrap();
    for token in grammar.lex(source).unwrap() {
        let terminal = grammar.terminal_name(token.kind);
        monitor.push_token_name(terminal, &token.lexeme).unwrap();
    }
    assert!(monitor.intersection_is_empty());
}

fn syntax_prefix_has_completion(source: &str) -> bool {
    let grammar = grammar();
    let mut parser = PwzRecognizer::compile(&grammar).unwrap();
    for token in grammar.lex(source).unwrap() {
        parser.push(token.kind).unwrap();
    }
    parser.has_completion()
}

#[test]
fn chopchop_expression_grammar_baseline_at_lexeme_boundaries() {
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
            syntax_prefix_has_completion(source),
            "expected a syntactic completion for {source:?}"
        );
    }
    for source in ["+ x", "let =", ")", "()"] {
        assert!(
            !syntax_prefix_has_completion(source),
            "unexpected syntactic completion for {source:?}"
        );
    }
}
