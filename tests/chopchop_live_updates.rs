// Live-update cases derived from ChopChop's dynamic e-graph tests at
// https://github.com/large-loris-models/chopchop/tree/681083a6fd921ac9cbaf984db628cf92eb019a3f
// (MIT). ChopChop checks characters; this port pushes one complete lexeme at
// a time. See THIRD_PARTY_NOTICES.md for attribution and license text.

use prefixspace::{Grammar, LivePrefixMonitor};

const DECLARATION_YACC: &str = r#"
%start start
%token LET IN ID EQ INT PLUS STAR LPAREN RPAREN
%%
start: LET ID EQ expr IN expr    { Body(6) }
     ;
expr: add                        { $1 }
    ;
add: mul                         { $1 }
   | add PLUS mul                { Add(1, 3) }
   ;
mul: atom                        { $1 }
   | mul STAR atom               { Mul(1, 3) }
   ;
atom: ID                         { Var(1) }
    | INT                        { Num(1) }
    | LPAREN expr RPAREN         { $2 }
    ;
"#;

const DECLARATION_LEX: &str = r#"
%%
let                        'LET'
in                         'IN'
=                          'EQ'
\+                         'PLUS'
\*                         'STAR'
\(                         'LPAREN'
\)                         'RPAREN'
[0-9]+                     'INT'
[a-zA-Z_][a-zA-Z0-9_]*     'ID'
[ \t\r\n]+                 ;
"#;

const Y_AND_SIX: &str = r#"
(datatype Expr
  (Num i64)
  (Var String)
  (Add Expr Expr)
  (Mul Expr Expr))
(datatype Program (Body Expr))

(let $six (Num 6))
(let $y (Var "y"))
(let $root (Body $six))
"#;

const Z_AND_PRODUCT: &str = r#"
(datatype Expr
  (Num i64)
  (Var String)
  (Add Expr Expr)
  (Mul Expr Expr))
(datatype Program (Body Expr))

(let $three (Num 3))
(let $two (Num 2))
(let $product (Mul $three $two))
(let $z (Var "z"))
(let $root (Body $product))
"#;

fn declaration_grammar() -> Grammar {
    Grammar::from_yacc_lex(DECLARATION_YACC, DECLARATION_LEX).unwrap()
}

fn push_one(
    grammar: &Grammar,
    monitor: &mut LivePrefixMonitor,
    token: &prefixspace::Token,
    source: &str,
) -> bool {
    let terminal = grammar.terminal_name(token.kind);
    monitor
        .push_token_name(terminal, &token.lexeme)
        .unwrap_or_else(|error| {
            panic!(
                "failed to push {terminal} {:?} from {source:?}: {error}",
                token.lexeme
            )
        })
}

#[test]
fn union_at_in_keeps_y_body_viable_and_late_union_resurrects_it() {
    let grammar = declaration_grammar();
    let source = "let y = 6 in y";
    let tokens = grammar.lex(source).unwrap();

    let mut updated_at_in = LivePrefixMonitor::from_egglog(&grammar, Y_AND_SIX, "$root").unwrap();
    assert!(!updated_at_in.intersection_is_empty());
    for token in &tokens {
        let terminal = grammar.terminal_name(token.kind);
        let empty = push_one(&grammar, &mut updated_at_in, token, source);
        assert!(
            !empty,
            "prefix {:?} unexpectedly became empty before the IN update",
            &source[..token.end]
        );
        if terminal == "IN" {
            assert!(
                !updated_at_in.run_egglog("(union $y $six)").unwrap(),
                "the prefix through IN should remain viable after the union"
            );
        }
    }
    assert!(
        !updated_at_in.intersection_is_empty(),
        "Body(Var(\"y\")) should match Body(Num(6)) after the union"
    );

    // The same completed prefix is initially outside the fixed target class.
    // Growing only the e-graph must resurrect it without replaying a lexeme.
    let mut late_update = LivePrefixMonitor::from_egglog(&grammar, Y_AND_SIX, "$root").unwrap();
    for (index, token) in tokens.iter().enumerate() {
        let empty = push_one(&grammar, &mut late_update, token, source);
        assert_eq!(
            empty,
            index + 1 == tokens.len(),
            "unexpected control result after prefix {:?}",
            &source[..token.end]
        );
    }
    let lexeme_updates = late_update.stats().lexeme_updates;
    assert!(late_update.intersection_is_empty());
    assert!(!late_update.run_egglog("(union $y $six)").unwrap());
    assert_eq!(late_update.stats().lexeme_updates, lexeme_updates);
    assert!(!late_update.intersection_is_empty());
}

#[test]
fn z_union_matches_the_body_but_a_trailing_plus_has_no_target_completion() {
    let grammar = declaration_grammar();
    let source = "let z = 3 * 2 in z +";
    let tokens = grammar.lex(source).unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, Z_AND_PRODUCT, "$root").unwrap();

    assert!(!monitor.intersection_is_empty());
    for token in &tokens {
        let terminal = grammar.terminal_name(token.kind);
        let empty = push_one(&grammar, &mut monitor, token, source);
        if terminal == "PLUS" {
            assert!(
                empty,
                "after `z +`, every syntactic completion has an Add root"
            );
        } else {
            assert!(
                !empty,
                "prefix {:?} should still have a target completion",
                &source[..token.end]
            );
        }

        if terminal == "IN" {
            assert!(!monitor.run_egglog("(union $z $product)").unwrap());
        }
        if terminal == "ID" && token.lexeme == "z" && token.start > source.find('=').unwrap() {
            assert!(
                !monitor.intersection_is_empty(),
                "the body z should match the product class after the IN update"
            );
        }
    }
    assert!(monitor.intersection_is_empty());
}

#[test]
fn update_before_or_after_the_final_lexeme_has_the_same_answer() {
    let grammar = declaration_grammar();
    let source = "let y = 6 in y";
    let tokens = grammar.lex(source).unwrap();

    let mut early = LivePrefixMonitor::from_egglog(&grammar, Y_AND_SIX, "$root").unwrap();
    for token in &tokens {
        let terminal = grammar.terminal_name(token.kind);
        let _ = push_one(&grammar, &mut early, token, source);
        if terminal == "IN" {
            let _ = early.run_egglog("(union $y $six)").unwrap();
        }
    }

    let mut late = LivePrefixMonitor::from_egglog(&grammar, Y_AND_SIX, "$root").unwrap();
    for token in &tokens {
        let _ = push_one(&grammar, &mut late, token, source);
    }
    assert!(late.intersection_is_empty());
    let _ = late.run_egglog("(union $y $six)").unwrap();

    assert_eq!(
        early.intersection_is_empty(),
        late.intersection_is_empty(),
        "the answer must depend on the final prefix/e-graph pair, not update order"
    );
    assert!(!early.intersection_is_empty());
}
