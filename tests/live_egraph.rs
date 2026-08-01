// Semantic cases adapted from ChopChop's `tests/test_egraph.py` at
// https://github.com/large-loris-models/chopchop/tree/681083a6fd921ac9cbaf984db628cf92eb019a3f
// (MIT). ChopChop asks after each character; this port pushes complete lexemes.

use prefixspace::{Grammar, LivePrefixMonitor};

#[test]
fn unchanged_prefix_is_resurrected_by_a_target_union() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD
        %%
        start: BAD { Bad() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    // Neither the empty prefix nor the complete BAD token can produce an AST
    // in the class of Good.
    assert!(monitor.intersection_is_empty());
    assert!(monitor.push_token_name("BAD", "bad").unwrap());

    // No token is pushed here. Growing the e-class alone must update the
    // answer for the already-consumed prefix.
    assert!(!monitor.run_egglog("(union $root (Bad))").unwrap());
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn interleaved_lexemes_and_child_unions_propagate_through_nested_constructors() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token Y Z
        %%
        start: pair { Outer(1) };
        pair: y z { Pair(1, 2) };
        y: Y { Y() };
        z: Z { Z() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast
          (Y) (Z) (ExpectedY) (ExpectedZ)
          (Pair Ast Ast)
          (Outer Ast))
        (let $expected-y (ExpectedY))
        (let $expected-z (ExpectedZ))
        (let $root (Outer (Pair $expected-y $expected-z)))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.intersection_is_empty());
    assert!(monitor.push_token_name("Y", "y").unwrap());

    // Matching only the first child cannot yet make the outer AST match.
    assert!(monitor.run_egglog("(union $expected-y (Y))").unwrap());
    assert!(monitor.push_token_name("Z", "z").unwrap());

    // This second leaf union must delta-propagate through Pair and then Outer.
    assert!(monitor.intersection_is_empty());
    assert!(!monitor.run_egglog("(union $expected-z (Z))").unwrap());
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn unrelated_egraph_changes_and_noop_runs_do_not_rebuild_the_intersection() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD
        %%
        start: BAD { Bad() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (JunkLeft) (JunkRight))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    let before = monitor.stats();

    assert!(
        monitor
            .run_egglog(
                r#"
                (let $junk-left (JunkLeft))
                (let $junk-right (JunkRight))
                (union $junk-left $junk-right)
                "#,
            )
            .unwrap()
    );
    let after_unrelated_merge = monitor.stats();
    assert_eq!(
        after_unrelated_merge.full_rebuilds, before.full_rebuilds,
        "an e-class delta must not trigger a full product rebuild"
    );
    assert_eq!(
        after_unrelated_merge.realizability_facts, before.realizability_facts,
        "unrelated constructors cannot add a productive product pair"
    );

    assert!(monitor.run_egglog("(run 1)").unwrap());
    let after_noop_run = monitor.stats();
    assert_eq!(
        after_noop_run.full_rebuilds,
        after_unrelated_merge.full_rebuilds
    );
    assert_eq!(
        after_noop_run.realizability_facts,
        after_unrelated_merge.realizability_facts
    );
}

#[test]
fn adding_and_running_a_constructor_rewrite_resurrects_a_complete_prefix() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token WRAP LEAF
        %%
        start: WRAP leaf { Wrap(2) };
        leaf: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Leaf) (Wrap Ast))
        (let $root (Leaf))
        (let $wrapped (Wrap (Leaf)))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.intersection_is_empty());
    assert!(monitor.push_token_name("WRAP", "wrap").unwrap());
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());

    // Defining a rewrite does not change an e-class until its ruleset runs.
    // The update contains both operations so the returned answer must reflect
    // the post-run e-graph, without reparsing the input.
    assert!(
        !monitor
            .run_egglog(
                r#"
                (rewrite (Wrap value) value)
                (run 1)
                "#,
            )
            .unwrap()
    );
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn selected_regex_terminal_uses_the_complete_lexeme_as_an_ast_child() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start id
        %token ID
        %%
        id: ID { Var(1) };
        "#,
        r#"
        %%
        [a-z]+    'ID'
        [ \t\r\n]+ ;
        "#,
    )
    .unwrap();
    let egraph = r#"
        (datatype Ast (Var String))
        (let $root (Var "x"))
    "#;

    // At epsilon, `x` is already a regex-valid completion. Supplying that
    // complete lexeme preserves non-emptiness.
    let mut accepted = LivePrefixMonitor::from_egglog(&grammar, egraph, "$root").unwrap();
    assert!(!accepted.intersection_is_empty());
    assert!(!accepted.push_token_name("ID", "x").unwrap());

    // Token kind alone is insufficient: the same ID token with another
    // lexeme denotes Var("y"), which is initially outside the target class.
    let mut resurrected = LivePrefixMonitor::from_egglog(&grammar, egraph, "$root").unwrap();
    assert!(resurrected.push_token_name("ID", "y").unwrap());
    assert!(resurrected.intersection_is_empty());
    assert!(!resurrected.run_egglog("(union $root (Var \"y\"))").unwrap());
    assert!(!resurrected.intersection_is_empty());
}
