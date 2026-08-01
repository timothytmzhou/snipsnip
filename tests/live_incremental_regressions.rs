use prefixspace::{Grammar, LiveMonitorError, LivePrefixMonitor};

#[test]
fn future_i64_token_accepts_a_noncanonical_decimal_spelling() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token PADDED
        %%
        start: PADDED { Num(1) };
        "#,
        r#"
        %%
        0[0-9]+ 'PADDED'
        "#,
    )
    .unwrap();
    let egraph = r#"
        (datatype Ast (Num i64))
        (let $root (Num 1))
    "#;

    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, egraph, "$root").unwrap();

    // `01` is both a complete PADDED lexeme and Rust's decimal spelling of
    // the i64 value 1, so it is a valid completion of epsilon.
    assert!(
        !monitor.intersection_is_empty(),
        "the epsilon prefix has completion `01` producing Num(1)"
    );
    assert!(!monitor.push_token_name("PADDED", "01").unwrap());
}

#[test]
fn future_i64_spelling_search_handles_signs_and_long_zero_runs_exactly() {
    fn check(regex: &str, value: i64, lexeme: &str) {
        let grammar = Grammar::from_yacc_lex(
            r#"
            %start start
            %token NUMBER
            %%
            start: NUMBER { Num(1) };
            "#,
            &format!("%%\n{regex} 'NUMBER'\n"),
        )
        .unwrap();
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            &format!(
                r#"
                (datatype Ast (Num i64))
                (let $root (Num {value}))
                "#
            ),
            "$root",
        )
        .unwrap();

        assert!(
            !monitor.intersection_is_empty(),
            "{lexeme:?} must be discovered as a completion"
        );
        assert!(!monitor.push_token_name("NUMBER", lexeme).unwrap());
    }

    check(r"\+0+[0-9]+", 7, "+0007");
    check(r"-0+[0-9]+", -7, "-0007");
    check(r"-0+", 0, "-000");
    check(r"0{128}1", 1, &format!("{}1", "0".repeat(128)));
}

#[test]
fn merging_the_target_with_a_new_nested_tree_reaches_all_of_its_children() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID
        %%
        start: item { Outer(1) };
        item: ID { Var(1) };
        "#,
        r#"
        %%
        [a-z]+ 'ID'
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Old) (Var String) (Outer Ast))
        (let $root (Old))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("ID", "y").unwrap());
    let lexeme_updates = monitor.stats().lexeme_updates;

    // The newly merged side was previously unreachable from the target.  Its
    // Outer, Var, and String rows all have to arrive through the e-graph delta
    // without replaying the already consumed token.
    assert!(
        !monitor
            .run_egglog("(union $root (Outer (Var \"y\")))")
            .unwrap()
    );
    assert_eq!(monitor.stats().lexeme_updates, lexeme_updates);
}

#[test]
fn a_rewrite_inside_a_reachable_child_class_resurrects_the_prefix() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token NEW
        %%
        start: leaf { Outer(1) };
        leaf: NEW { New() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Old) (New) (Outer Ast))
        (let $root (Outer (Old)))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("NEW", "new").unwrap());

    assert!(
        !monitor
            .run_egglog(
                r#"
                (rewrite (Old) (New))
                (run 1)
                "#,
            )
            .unwrap()
    );
}

#[test]
fn rewrite_created_recursive_target_class_updates_existing_and_future_prefixes() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X END
        %%
        start: X start { Step(2) }
             | END { Base() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Base) (Step Ast))
        (let $root (Base))
        "#,
        "$root",
    )
    .unwrap();

    assert!(!monitor.intersection_is_empty());
    assert!(monitor.push_token_name("X", "x").unwrap());
    assert!(
        !monitor
            .run_egglog(
                r#"
                (rewrite (Base) (Step (Base)))
                (run 1)
                "#,
            )
            .unwrap()
    );
    for _ in 0..4 {
        assert!(!monitor.push_token_name("X", "x").unwrap());
    }
}

#[test]
fn nonmonotone_updates_cannot_bypass_the_guard_with_whitespace_or_rewrite_flags() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    for initial_program in [
        r#"
        (datatype Ast (Leaf))
        (let $root (Leaf))
        (rule ((= x (Leaf))) ((delete (Leaf))))
        "#,
        r#"
        (datatype Ast (Leaf))
        (let $root (Leaf))
        (rewrite (Leaf) (Leaf) :subsume)
        "#,
    ] {
        let result = LivePrefixMonitor::from_egglog(&grammar, initial_program, "$root");
        assert!(
            matches!(result, Err(LiveMonitorError::NonMonotoneUpdate(_))),
            "initial program could install a latent nonmonotone rule"
        );
    }
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Leaf))
        (let $root (Leaf))
        "#,
        "$root",
    )
    .unwrap();

    for update in [
        "(\n  delete (Leaf))",
        "(rewrite (Leaf) (Leaf) :subsume)",
        "(rule ((= x (Leaf))) ((set (Leaf) x)))",
    ] {
        let result = monitor.run_egglog(update);
        assert!(
            matches!(result, Err(LiveMonitorError::NonMonotoneUpdate(_))),
            "{update:?}: {result:?}"
        );
    }

    // Parsing the update must not reject words found only in data or comments.
    assert!(
        !monitor
            .run_egglog("; (delete (Leaf))\n(let $message \"(pop) :subsume\")")
            .unwrap()
    );
}

#[test]
fn late_enode_matches_every_selected_and_ignored_zipper_hole() {
    let selected = Grammar::from_yacc(
        r#"
        %start start
        %token A B C
        %%
        start: a b c { Tri(1, 2, 3) };
        a: A { ALeaf() };
        b: B { BLeaf() };
        c: C { CLeaf() };
        "#,
    )
    .unwrap();
    let ignored = Grammar::from_yacc(
        r#"
        %start start
        %token A B C
        %%
        start: a B c { Pair(1, 3) };
        a: A { ALeaf() };
        c: C { CLeaf() };
        "#,
    )
    .unwrap();
    let program = r#"
        (datatype Ast
          (Old) (ALeaf) (BLeaf) (CLeaf)
          (Tri Ast Ast Ast) (Pair Ast Ast))
        (let $root (Old))
    "#;
    let stream = [("A", "a"), ("B", "b"), ("C", "c")];

    for consumed in 0..=stream.len() {
        let mut monitor = LivePrefixMonitor::from_egglog(&selected, program, "$root").unwrap();
        for &(terminal, lexeme) in &stream[..consumed] {
            assert!(monitor.push_token_name(terminal, lexeme).unwrap());
        }
        assert!(monitor.intersection_is_empty());
        assert!(
            !monitor
                .run_egglog("(union $root (Tri (ALeaf) (BLeaf) (CLeaf)))")
                .unwrap(),
            "selected hole after {consumed} token(s)"
        );
    }

    for consumed in 0..=stream.len() {
        let mut monitor = LivePrefixMonitor::from_egglog(&ignored, program, "$root").unwrap();
        for &(terminal, lexeme) in &stream[..consumed] {
            assert!(monitor.push_token_name(terminal, lexeme).unwrap());
        }
        assert!(monitor.intersection_is_empty());
        assert!(
            !monitor
                .run_egglog("(union $root (Pair (ALeaf) (CLeaf)))")
                .unwrap(),
            "selected/ignored hole after {consumed} token(s)"
        );
    }
}

#[test]
fn private_matcher_namespace_cannot_be_collided_with_or_forged() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD
        %%
        start: atom { Wrap(1) };
        atom: GOOD { Good() }
            | BAD { Bad() }
            ;
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Wrap Ast) (Good) (Bad))
        ; Force prefix 0 to be skipped, including for generated ruleset and
        ; capture names which are not ordinary egraph functions yet.
        (ruleset __prefixspace_live_0_rules)
        (let $root (Wrap (Good)))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());

    // The prefix in ordinary String data and comments is not a capability
    // reference and must remain usable.
    assert!(
        monitor
            .run_egglog(
                r#"
            ; __prefixspace_live_1_capture_constructor_0
            (let $message "__prefixspace_live_1_capture_constructor_0")
            "#,
            )
            .unwrap()
    );

    // Prefix 1 is now the monitor's private namespace. A user cannot inject a
    // fake constructor row into its capture buffer.
    let result = monitor.run_egglog("(__prefixspace_live_1_capture_constructor_0 $root (Bad))");
    assert!(matches!(
        result,
        Err(LiveMonitorError::ReservedNamespace(_))
    ));
    assert!(monitor.intersection_is_empty());
}

#[test]
fn partial_egglog_failure_is_synchronized_before_the_error_is_returned() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD
        %%
        start: GOOD { Good() }
             | BAD { Bad() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        (let $bad (Bad))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());

    // egglog executes a batch sequentially, so the union persists even though
    // the following command fails. The cached answer must already reflect it.
    assert!(
        monitor
            .run_egglog("(union $root $bad) (let $oops (missing-function))")
            .is_err()
    );
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn foreign_out_of_range_terminal_ids_return_an_error_instead_of_panicking() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token ONLY
        %%
        start: ONLY { Leaf() };
        "#,
    )
    .unwrap();
    let other = Grammar::from_yacc(
        r#"
        %start start
        %token FIRST SECOND
        %%
        start: FIRST { Leaf() }
             | SECOND { Leaf() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Leaf)) (let $root (Leaf))",
        "$root",
    )
    .unwrap();
    let foreign = other.terminal_by_name("SECOND").unwrap();
    assert!(matches!(
        monitor.push_lexeme(foreign, "second"),
        Err(LiveMonitorError::InvalidTerminalId(_))
    ));
}

#[test]
fn grammar_actions_require_ranked_datatype_constructors() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { Table() };
        "#,
    )
    .unwrap();
    let result = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Root))
        (function Table () Ast :merge old)
        (let $root (Root))
        "#,
        "$root",
    );
    assert!(
        matches!(
            &result,
            Err(LiveMonitorError::NonConstructorAction(name)) if name == "Table"
        ),
        "{:?}",
        result.as_ref().err()
    );
}
