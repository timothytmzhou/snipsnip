use prefixspace::{Grammar, LiveMonitorStats, LivePrefixMonitor};

fn list_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: items { List(1) };
        items: X items { Cons(2) }
             | { Nil() }
             ;
        "#,
    )
    .unwrap()
}

const LIST_EGRAPH: &str = r#"
    (datatype Ast (List Ast) (Cons Ast) (Nil) (JunkLeft) (JunkRight))
    (let $nil (Nil))
    (union $nil (Cons $nil))
    (let $root (List $nil))
    (let $junk-left (JunkLeft))
    (let $junk-right (JunkRight))
"#;

fn stream_list(count: usize) -> LiveMonitorStats {
    let grammar = list_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, LIST_EGRAPH, "$root").unwrap();
    assert!(!monitor.intersection_is_empty());
    for _ in 0..count {
        assert!(!monitor.push_token_name("X", "x").unwrap());
    }
    monitor.stats()
}

#[test]
fn ll1_live_prefix_forest_and_realizability_work_grow_linearly() {
    // Keep the debug suite quick; optimized test runs exercise 100K lexemes.
    // Structural ratios, rather than noisy wall-clock assertions, detect
    // accidental quadratic history growth.
    const SMALL: usize = if cfg!(debug_assertions) { 16 } else { 10_000 };
    const LARGE: usize = if cfg!(debug_assertions) {
        SMALL * 8
    } else {
        100_000
    };
    const SCALE_WITH_FIXED_ALLOWANCE: usize = LARGE / SMALL + 1;

    let baseline = stream_list(0);
    let small = stream_list(SMALL);
    let large = stream_list(LARGE);

    assert_eq!(large.lexeme_updates, LARGE);
    assert_eq!(large.pwz.derivatives, LARGE);
    assert_eq!(large.full_rebuilds, 0);

    let small_states = small.prefix_space_states - baseline.prefix_space_states;
    let large_states = large.prefix_space_states - baseline.prefix_space_states;
    let small_prefix_facts = small.prefix_space_facts - baseline.prefix_space_facts;
    let large_prefix_facts = large.prefix_space_facts - baseline.prefix_space_facts;
    let small_realizability_facts = small.realizability_facts - baseline.realizability_facts;
    let large_realizability_facts = large.realizability_facts - baseline.realizability_facts;
    let small_matches = small.total_delta_rule_matches - baseline.total_delta_rule_matches;
    let large_matches = large.total_delta_rule_matches - baseline.total_delta_rule_matches;
    let small_probes = small.total_delta_join_probes - baseline.total_delta_join_probes;
    let large_probes = large.total_delta_join_probes - baseline.total_delta_join_probes;

    // Add one small-run allowance for fixed initialization effects while still
    // rejecting quadratic histories.
    assert!(
        large_states <= small_states * SCALE_WITH_FIXED_ALLOWANCE,
        "{baseline:?} {small:?} {large:?}"
    );
    assert!(
        large_prefix_facts <= small_prefix_facts * SCALE_WITH_FIXED_ALLOWANCE,
        "{baseline:?} {small:?} {large:?}"
    );
    assert!(
        large_realizability_facts <= small_realizability_facts * SCALE_WITH_FIXED_ALLOWANCE,
        "{baseline:?} {small:?} {large:?}"
    );
    assert!(
        large_matches <= small_matches * SCALE_WITH_FIXED_ALLOWANCE,
        "{baseline:?} {small:?} {large:?}"
    );
    assert!(
        large_probes <= small_probes * SCALE_WITH_FIXED_ALLOWANCE,
        "{baseline:?} {small:?} {large:?}"
    );
    assert!(large_states <= LARGE * 8 + 64, "{large:?}");
    assert!(large_prefix_facts <= LARGE * 10 + 64, "{large:?}");
    assert!(large_realizability_facts <= LARGE * 7 + 64, "{large:?}");
    assert!(large_matches <= LARGE * 11 + 64, "{large:?}");
    assert!(large_probes <= LARGE * 4 + 64, "{large:?}");
    assert!(large.pwz.events <= LARGE * 24 + 64, "{large:?}");
    assert!(large.pwz.memo_records <= LARGE * 8 + 64, "{large:?}");
    assert!(large.last_delta_rule_matches <= 8, "{large:?}");
    assert!(large.last_delta_join_probes <= 4, "{large:?}");
}

#[test]
fn no_op_and_target_unreachable_egraph_deltas_add_no_realizability_facts() {
    let grammar = list_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, LIST_EGRAPH, "$root").unwrap();
    // The 100K structural stream above is the retained-memory stress case.
    // Keep this concurrently runnable update test smaller; Criterion exercises
    // the same no-op update after a 100K history.
    let history = if cfg!(debug_assertions) { 32 } else { 10_000 };
    for _ in 0..history {
        assert!(!monitor.push_token_name("X", "x").unwrap());
    }
    let before = monitor.stats();

    assert!(
        !monitor
            .run_egglog("(union $junk-left $junk-right)")
            .unwrap()
    );
    let unrelated = monitor.stats();
    assert_eq!(unrelated.full_rebuilds, 0);
    assert_eq!(unrelated.realizability_facts, before.realizability_facts);
    assert_eq!(
        unrelated.last_delta_rule_matches, 0,
        "{before:?} {unrelated:?}"
    );

    assert!(!monitor.run_egglog("(run 1)").unwrap());
    let no_op = monitor.stats();
    assert_eq!(no_op.full_rebuilds, 0);
    assert_eq!(no_op.realizability_facts, unrelated.realizability_facts);
    assert_eq!(no_op.last_delta_rule_matches, 0, "{unrelated:?} {no_op:?}");
}

#[test]
fn one_relevant_union_adds_only_a_constant_number_of_realizability_facts() {
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
        (let $bad (Bad))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    let before = monitor.stats();

    assert!(!monitor.run_egglog("(union $root $bad)").unwrap());
    let after = monitor.stats();
    assert_eq!(after.full_rebuilds, 0);
    assert!(after.realizability_facts > before.realizability_facts);
    assert!(
        after.realizability_facts <= before.realizability_facts + 8,
        "{before:?} {after:?}"
    );
    assert!(after.last_delta_rule_matches <= 8, "{before:?} {after:?}");
}

#[test]
fn late_unmatched_reachable_enode_does_not_scan_prefix_history() {
    fn after_union(count: usize) -> LiveMonitorStats {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token X
            %%
            start: items { Root(1) };
            items: atom items { Pair(1, 2) }
                 | { Good() }
                 ;
            atom: X { Good() };
            "#,
        )
        .unwrap();
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            r#"
            (datatype Ast (Root Ast) (Pair Ast Ast) (Good) (Bad))
            (let $root (Root (Good)))
            (let $candidate (Root (Pair (Bad) (Good))))
            "#,
            "$root",
        )
        .unwrap();
        for _ in 0..count {
            assert!(monitor.push_token_name("X", "x").unwrap());
        }
        assert!(monitor.run_egglog("(union $root $candidate)").unwrap());
        monitor.stats()
    }

    let small = after_union(16);
    let large = after_union(1_024);
    assert_eq!(small.full_rebuilds, 0);
    assert_eq!(large.full_rebuilds, 0);
    assert!(
        large.last_delta_join_probes <= small.last_delta_join_probes + 8,
        "late e-node work must be independent of irrelevant prefix history: {small:?} {large:?}"
    );
}

#[test]
fn distinct_ignored_lexemes_do_not_allocate_distinct_semantic_spaces() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X END
        %%
        start: items END { Root(1) };
        items: X items { $2 }
             | { Nil() }
             ;
        "#,
    )
    .unwrap();

    fn stream(grammar: &Grammar, distinct: bool) -> LiveMonitorStats {
        let mut monitor = LivePrefixMonitor::from_egglog(
            grammar,
            "(datatype Ast (Root Ast) (Nil)) (let $root (Root (Nil)))",
            "$root",
        )
        .unwrap();
        for index in 0..128 {
            let lexeme = if distinct {
                format!("ignored-{index:04}-{}", "x".repeat(64))
            } else {
                "x".to_owned()
            };
            assert!(!monitor.push_token_name("X", &lexeme).unwrap());
        }
        monitor.stats()
    }

    let repeated = stream(&grammar, false);
    let distinct = stream(&grammar, true);
    assert_eq!(distinct.prefix_space_states, repeated.prefix_space_states);
    assert_eq!(distinct.prefix_space_facts, repeated.prefix_space_facts);
    assert_eq!(distinct.realizability_facts, repeated.realizability_facts);
}

#[test]
fn selected_lexemes_after_syntactic_death_do_not_grow_live_state() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID
        %%
        start: ID { Var(1) };
        "#,
        "%%\n[a-z0-9]+ 'ID'\n",
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Var String)) (let $root (Var \"first\"))",
        "$root",
    )
    .unwrap();
    assert!(!monitor.push_token_name("ID", "first").unwrap());
    assert!(monitor.push_token_name("ID", "second").unwrap());
    let dead = monitor.stats();

    for index in 0..128 {
        assert!(
            monitor
                .push_token_name("ID", &format!("dead{index}"))
                .unwrap()
        );
    }
    let after = monitor.stats();
    assert_eq!(after.prefix_space_states, dead.prefix_space_states);
    assert_eq!(after.prefix_space_facts, dead.prefix_space_facts);
    assert_eq!(after.realizability_facts, dead.realizability_facts);
    assert_eq!(after.total_delta_join_probes, dead.total_delta_join_probes);
}
