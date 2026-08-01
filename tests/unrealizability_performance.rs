use prefixspace::{
    DEFAULT_UNREALIZABILITY_WORK_LIMIT, Grammar, LiveMonitorStats, LivePrefixMonitor,
};

fn repeated_statement_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start stream
        %token X SEMI END
        %%
        stream: item stream { $1 }
              | END         { Leaf() }
              ;
        item: X SEMI { Leaf() };
        "#,
    )
    .unwrap()
}

fn complete_free_stream(statement_count: usize) -> LiveMonitorStats {
    let grammar = repeated_statement_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Leaf) (Other))
        (free Type TypeDisjoint)
        (let $wanted (Leaf))
        "#,
        "$wanted",
        "TypeDisjoint",
    )
    .unwrap();

    for _ in 0..statement_count {
        assert!(!monitor.push_token_name("X", "x").unwrap());
        assert!(!monitor.push_token_name("SEMI", ";").unwrap());
        assert_eq!(monitor.realizability(), Some(true));
    }
    monitor.stats()
}

fn focused_managed_stream(statement_count: usize) -> LiveMonitorStats {
    let grammar = repeated_statement_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Type (Leaf) (Other))
        (let $wanted (Other))
        "#,
        "$wanted",
    )
    .unwrap();
    monitor
        .add_managed_rewrites("(rewrite (Leaf) (Other))")
        .unwrap();

    for _ in 0..statement_count {
        assert!(!monitor.push_token_name("X", "x").unwrap());
        assert!(!monitor.push_token_name("SEMI", ";").unwrap());
        assert_eq!(monitor.realizability(), Some(true));
    }
    monitor.stats()
}

#[test]
fn complete_free_ll1_stream_keeps_incremental_overhead_linear() {
    let small_count = 64;
    let large_count = 512;
    let baseline = complete_free_stream(0);
    let small = complete_free_stream(small_count);
    let large = complete_free_stream(large_count);

    let small_facts = small.prefix_space_facts - baseline.prefix_space_facts;
    let large_facts = large.prefix_space_facts - baseline.prefix_space_facts;
    let small_matches = small.total_delta_rule_matches - baseline.total_delta_rule_matches;
    let large_matches = large.total_delta_rule_matches - baseline.total_delta_rule_matches;
    let scale = large_count / small_count + 1;

    assert!(large_facts <= small_facts * scale, "{small:?} {large:?}");
    assert!(
        large_matches <= small_matches * scale + 64,
        "{small:?} {large:?}"
    );
    // Repeated Leaf() terms share one private egglog binding.
    assert_eq!(large.fixed_tree_bindings, 1, "{large:?}");
    // Complete free structure uses the exact cached zipper/e-class product;
    // it never invokes the bounded fallback enumerator.
    assert_eq!(large.total_prefix_output_work, 0, "{large:?}");
    assert_eq!(large.full_rebuilds, 0);
}

#[test]
fn focused_managed_ll1_stream_keeps_prefix_work_linear() {
    let small_count = 64;
    let large_count = 512;
    let baseline = focused_managed_stream(0);
    let small = focused_managed_stream(small_count);
    let large = focused_managed_stream(large_count);

    let small_work = small.total_prefix_output_work - baseline.total_prefix_output_work;
    let large_work = large.total_prefix_output_work - baseline.total_prefix_output_work;
    let scale = large_count / small_count + 1;
    assert!(large_work <= small_work * scale, "{small:?} {large:?}");
    assert_eq!(large.fixed_tree_bindings, 1, "{large:?}");
    assert_eq!(large.full_rebuilds, 0);
}

#[test]
fn partial_disjointness_has_a_hard_per_update_work_bound() {
    let grammar = repeated_statement_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Leaf) (Other))
        (relation TypeDisjoint (Type Type))
        (TypeDisjoint (Other) (Leaf))
        (let $wanted (Leaf))
        "#,
        "$wanted",
        "TypeDisjoint",
    )
    .unwrap();

    let statement_count = if cfg!(debug_assertions) { 256 } else { 2_500 };
    for _ in 0..statement_count {
        monitor.push_token_name("X", "x").unwrap();
        assert!(monitor.stats().last_prefix_output_work <= DEFAULT_UNREALIZABILITY_WORK_LIMIT);
        monitor.push_token_name("SEMI", ";").unwrap();
        assert!(monitor.stats().last_prefix_output_work <= DEFAULT_UNREALIZABILITY_WORK_LIMIT);
    }
    assert_eq!(monitor.stats().full_rebuilds, 0);
}

fn monitor_with_unfocused_free_terms(term_count: usize) -> LivePrefixMonitor {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token WANTED
        %%
        start: WANTED { Wanted() };
        "#,
    )
    .unwrap();
    let mut program = String::from(
        r#"
        (datatype Type (Wanted) (Junk i64))
        (free Type TypeDisjoint)
        (let $wanted (Wanted))
        "#,
    );
    for index in 0..term_count {
        program.push_str(&format!("(let $unfocused_{index} (Junk {index}))\n"));
    }
    LivePrefixMonitor::from_egglog_with_disjointness(&grammar, &program, "$wanted", "TypeDisjoint")
        .unwrap()
}

#[test]
fn free_reasoning_does_not_cross_product_a_large_unfocused_egraph() {
    let small = monitor_with_unfocused_free_terms(16);
    let large = monitor_with_unfocused_free_terms(if cfg!(debug_assertions) {
        2_000
    } else {
        10_000
    });

    assert_eq!(small.realizability(), Some(true));
    assert_eq!(large.realizability(), Some(true));
    assert!(
        large.stats().total_delta_rule_matches <= small.stats().total_delta_rule_matches + 8,
        "small={:?} large={:?}",
        small.stats(),
        large.stats()
    );
}
