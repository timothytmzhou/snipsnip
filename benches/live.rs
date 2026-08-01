use std::{hint::black_box, time::Duration};

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use prefixspace::{Grammar, LivePrefixMonitor, PwzRecognizer};

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

// This exercises the complete value-producing PwZ forest and its local fact
// indexes, but has no target-reachable constructor row with which those facts
// can join. It is the closest public-API baseline for the semantic forest;
// `ForestPwz` itself is intentionally crate-private.
const UNMATCHED_EGRAPH: &str = r#"
    (datatype Ast (List Ast) (Cons Ast) (Nil) (Junk))
    (let $root (Junk))
"#;

fn live_streaming(c: &mut Criterion) {
    let grammar = list_grammar();
    let terminal = grammar.terminal_by_name("X").unwrap();
    let mut group = c.benchmark_group("live_ll1_stream");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(5));

    // The geometric series makes accidental superlinear growth visible in
    // Criterion's line chart without making the benchmark prohibitively long.
    // Keep the batched input behind `&mut`: consuming it with `iter_batched`
    // charges destruction of the accumulated forest/e-graph to the sample.
    for count in [1_000usize, 10_000, 100_000] {
        group.throughput(Throughput::Elements(count as u64));
        group.bench_with_input(
            BenchmarkId::new("vanilla_pwz", count),
            &count,
            |b, &count| {
                b.iter_batched_ref(
                    || PwzRecognizer::compile(&grammar).unwrap(),
                    |parser| {
                        for _ in 0..count {
                            black_box(parser.push(terminal).unwrap());
                        }
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        group.bench_with_input(
            BenchmarkId::new("forest_and_indexes", count),
            &count,
            |b, &count| {
                b.iter_batched_ref(
                    || LivePrefixMonitor::from_egglog(&grammar, UNMATCHED_EGRAPH, "$root").unwrap(),
                    |monitor| {
                        for _ in 0..count {
                            black_box(monitor.push_lexeme(terminal, "x").unwrap());
                        }
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("live", count), &count, |b, &count| {
            b.iter_batched_ref(
                || LivePrefixMonitor::from_egglog(&grammar, LIST_EGRAPH, "$root").unwrap(),
                |monitor| {
                    for _ in 0..count {
                        black_box(monitor.push_lexeme(terminal, "x").unwrap());
                    }
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
}

fn live_deltas(c: &mut Criterion) {
    let grammar = list_grammar();
    let terminal = grammar.terminal_by_name("X").unwrap();
    let setup = |count| {
        let mut monitor = LivePrefixMonitor::from_egglog(&grammar, LIST_EGRAPH, "$root").unwrap();
        for _ in 0..count {
            assert!(!monitor.push_lexeme(terminal, "x").unwrap());
        }
        monitor
    };
    let mut group = c.benchmark_group("live_egraph_delta");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(5));
    for count in [1_000usize, 10_000, 100_000] {
        group.throughput(Throughput::Elements(1));
        group.bench_with_input(BenchmarkId::new("no_op_run", count), &count, |b, &count| {
            b.iter_batched_ref(
                || setup(count),
                |monitor| black_box(monitor.run_egglog("(run 1)").unwrap()),
                BatchSize::PerIteration,
            )
        });
    }
    group.bench_with_input(
        BenchmarkId::new("unrelated_union", 100_000),
        &100_000usize,
        |b, &count| {
            b.iter_batched_ref(
                || setup(count),
                |monitor| {
                    black_box(
                        monitor
                            .run_egglog("(union $junk-left $junk-right)")
                            .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            )
        },
    );

    let relevant_grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD
        %%
        start: BAD { Bad() };
        "#,
    )
    .unwrap();
    let bad = relevant_grammar.terminal_by_name("BAD").unwrap();
    group.bench_function("relevant_union", |b| {
        b.iter_batched_ref(
            || {
                let mut monitor = LivePrefixMonitor::from_egglog(
                    &relevant_grammar,
                    r#"
                    (datatype Ast (Good) (Bad))
                    (let $root (Good))
                    (let $bad (Bad))
                    "#,
                    "$root",
                )
                .unwrap();
                assert!(monitor.push_lexeme(bad, "bad").unwrap());
                monitor
            },
            |monitor| black_box(monitor.run_egglog("(union $root $bad)").unwrap()),
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

fn managed_saturation(c: &mut Criterion) {
    let leaf_grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD
        %%
        start: BAD { Bad() };
        "#,
    )
    .unwrap();
    let bad = leaf_grammar.terminal_by_name("BAD").unwrap();
    let setup_leaf = || {
        let mut monitor = LivePrefixMonitor::from_egglog(
            &leaf_grammar,
            "(datatype Ast (Good) (Bad)) (let $root (Good))",
            "$root",
        )
        .unwrap();
        assert!(monitor.push_lexeme(bad, "bad").unwrap());
        monitor
    };

    let mut group = c.benchmark_group("managed_saturation");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(5));
    group.bench_function("target_basin_birewrite", |b| {
        b.iter_batched_ref(
            setup_leaf,
            |monitor| {
                black_box(
                    monitor
                        .add_managed_rewrites("(birewrite (Bad) (Good))")
                        .unwrap(),
                )
            },
            BatchSize::PerIteration,
        )
    });

    // The unrelated rows deliberately dwarf the target basin. A pure
    // birewrite should install and close without scanning these matches.
    let mut unrelated_program =
        String::from("(datatype Ast (Good) (Bad) (Junk i64) (Other i64))\n");
    unrelated_program.push_str("(let $root (Good))\n");
    for value in 0..1_024 {
        unrelated_program.push_str(&format!("(let $junk_{value} (Junk {value}))\n"));
    }
    group.bench_function("target_basin_skips_1024_unrelated_rows", |b| {
        b.iter_batched_ref(
            || {
                let mut monitor =
                    LivePrefixMonitor::from_egglog(&leaf_grammar, &unrelated_program, "$root")
                        .unwrap();
                assert!(monitor.push_lexeme(bad, "bad").unwrap());
                monitor
            },
            |monitor| {
                black_box(
                    monitor
                        .add_managed_rewrites("(birewrite (Junk x) (Other x))")
                        .unwrap(),
                )
            },
            BatchSize::PerIteration,
        )
    });

    let common_ancestor_grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let leaf = common_ancestor_grammar.terminal_by_name("LEAF").unwrap();
    group.bench_function("directed_unrelated_lhs_is_skipped", |b| {
        b.iter_batched_ref(
            || {
                let mut monitor = LivePrefixMonitor::from_egglog(
                    &common_ancestor_grammar,
                    r#"
                    (datatype Ast (Good) (Leaf) (U) (Middle))
                    (let $root (Good))
                    (let $source (U))
                    "#,
                    "$root",
                )
                .unwrap();
                assert!(monitor.push_lexeme(leaf, "leaf").unwrap());
                monitor
            },
            |monitor| {
                black_box(
                    monitor
                        .add_managed_rewrites(
                            "(rewrite (U) (Middle))\n\
                             (rewrite (Middle) (Good))\n\
                             (rewrite (Middle) (Leaf))",
                        )
                        .unwrap(),
                )
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

criterion_group!(benches, live_streaming, live_deltas, managed_saturation);
criterion_main!(benches);
