use std::{hint::black_box, time::Duration};

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use prefixspace::{
    Grammar, Monitor,
    paper_pwz::{Grammar as PwzGrammar, Pwz, Token as PwzToken},
};

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
    let pwz_grammar: PwzGrammar<()> = (&grammar).try_into().unwrap();
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
                    || Pwz::new(pwz_grammar.clone()),
                    |parser| {
                        for _ in 0..count {
                            parser.derive(PwzToken {
                                terminal: terminal.index() as u32,
                                payload: (),
                            });
                            black_box(parser.zippers());
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
                    || Monitor::new(&grammar, UNMATCHED_EGRAPH, "$root").unwrap(),
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
                || Monitor::new(&grammar, LIST_EGRAPH, "$root").unwrap(),
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
        let mut monitor = Monitor::new(&grammar, LIST_EGRAPH, "$root").unwrap();
        for _ in 0..count {
            assert_eq!(monitor.push_lexeme(terminal, "x").unwrap(), Some(true));
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
                |monitor| black_box(monitor.run_egglog("(union $nil $nil)").unwrap()),
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
                let mut monitor = Monitor::new(
                    &relevant_grammar,
                    r#"
                    (datatype Ast (Good) (Bad))
                    (let $root (Good))
                    (let $bad (Bad))
                    "#,
                    "$root",
                )
                .unwrap();
                assert_ne!(monitor.push_lexeme(bad, "bad").unwrap(), Some(true));
                monitor
            },
            |monitor| black_box(monitor.run_egglog("(union $root $bad)").unwrap()),
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

criterion_group!(benches, live_streaming, live_deltas);
criterion_main!(benches);
