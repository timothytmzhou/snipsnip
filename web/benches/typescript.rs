use std::{hint::black_box, time::Duration};

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use prefixspace::{Grammar, Monitor};
use prefixspace_web::{
    DEFAULT_EGGLOG_PROGRAM, TYPESCRIPT_LEX, TYPESCRIPT_YACC, TypeScriptAnalyzer,
};

const NESTING_DEPTH: usize = 4_096;

fn nested_number_calls(depth: usize) -> String {
    let mut source = String::from("let answer: number = ");
    for _ in 0..depth {
        source.push_str("Number(");
    }
    source.push('0');
    for _ in 0..depth {
        source.push(')');
    }
    source.push(';');
    source
}

fn typescript(c: &mut Criterion) {
    let grammar = Grammar::from_yacc_lex(TYPESCRIPT_YACC, TYPESCRIPT_LEX).unwrap();

    let mut construction = c.benchmark_group("typescript_construction");
    construction.sample_size(10);
    construction.warm_up_time(Duration::from_secs(1));
    construction.measurement_time(Duration::from_secs(5));
    construction.bench_function("monitor", |b| {
        b.iter(|| black_box(Monitor::new(&grammar, DEFAULT_EGGLOG_PROGRAM, "$required")).unwrap())
    });
    construction.bench_function("analyzer", |b| {
        b.iter(|| black_box(TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM)).unwrap())
    });
    construction.finish();

    let source = nested_number_calls(NESTING_DEPTH);
    let tokens = grammar.lex(&source).unwrap();
    let mut updates = c.benchmark_group("typescript_nested_number_calls");
    updates.sample_size(10);
    updates.warm_up_time(Duration::from_secs(1));
    updates.measurement_time(Duration::from_secs(5));
    updates.throughput(Throughput::Elements(tokens.len() as u64));
    updates.bench_function(NESTING_DEPTH.to_string(), |b| {
        b.iter_batched_ref(
            || Monitor::new(&grammar, DEFAULT_EGGLOG_PROGRAM, "$required").unwrap(),
            |monitor| {
                for token in &tokens {
                    black_box(monitor.push_token(token).unwrap());
                }
            },
            BatchSize::PerIteration,
        )
    });
    updates.finish();
}

criterion_group!(benches, typescript);
criterion_main!(benches);
