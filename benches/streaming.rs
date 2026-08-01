use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use prefixspace::{Grammar, PrefixMonitor, PwzRecognizer, RegularTreeGrammar};

fn benchmark(c: &mut Criterion) {
    let grammar = Grammar::from_yacc(
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
    .unwrap();
    let x = grammar.terminal_by_name("X").unwrap();
    let (automaton, target) = RegularTreeGrammar::from_egglog(
        r#"
        (datatype Ast (List Ast) (Cons Ast) (Nil))
        (let $nil (Nil))
        (union $nil (Cons $nil))
        (let $root (List $nil))
        "#,
        "$root",
    )
    .unwrap();

    let mut group = c.benchmark_group("ll1_stream");
    for count in [1_000usize, 10_000, 100_000] {
        group.throughput(Throughput::Elements(count as u64));
        group.bench_function(format!("vanilla/{count}"), |b| {
            b.iter(|| {
                let mut parser = PwzRecognizer::compile(&grammar).unwrap();
                for _ in 0..count {
                    assert!(parser.push(x).unwrap());
                }
            })
        });
        group.bench_function(format!("monitored/{count}"), |b| {
            b.iter(|| {
                let mut stream = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
                for _ in 0..count {
                    assert!(!stream.push_terminal(x).unwrap());
                }
            })
        });
    }
    group.finish();

    let lexer_grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token A B
        %%
        start: A start { Cons(2) }
             | B       { Last() }
             ;
        "#,
        r#"
        %%
        a*b 'B'
        a   'A'
        "#,
    )
    .unwrap();
    let mut group = c.benchmark_group("maximal_munch_lexer");
    for count in [1_000usize, 10_000, 100_000] {
        let input = "a".repeat(count);
        group.throughput(Throughput::Bytes(count as u64));
        group.bench_function(count.to_string(), |b| {
            b.iter(|| lexer_grammar.lex(black_box(&input)).unwrap())
        });
    }
    group.finish();
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
