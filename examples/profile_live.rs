use std::{env, hint::black_box, time::Instant};

use prefixspace::{Grammar, LivePrefixMonitor, PwzRecognizer};

fn grammar() -> Grammar {
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

const LIVE_EGRAPH: &str = r#"
    (datatype Ast (List Ast) (Cons Ast) (Nil) (JunkLeft) (JunkRight))
    (let $nil (Nil))
    (union $nil (Cons $nil))
    (let $root (List $nil))
    (let $junk-left (JunkLeft))
    (let $junk-right (JunkRight))
"#;

const UNMATCHED_EGRAPH: &str = r#"
    (datatype Ast (List Ast) (Cons Ast) (Nil) (Junk))
    (let $root (Junk))
"#;

const LATE_EGRAPH: &str = r#"
    (datatype Ast (List Ast) (Cons Ast) (Nil) (JunkLeft) (JunkRight))
    (let $nil (Nil))
    (let $root (List $nil))
    (let $junk-left (JunkLeft))
    (let $junk-right (JunkRight))
"#;

fn setup_monitor(count: usize, program: &str) -> LivePrefixMonitor {
    let grammar = grammar();
    let terminal = grammar.terminal_by_name("X").unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, program, "$root").unwrap();
    for _ in 0..count {
        black_box(monitor.push_lexeme(terminal, "x").unwrap());
    }
    monitor
}

fn main() {
    let count = env::args().nth(1).unwrap().parse::<usize>().unwrap();
    let mode = env::args().nth(2).unwrap_or_else(|| "live".to_owned());
    match mode.as_str() {
        "vanilla" => {
            let started = Instant::now();
            let grammar = grammar();
            let terminal = grammar.terminal_by_name("X").unwrap();
            let mut parser = PwzRecognizer::compile(&grammar).unwrap();
            for _ in 0..count {
                black_box(parser.push(terminal).unwrap());
            }
            eprintln!("mode=vanilla count={count} elapsed={:?}", started.elapsed());
        }
        "forest" | "live" => {
            let started = Instant::now();
            let program = if mode == "forest" {
                UNMATCHED_EGRAPH
            } else {
                LIVE_EGRAPH
            };
            let monitor = setup_monitor(count, program);
            eprintln!(
                "mode={mode} count={count} elapsed={:?} stats={:?}",
                started.elapsed(),
                monitor.stats()
            );
        }
        "noop" | "unrelated" | "relevant" => {
            let program = if mode == "relevant" {
                LATE_EGRAPH
            } else {
                LIVE_EGRAPH
            };
            let mut monitor = setup_monitor(count, program);
            let update = match mode.as_str() {
                "noop" => "(run 1)",
                "unrelated" => "(union $junk-left $junk-right)",
                "relevant" => "(union $nil (Cons $nil))",
                _ => unreachable!(),
            };
            let started = Instant::now();
            black_box(monitor.run_egglog(update).unwrap());
            eprintln!(
                "mode={mode} count={count} elapsed={:?} stats={:?}",
                started.elapsed(),
                monitor.stats()
            );
        }
        _ => panic!("mode must be vanilla, forest, live, noop, unrelated, or relevant"),
    }
}
