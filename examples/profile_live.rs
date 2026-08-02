use std::{env, hint::black_box, time::Instant};

use prefixspace::{
    Grammar, Monitor,
    paper_pwz::{Grammar as PwzGrammar, Pwz, Token as PwzToken},
};

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

fn setup_monitor(count: usize, program: &str) -> Monitor {
    let grammar = grammar();
    let terminal = grammar.terminal_by_name("X").unwrap();
    let mut monitor = Monitor::new(&grammar, program, "$root").unwrap();
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
            let compiled: PwzGrammar<()> = (&grammar).try_into().unwrap();
            let mut parser = Pwz::new(compiled);
            for _ in 0..count {
                parser.derive(PwzToken {
                    terminal: terminal.index() as u32,
                    payload: (),
                });
                black_box(parser.zippers());
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
            black_box(setup_monitor(count, program));
            eprintln!("mode={mode} count={count} elapsed={:?}", started.elapsed());
        }
        "noop" | "unrelated" | "relevant" => {
            let program = if mode == "relevant" {
                LATE_EGRAPH
            } else {
                LIVE_EGRAPH
            };
            let mut monitor = setup_monitor(count, program);
            let update = match mode.as_str() {
                "noop" => "(union $nil $nil)",
                "unrelated" => "(union $junk-left $junk-right)",
                "relevant" => "(union $nil (Cons $nil))",
                _ => unreachable!(),
            };
            let started = Instant::now();
            black_box(monitor.run_egglog(update).unwrap());
            eprintln!("mode={mode} count={count} elapsed={:?}", started.elapsed());
        }
        _ => panic!("mode must be vanilla, forest, live, noop, unrelated, or relevant"),
    }
}
