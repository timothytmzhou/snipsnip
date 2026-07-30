//! Empirical scaling checks for the O(1)-per-token contract of
//! `PrefixSpace::derivative`.
//!
//! Run with:
//!   cargo test --release --test performance -- --ignored --nocapture
//!
//! The measurement tests are #[ignore]d so the normal suite is unaffected;
//! they print tables and the human (or auditing agent) judges the scaling.
//! The deep-cascade regression test runs with the normal suite.

use realizability::{Ast, Grammar, GrammarSymbol, Lexeme, PrefixSpace, Production};
use std::time::Instant;

const ARITH: &str = "(datatype Ast (Num i64) (Add Ast Ast))";
const COMMUTATIVITY: &str = "(rewrite (Add x y) (Add y x))";

fn arithmetic_grammar() -> Grammar {
    Grammar::new(
        "Expr",
        vec![
            Production {
                nonterminal: "Expr".into(),
                symbols: vec![GrammarSymbol::LexemeKind("number".into())],
                constructor: "Num".into(),
                selected_positions: vec![1],
            },
            Production {
                nonterminal: "Expr".into(),
                symbols: vec![
                    GrammarSymbol::LexemeKind("(".into()),
                    GrammarSymbol::Nonterminal("Expr".into()),
                    GrammarSymbol::LexemeKind("+".into()),
                    GrammarSymbol::Nonterminal("Expr".into()),
                    GrammarSymbol::LexemeKind(")".into()),
                ],
                constructor: "Add".into(),
                selected_positions: vec![2, 4],
            },
        ],
    )
    .unwrap()
}

fn num(n: i64) -> Ast {
    Ast::constructor("Num", vec![Ast::Number(n)])
}

fn add(left: Ast, right: Ast) -> Ast {
    Ast::constructor("Add", vec![left, right])
}

fn number(n: i64) -> Lexeme {
    Lexeme::number("number", n)
}

fn mark(kind: &str) -> Lexeme {
    Lexeme::text(kind, kind)
}

/// Right-nested `( 0 + ( 1 + ... ( d-1 + d ) ... ) )` with distinct numbers,
/// so e-classes are not shared. Tokens = 4*depth + 1.
fn nested_lexemes(depth: usize) -> Vec<Lexeme> {
    let mut lexemes = Vec::with_capacity(4 * depth + 1);
    for i in 0..depth {
        lexemes.push(mark("("));
        lexemes.push(number(i as i64));
        lexemes.push(mark("+"));
    }
    lexemes.push(number(depth as i64));
    for _ in 0..depth {
        lexemes.push(mark(")"));
    }
    lexemes
}

/// The matching root tree: Add(Num 0, Add(Num 1, ... Add(Num d-1, Num d)...)).
fn nested_root(depth: usize) -> Ast {
    let mut acc = num(depth as i64);
    for i in (0..depth).rev() {
        acc = add(num(i as i64), acc);
    }
    acc
}

/// Feeds all lexemes, timing the loop in four consecutive quarters so
/// prefix-position-dependent growth is visible; returns quarter times (us).
fn feed_in_quarters(space: &mut PrefixSpace, lexemes: Vec<Lexeme>) -> [f64; 4] {
    let n = lexemes.len();
    let mut quarters = [0.0f64; 4];
    let mut fed = 0usize;
    let mut iter = lexemes.into_iter();
    for (q, quarter) in quarters.iter_mut().enumerate() {
        let end = if q == 3 { n } else { (q + 1) * n / 4 };
        let start = Instant::now();
        while fed < end {
            space.derivative(iter.next().unwrap()).unwrap();
            fed += 1;
        }
        *quarter = start.elapsed().as_secs_f64() * 1e6;
    }
    quarters
}

#[test]
#[ignore]
fn nested_derivative_is_flat_per_token() {
    // Warm-up (egglog global init, allocator warmup).
    {
        let mut space =
            PrefixSpace::new(arithmetic_grammar(), ARITH, nested_root(10)).unwrap();
        for lexeme in nested_lexemes(10) {
            space.derivative(lexeme).unwrap();
        }
    }
    println!();
    println!("TEST 1: right-nested arithmetic, no rules, no saturation");
    println!(
        "{:>7} {:>10} {:>10} {:>12} | per-quarter us/token",
        "tokens", "new(ms)", "loop(ms)", "us/token"
    );
    for depth in [50usize, 100, 200, 400] {
        let lexemes = nested_lexemes(depth);
        let tokens = lexemes.len();
        let setup = Instant::now();
        let mut space =
            PrefixSpace::new(arithmetic_grammar(), ARITH, nested_root(depth)).unwrap();
        let setup_ms = setup.elapsed().as_secs_f64() * 1e3;
        let quarters = feed_in_quarters(&mut space, lexemes);
        assert!(space.realizable(), "exact word must stay realizable");
        let total_us: f64 = quarters.iter().sum();
        let per_quarter: Vec<String> = quarters
            .iter()
            .map(|q| format!("{:8.2}", q / (tokens as f64 / 4.0)))
            .collect();
        println!(
            "{:>7} {:>10.2} {:>10.2} {:>12.2} | {}",
            tokens,
            setup_ms,
            total_us / 1e3,
            total_us / tokens as f64,
            per_quarter.join(" ")
        );
    }
}

#[test]
#[ignore]
fn nested_with_rules_and_midway_saturation() {
    // Warm-up.
    {
        let program = format!("{ARITH}\n{COMMUTATIVITY}");
        let mut space =
            PrefixSpace::new(arithmetic_grammar(), &program, nested_root(10)).unwrap();
        space.saturate(1).unwrap();
        for lexeme in nested_lexemes(10) {
            space.derivative(lexeme).unwrap();
        }
    }
    println!();
    println!("TEST 2: rules loaded, saturate(1) halfway through the tokens");
    println!(
        "{:>7} {:>10} {:>12} {:>12} {:>12} {:>12}",
        "tokens", "new(ms)", "loop(ms)", "us/token", "sat1(ms)", "sat2(ms)"
    );
    for depth in [50usize, 100, 200, 400] {
        let program = format!("{ARITH}\n{COMMUTATIVITY}");
        let lexemes = nested_lexemes(depth);
        let tokens = lexemes.len();
        let half = tokens / 2;
        let setup = Instant::now();
        let mut space =
            PrefixSpace::new(arithmetic_grammar(), &program, nested_root(depth)).unwrap();
        let setup_ms = setup.elapsed().as_secs_f64() * 1e3;

        let mut loop_us = 0.0f64;
        let mut sat1_ms = 0.0f64;
        let mut sat2_ms = 0.0f64;
        for (index, lexeme) in lexemes.into_iter().enumerate() {
            if index == half {
                let t = Instant::now();
                space.saturate(1).unwrap();
                sat1_ms = t.elapsed().as_secs_f64() * 1e3;
                // A second saturation with nothing new to do: measures the
                // fixed overhead re-done per saturation point.
                let t = Instant::now();
                space.saturate(1).unwrap();
                sat2_ms = t.elapsed().as_secs_f64() * 1e3;
            }
            let t = Instant::now();
            space.derivative(lexeme).unwrap();
            loop_us += t.elapsed().as_secs_f64() * 1e6;
        }
        assert!(space.realizable(), "exact word must stay realizable");
        println!(
            "{:>7} {:>10.2} {:>12.2} {:>12.2} {:>12.2} {:>12.2}",
            tokens,
            setup_ms,
            loop_us / 1e3,
            loop_us / tokens as f64,
            sat1_ms,
            sat2_ms
        );
    }
}

const LIST: &str = "(datatype L (Nil) (Wrap L) (Cons i64 L))";

/// LL(1) chain grammar for `n0 , n1 , ... , nk ;` -> Cons/Wrap/Nil chain.
fn list_grammar() -> Grammar {
    Grammar::new(
        "List",
        vec![
            Production {
                nonterminal: "List".into(),
                symbols: vec![
                    GrammarSymbol::LexemeKind("number".into()),
                    GrammarSymbol::Nonterminal("Rest".into()),
                ],
                constructor: "Cons".into(),
                selected_positions: vec![1, 2],
            },
            Production {
                nonterminal: "Rest".into(),
                symbols: vec![
                    GrammarSymbol::LexemeKind(",".into()),
                    GrammarSymbol::Nonterminal("List".into()),
                ],
                constructor: "Wrap".into(),
                selected_positions: vec![2],
            },
            Production {
                nonterminal: "Rest".into(),
                symbols: vec![GrammarSymbol::LexemeKind(";".into())],
                constructor: "Nil".into(),
                selected_positions: vec![],
            },
        ],
    )
    .unwrap()
}

/// `0 , 1 , ... , n-1 ;` — 2n tokens.
fn list_lexemes(count: usize) -> Vec<Lexeme> {
    let mut lexemes = Vec::with_capacity(2 * count);
    for i in 0..count {
        if i > 0 {
            lexemes.push(mark(","));
        }
        lexemes.push(number(i as i64));
    }
    lexemes.push(mark(";"));
    lexemes
}

/// Cons(0, Wrap(Cons(1, ... Cons(n-1, Nil) ...)))
fn list_root(count: usize) -> Ast {
    let mut acc = Ast::constructor("Nil", vec![]);
    for i in (0..count).rev() {
        acc = Ast::constructor("Cons", vec![Ast::Number(i as i64), acc]);
        if i > 0 {
            acc = Ast::constructor("Wrap", vec![acc]);
        }
    }
    acc
}

#[test]
#[ignore]
fn wide_list_derivative_is_flat_per_token() {
    println!();
    println!("TEST 3: wide list (chain grammar), many sibling numbers");
    println!(
        "{:>7} {:>10} {:>10} {:>12} | per-quarter us/token",
        "tokens", "new(ms)", "loop(ms)", "us/token"
    );
    for count in [100usize, 200, 400, 800] {
        let lexemes = list_lexemes(count);
        let tokens = lexemes.len();
        let setup = Instant::now();
        let mut space = PrefixSpace::new(list_grammar(), LIST, list_root(count)).unwrap();
        let setup_ms = setup.elapsed().as_secs_f64() * 1e3;
        let quarters = feed_in_quarters(&mut space, lexemes);
        assert!(space.realizable(), "exact word must stay realizable");
        let total_us: f64 = quarters.iter().sum();
        let per_quarter: Vec<String> = quarters
            .iter()
            .map(|q| format!("{:8.2}", q / (tokens as f64 / 4.0)))
            .collect();
        println!(
            "{:>7} {:>10.2} {:>10.2} {:>12.2} | {}",
            tokens,
            setup_ms,
            total_us / 1e3,
            total_us / tokens as f64,
            per_quarter.join(" ")
        );
    }
}

/// The setup traversals and the final-token completion cascade used to be
/// recursive and overflowed the default stack near 2000 list elements;
/// this runs well past that point without an enlarged stack.
#[test]
fn deep_completion_cascade_runs_on_the_default_stack() {
    let count = 2500;
    let mut space = PrefixSpace::new(list_grammar(), LIST, list_root(count)).unwrap();
    for lexeme in list_lexemes(count) {
        space.derivative(lexeme).unwrap();
    }
    assert!(space.realizable(), "exact word must stay realizable");
}

/// Setup and saturation-point costs, which are allowed to be linear in the
/// e-graph but must not be worse:
///
/// (a) chain-vs-balanced arithmetic roots of equal node count should cost
///     the same to set up;
/// (b) the two-nonterminal list grammar exercises the derives worklist
///     depth-linearly, and a saturation that changed nothing (sat2, no
///     rules are loaded so both change nothing) should cost ~0.
#[test]
#[ignore]
fn localize_setup_and_saturation_growth() {
    println!();
    println!("TEST 4a: arithmetic new(), deep chain vs balanced, equal node count");
    println!("{:>8} {:>14} {:>16}", "leaves", "chain new(ms)", "balanced new(ms)");
    for leaves in [200i64, 400, 800, 1600] {
        let t = Instant::now();
        let s1 = PrefixSpace::new(arithmetic_grammar(), ARITH, chain(leaves)).unwrap();
        let chain_ms = t.elapsed().as_secs_f64() * 1e3;
        let t = Instant::now();
        let s2 = PrefixSpace::new(arithmetic_grammar(), ARITH, balanced(0, leaves)).unwrap();
        let bal_ms = t.elapsed().as_secs_f64() * 1e3;
        println!("{:>8} {:>14.2} {:>16.2}", leaves, chain_ms, bal_ms);
        drop(s1);
        drop(s2);
    }
    println!();
    println!("TEST 4b: list grammar new() and mid-parse saturate (no rules: pure refresh)");
    println!("{:>8} {:>10} {:>12} {:>12}", "count", "new(ms)", "sat1(ms)", "sat2(ms)");
    for count in [100usize, 200, 400, 800, 1600] {
        let t = Instant::now();
        let mut space = PrefixSpace::new(list_grammar(), LIST, list_root(count)).unwrap();
        let new_ms = t.elapsed().as_secs_f64() * 1e3;
        let lexemes = list_lexemes(count);
        let half = lexemes.len() / 2;
        for lexeme in lexemes.into_iter().take(half) {
            space.derivative(lexeme).unwrap();
        }
        let t = Instant::now();
        space.saturate(1).unwrap();
        let sat1_ms = t.elapsed().as_secs_f64() * 1e3;
        let t = Instant::now();
        space.saturate(1).unwrap();
        let sat2_ms = t.elapsed().as_secs_f64() * 1e3;
        println!(
            "{:>8} {:>10.2} {:>12.2} {:>12.2}",
            count, new_ms, sat1_ms, sat2_ms
        );
    }
}

/// Balanced Add tree over distinct leaves [lo, hi).
fn balanced(lo: i64, hi: i64) -> Ast {
    if hi - lo == 1 {
        num(lo)
    } else {
        let mid = lo + (hi - lo) / 2;
        add(balanced(lo, mid), balanced(mid, hi))
    }
}

/// Deep right-nested Add chain with `n` leaves.
fn chain(n: i64) -> Ast {
    let mut acc = num(n - 1);
    for i in (0..n - 1).rev() {
        acc = add(num(i), acc);
    }
    acc
}
