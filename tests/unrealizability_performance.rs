use std::time::{Duration, Instant};

use prefixspace::{Grammar, Monitor};

fn stream_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start stream
        %token X SEMI END
        %%
        stream: item stream { $1 }
              | END         { Wanted() }
              ;
        item: X SEMI { Wanted() };
        "#,
    )
    .unwrap()
}

fn stream_monitor(unrelated_terms: usize, negative: bool) -> Monitor {
    let grammar = stream_grammar();
    let mut program = String::from(
        r#"
        (datatype Type (Wanted) (Other) (Junk i64))
        (relation Disjoint (Type Type))
        (Disjoint (Wanted) (Other))
        (Disjoint (Other) (Wanted))
        "#,
    );
    for value in 0..unrelated_terms {
        program.push_str(&format!("(Junk {value})\n"));
    }
    program.push_str(if negative {
        "(let $target (Other))\n"
    } else {
        "(let $target (Wanted))\n"
    });
    Monitor::new(&grammar, &program, "$target").unwrap()
}

fn push_statements(monitor: &mut Monitor, count: usize, expected: Option<bool>) -> Duration {
    let start = Instant::now();
    for _ in 0..count {
        assert_eq!(monitor.push_token_name("X", "x").unwrap(), expected);
        assert_eq!(monitor.push_token_name("SEMI", ";").unwrap(), expected);
    }
    start.elapsed()
}

fn assert_loosely_bounded(small: Duration, large: Duration, multiplier: u32) {
    let bound = small
        .saturating_mul(multiplier)
        .saturating_add(Duration::from_secs(3));
    assert!(large <= bound, "small={small:?}, large={large:?}");
}

#[test]
fn long_ll1_stream_has_linear_black_box_scaling() {
    let mut small = stream_monitor(0, false);
    let mut large = stream_monitor(0, false);

    assert_eq!(small.realizability(), Some(true));
    assert_eq!(large.realizability(), Some(true));
    let small_elapsed = push_statements(&mut small, 128, Some(true));
    let large_elapsed = push_statements(&mut large, 1_024, Some(true));

    assert_eq!(large.realizability(), Some(true));
    assert_loosely_bounded(small_elapsed, large_elapsed, 24);
}

#[test]
fn large_unrelated_egraph_does_not_dominate_streaming_updates() {
    let mut small = stream_monitor(16, true);
    let mut large = stream_monitor(
        if cfg!(debug_assertions) {
            2_000
        } else {
            10_000
        },
        true,
    );

    assert_eq!(small.realizability(), Some(false));
    assert_eq!(large.realizability(), Some(false));
    let small_elapsed = push_statements(&mut small, 128, Some(false));
    let large_elapsed = push_statements(&mut large, 128, Some(false));

    assert_eq!(large.realizability(), Some(false));
    assert_loosely_bounded(small_elapsed, large_elapsed, 8);
}
