use std::fmt::Write;

use prefixspace::{Grammar, Monitor};

fn deep_right_recursive_fixture(depth: usize) -> (Grammar, String) {
    let mut yacc = String::from("%start n0\n%token X\n%%\n");
    for level in 0..depth {
        writeln!(yacc, "n{level}: X n{} {{ C{level}(2) }};", level + 1).unwrap();
    }
    writeln!(yacc, "n{depth}: X {{ Actual() }};").unwrap();

    let mut egglog = String::from("(datatype Ast (Actual) (Expected)");
    for level in 0..depth {
        write!(egglog, " (C{level} Ast)").unwrap();
    }
    egglog.push_str(")\n(let $expected (Expected))\n(let $root ");
    for level in 0..depth {
        write!(egglog, "(C{level} ").unwrap();
    }
    egglog.push_str("$expected");
    for _ in 0..depth {
        egglog.push(')');
    }
    egglog.push_str(")\n");

    (Grammar::from_yacc(&yacc).unwrap(), egglog)
}

#[test]
fn late_leaf_union_propagates_through_a_300_layer_realizability_chain() {
    const DEPTH: usize = 300;
    let (grammar, egglog) = deep_right_recursive_fixture(DEPTH);
    let terminal = grammar.terminal_by_name("X").unwrap();
    let mut monitor = Monitor::new(&grammar, &egglog, "$root").unwrap();

    // The only syntactic tree ends in Actual, while the target chain ends in
    // Expected. Keep a substantial parser history before changing the egraph.
    assert_eq!(monitor.realizability(), None);
    for _ in 0..=DEPTH / 2 {
        assert_eq!(monitor.push_lexeme(terminal, "x").unwrap(), None);
    }

    // The prefix is unchanged. One leaf merge must propagate through all 300
    // retained constructor levels without replaying it.
    assert_eq!(
        monitor.run_egglog("(union $expected (Actual))").unwrap(),
        Some(true)
    );
    for _ in (DEPTH / 2 + 1)..=DEPTH {
        assert_eq!(monitor.push_lexeme(terminal, "x").unwrap(), Some(true));
    }
    assert_eq!(monitor.realizability(), Some(true));

    // One extra token is syntactically irreparable.
    assert_eq!(monitor.push_lexeme(terminal, "x").unwrap(), Some(false));
}
