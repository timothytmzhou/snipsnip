use realizability::{Ast, Grammar, GrammarSymbol, Lexeme, PrefixSpace, Production};

fn nt(name: &str) -> GrammarSymbol {
    GrammarSymbol::Nonterminal(name.into())
}

fn kind(name: &str) -> GrammarSymbol {
    GrammarSymbol::LexemeKind(name.into())
}

fn mark(k: &str) -> Lexeme {
    Lexeme::text(k, k)
}

fn number(n: i64) -> Lexeme {
    Lexeme::number("number", n)
}

fn production(
    nonterminal: &str,
    symbols: Vec<GrammarSymbol>,
    constructor: &str,
    selected_positions: Vec<usize>,
) -> Production {
    Production {
        nonterminal: nonterminal.into(),
        symbols,
        constructor: constructor.into(),
        selected_positions,
    }
}

// --- Peano numerals -------------------------------------------------------

const PEANO: &str = "(datatype Ast (Zero) (Succ Ast))";
const PEANO_MOD_TWO: &str =
    "(datatype Ast (Zero) (Succ Ast))\n(rewrite (Succ (Succ x)) x)\n(let seed (Succ (Succ (Zero))))";

fn peano_grammar() -> Grammar {
    Grammar::new(
        "Numeral",
        vec![
            production("Numeral", vec![kind("z")], "Zero", vec![]),
            production("Numeral", vec![kind("s"), nt("Numeral")], "Succ", vec![2]),
        ],
    )
    .unwrap()
}

fn zero() -> Ast {
    Ast::constructor("Zero", vec![])
}

fn succ(inner: Ast) -> Ast {
    Ast::constructor("Succ", vec![inner])
}

#[test]
fn peano_exact_numeral_is_realizable_at_every_prefix() {
    let root = succ(succ(zero()));
    let mut space = PrefixSpace::new(peano_grammar(), PEANO, root).unwrap();
    for lexeme in [mark("s"), mark("s"), mark("z")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn peano_too_deep_prefix_is_not_realizable() {
    let root = succ(succ(zero()));
    let mut space = PrefixSpace::new(peano_grammar(), PEANO, root).unwrap();
    for lexeme in [mark("s"), mark("s"), mark("s")] {
        space.derivative(lexeme).unwrap();
    }
    assert!(!space.realizable());
}

#[test]
fn peano_modulo_two_keeps_even_prefixes_alive() {
    let root = zero();
    let mut space = PrefixSpace::new(peano_grammar(), PEANO_MOD_TWO, root).unwrap();
    space.saturate(10).unwrap();
    // Any number of `s` stays realizable: parity can always be completed.
    for lexeme in [mark("s"), mark("s"), mark("s"), mark("s")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
    space.derivative(mark("z")).unwrap();
    assert!(space.realizable());
    assert!(space.asts_equal(&succ(succ(zero())), &zero()));
}

#[test]
fn peano_modulo_two_rejects_odd_words() {
    let root = zero();
    let mut space = PrefixSpace::new(peano_grammar(), PEANO_MOD_TWO, root).unwrap();
    space.saturate(10).unwrap();
    space.derivative(mark("s")).unwrap();
    assert!(space.realizable());
    space.derivative(mark("z")).unwrap();
    assert!(!space.realizable());
}

// --- Forced-parenthesis subtraction (no left-associative chains) ----------

const SUBTRACTION: &str = "(datatype Ast (Num i64) (Sub Ast Ast))";

fn subtraction_grammar() -> Grammar {
    Grammar::new(
        "Expr",
        vec![
            production("Expr", vec![kind("number")], "Num", vec![1]),
            production(
                "Expr",
                vec![kind("("), nt("Expr"), kind("-"), nt("Expr"), kind(")")],
                "Sub",
                vec![2, 4],
            ),
        ],
    )
    .unwrap()
}

fn num(n: i64) -> Ast {
    Ast::constructor("Num", vec![Ast::Number(n)])
}

fn sub(left: Ast, right: Ast) -> Ast {
    Ast::constructor("Sub", vec![left, right])
}

#[test]
fn right_nested_subtraction_is_realizable_at_every_prefix() {
    let root = sub(num(5), sub(num(3), num(2)));
    let mut space = PrefixSpace::new(subtraction_grammar(), SUBTRACTION, root).unwrap();
    for lexeme in [
        mark("("),
        number(5),
        mark("-"),
        mark("("),
        number(3),
        mark("-"),
        number(2),
        mark(")"),
        mark(")"),
    ] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn wrong_minuend_is_not_realizable() {
    let root = sub(num(5), sub(num(3), num(2)));
    let mut space = PrefixSpace::new(subtraction_grammar(), SUBTRACTION, root).unwrap();
    space.derivative(mark("(")).unwrap();
    space.derivative(number(3)).unwrap();
    assert!(!space.realizable());
}

#[test]
fn drop_zero_rule_flips_subtraction_result() {
    let program = format!("{SUBTRACTION}\n(rewrite (Sub x (Num 0)) x)");
    let root = num(7);
    let mut space = PrefixSpace::new(subtraction_grammar(), &program, root).unwrap();
    for lexeme in [mark("("), number(7), mark("-"), number(0), mark(")")] {
        space.derivative(lexeme).unwrap();
    }
    assert!(!space.realizable());
    space.saturate(10).unwrap();
    assert!(space.realizable());
    assert!(space.asts_equal(&sub(num(7), num(0)), &num(7)));
}

// --- A statement level above expressions ----------------------------------

const PRINT: &str = "(datatype Ast (Num i64) (Add Ast Ast) (Print Ast))";

fn print_grammar() -> Grammar {
    Grammar::new(
        "Statement",
        vec![
            production(
                "Statement",
                vec![kind("print"), kind("("), nt("Expr"), kind(")")],
                "Print",
                vec![3],
            ),
            production("Expr", vec![kind("number")], "Num", vec![1]),
            production(
                "Expr",
                vec![kind("("), nt("Expr"), kind("+"), nt("Expr"), kind(")")],
                "Add",
                vec![2, 4],
            ),
        ],
    )
    .unwrap()
}

#[test]
fn statement_over_expression_is_realizable_at_every_prefix() {
    let root = Ast::constructor("Print", vec![Ast::constructor(
        "Add",
        vec![num(1), num(2)],
    )]);
    let mut space = PrefixSpace::new(print_grammar(), PRINT, root).unwrap();
    for lexeme in [
        mark("print"),
        mark("("),
        mark("("),
        number(1),
        mark("+"),
        number(2),
        mark(")"),
        mark(")"),
    ] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn statement_with_wrong_expression_is_not_realizable() {
    let root = Ast::constructor("Print", vec![num(1)]);
    let mut space = PrefixSpace::new(print_grammar(), PRINT, root).unwrap();
    space.derivative(mark("print")).unwrap();
    space.derivative(mark("(")).unwrap();
    assert!(space.realizable());
    space.derivative(number(3)).unwrap();
    assert!(!space.realizable());
}

// --- Union at the root ----------------------------------------------------

#[test]
fn union_at_the_root_admits_a_second_completion() {
    let root = sub(num(5), num(3));
    let mut space = PrefixSpace::new(subtraction_grammar(), SUBTRACTION, root).unwrap();
    space.run_program("(union (Sub (Num 5) (Num 3)) (Num 7))").unwrap();
    space.derivative(number(7)).unwrap();
    assert!(space.realizable());
}
