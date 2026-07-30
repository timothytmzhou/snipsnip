//! A TypeScript-flavored type system as egglog relations: expressions of the
//! same type collapse into one witness class, so `realizable` against a
//! witness asks "can the prefix complete to an expression of this type?".

use realizability::{Ast, Grammar, GrammarSymbol, Lexeme, PrefixSpace, Production};

const TYPESCRIPT: &str = include_str!("typescript.egg");

fn nt(name: &str) -> GrammarSymbol {
    GrammarSymbol::Nonterminal(name.into())
}

fn kind(name: &str) -> GrammarSymbol {
    GrammarSymbol::LexemeKind(name.into())
}

fn production(
    symbols: Vec<GrammarSymbol>,
    constructor: &str,
    selected_positions: Vec<usize>,
) -> Production {
    Production {
        nonterminal: "Expr".into(),
        symbols,
        constructor: constructor.into(),
        selected_positions,
    }
}

fn typescript_grammar() -> Grammar {
    Grammar::new(
        "Expr",
        vec![
            production(vec![kind("number")], "NumLit", vec![1]),
            production(vec![kind("string")], "StrLit", vec![1]),
            production(vec![kind("true")], "BoolTrue", vec![]),
            production(vec![kind("false")], "BoolFalse", vec![]),
            production(
                vec![kind("plus"), kind("("), nt("Expr"), kind(","), nt("Expr"), kind(")")],
                "Plus",
                vec![3, 5],
            ),
            production(
                vec![kind("lt"), kind("("), nt("Expr"), kind(","), nt("Expr"), kind(")")],
                "Lt",
                vec![3, 5],
            ),
            production(
                vec![kind("and"), kind("("), nt("Expr"), kind(","), nt("Expr"), kind(")")],
                "And",
                vec![3, 5],
            ),
            production(
                vec![
                    kind("cond"), kind("("), nt("Expr"), kind(","), nt("Expr"),
                    kind(","), nt("Expr"), kind(")"),
                ],
                "Cond",
                vec![3, 5, 7],
            ),
            production(
                vec![kind("identifier"), kind("("), nt("Expr"), kind(")")],
                "App",
                vec![1, 3],
            ),
        ],
    )
    .unwrap()
}

fn witness(type_name: &str) -> Ast {
    Ast::constructor(type_name, vec![])
}

fn space_for(type_name: &str) -> PrefixSpace {
    let mut space =
        PrefixSpace::new(typescript_grammar(), TYPESCRIPT, witness(type_name)).unwrap();
    space.saturate(20).unwrap();
    space
}

fn number(n: i64) -> Lexeme {
    Lexeme::number("number", n)
}

fn string(s: &str) -> Lexeme {
    Lexeme::text("string", s)
}

fn mark(k: &str) -> Lexeme {
    Lexeme::text(k, k)
}

fn feed_all_realizable(space: &mut PrefixSpace, lexemes: Vec<Lexeme>) {
    for lexeme in lexemes {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn each_literal_realizes_its_own_type_only() {
    let mut space = space_for("NumberTyped");
    space.derivative(number(5)).unwrap();
    assert!(space.realizable());

    let mut space = space_for("BooleanTyped");
    space.derivative(mark("true")).unwrap();
    assert!(space.realizable());

    let mut space = space_for("NumberTyped");
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn number_plus_number_realizes_number() {
    let mut space = space_for("NumberTyped");
    feed_all_realizable(
        &mut space,
        vec![mark("plus"), mark("("), number(5), mark(","), number(0), mark(")")],
    );
}

#[test]
fn a_string_operand_flips_plus_out_of_number() {
    let mut space = space_for("NumberTyped");
    feed_all_realizable(&mut space, vec![mark("plus"), mark("("), number(5), mark(",")]);
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn string_plus_anything_realizes_string() {
    let mut space = space_for("StringTyped");
    feed_all_realizable(&mut space, vec![mark("plus"), mark("("), string("a"), mark(",")]);
    space.derivative(mark("true")).unwrap();
    assert!(space.realizable());
    space.derivative(mark(")")).unwrap();
    assert!(space.realizable());
}

#[test]
fn boolean_plus_boolean_is_a_type_error() {
    let mut space = space_for("StringTyped");
    feed_all_realizable(&mut space, vec![mark("plus"), mark("("), mark("true"), mark(",")]);
    space.derivative(mark("false")).unwrap();
    assert!(!space.realizable());

    let mut space = space_for("NumberTyped");
    space.derivative(mark("plus")).unwrap();
    space.derivative(mark("(")).unwrap();
    space.derivative(mark("true")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn mixed_comparison_is_a_type_error() {
    let mut space = space_for("BooleanTyped");
    feed_all_realizable(&mut space, vec![mark("lt"), mark("("), number(5), mark(",")]);
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());

    let mut space = space_for("BooleanTyped");
    feed_all_realizable(
        &mut space,
        vec![mark("lt"), mark("("), string("a"), mark(","), string("b"), mark(")")],
    );
}

#[test]
fn conjunction_requires_same_type_operands() {
    let mut space = space_for("BooleanTyped");
    feed_all_realizable(
        &mut space,
        vec![mark("and"), mark("("), mark("true"), mark(","), mark("false"), mark(")")],
    );

    let mut space = space_for("NumberTyped");
    feed_all_realizable(&mut space, vec![mark("and"), mark("("), number(0), mark(",")]);
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn conditional_allows_any_condition_but_matching_branches() {
    let mut space = space_for("StringTyped");
    feed_all_realizable(
        &mut space,
        vec![
            mark("cond"), mark("("), number(0), mark(","), string("a"), mark(","),
            string("b"), mark(")"),
        ],
    );

    let mut space = space_for("NumberTyped");
    feed_all_realizable(
        &mut space,
        vec![mark("cond"), mark("("), mark("true"), mark(","), number(0), mark(",")],
    );
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn unseeded_literal_needs_saturation_to_be_typed() {
    let mut space = space_for("NumberTyped");
    space.derivative(mark("plus")).unwrap();
    space.derivative(mark("(")).unwrap();
    space.derivative(number(42)).unwrap();
    assert!(!space.realizable());
    space.saturate(10).unwrap();
    assert!(space.realizable());
    feed_all_realizable(&mut space, vec![mark(","), number(0), mark(")")]);
}

#[test]
fn nested_expression_stays_realizable_throughout() {
    let mut space = space_for("StringTyped");
    feed_all_realizable(
        &mut space,
        vec![
            mark("plus"), mark("("), number(5), mark(","), mark("plus"), mark("("),
            number(5), mark(","), string("a"), mark(")"), mark(")"),
        ],
    );
}

fn identifier(name: &str) -> Lexeme {
    Lexeme::text("identifier", name)
}

#[test]
fn function_application_types_by_signature() {
    let mut space = space_for("NumberTyped");
    feed_all_realizable(
        &mut space,
        vec![identifier("abs"), mark("("), number(5), mark(")")],
    );

    let mut space = space_for("StringTyped");
    feed_all_realizable(
        &mut space,
        vec![identifier("String"), mark("("), mark("true"), mark(")")],
    );
}

#[test]
fn function_argument_type_is_enforced() {
    let mut space = space_for("NumberTyped");
    feed_all_realizable(&mut space, vec![identifier("abs"), mark("(")]);
    space.derivative(string("a")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn function_name_itself_prunes() {
    let mut space = space_for("NumberTyped");
    space.derivative(identifier("frobnicate")).unwrap();
    assert!(!space.realizable());

    let mut space = space_for("StringTyped");
    space.derivative(identifier("isNaN")).unwrap();
    assert!(!space.realizable());

    let mut space = space_for("BooleanTyped");
    feed_all_realizable(
        &mut space,
        vec![identifier("isNaN"), mark("("), number(5), mark(")")],
    );
}

#[test]
fn nested_function_application_through_the_type_quotient() {
    let mut space = space_for("NumberTyped");
    feed_all_realizable(
        &mut space,
        vec![
            identifier("abs"), mark("("), identifier("abs"), mark("("), number(5),
            mark(")"), mark(")"),
        ],
    );
}
