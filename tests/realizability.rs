use realizability::{Ast, Grammar, GrammarError, GrammarSymbol, Lexeme, PrefixSpace, Production};

const ARITH: &str = "(datatype Ast (Num i64) (Add Ast Ast))";
const COMMUTATIVITY: &str = "(rewrite (Add x y) (Add y x))";
const DROP_ZERO: &str = "(rewrite (Add x (Num 0)) x)";

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

fn feed(space: &mut PrefixSpace, lexemes: Vec<Lexeme>) {
    for lexeme in lexemes {
        space.derivative(lexeme).unwrap();
    }
}

#[test]
fn exact_program_is_realizable_at_every_prefix() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    assert!(space.realizable());
    for lexeme in [mark("("), number(1), mark("+"), number(2), mark(")")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn open_hole_can_still_reach_the_root() {
    let root = add(num(1), num(5));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    feed(&mut space, vec![mark("("), number(1), mark("+")]);
    assert!(space.realizable());
}

#[test]
fn wrong_first_argument_is_not_realizable() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    feed(&mut space, vec![mark("("), number(2)]);
    assert!(!space.realizable());
}

#[test]
fn deep_prefix_is_pruned_early() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    feed(&mut space, vec![mark("("), mark("(")]);
    assert!(!space.realizable());
}

#[test]
fn commutativity_makes_swapped_prefix_realizable() {
    let root = add(num(1), num(2));
    let program = format!("{ARITH}\n{COMMUTATIVITY}");
    let mut space = PrefixSpace::new(arithmetic_grammar(), &program, root).unwrap();
    space.saturate(10).unwrap();
    // The intended completion must itself be in the e-graph.
    assert!(space.asts_equal(&add(num(2), num(1)), &add(num(1), num(2))));
    for lexeme in [mark("("), number(2), mark("+"), number(1), mark(")")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn saturation_after_derivative_flips_no_to_yes() {
    let root = add(num(1), num(2));
    let program = format!("{ARITH}\n{COMMUTATIVITY}");
    let mut space = PrefixSpace::new(arithmetic_grammar(), &program, root).unwrap();
    feed(&mut space, vec![mark("("), number(2)]);
    assert!(!space.realizable());
    space.saturate(10).unwrap();
    assert!(space.realizable());
    assert!(space.asts_equal(&add(num(2), num(1)), &add(num(1), num(2))));
}

#[test]
fn completed_program_becomes_equal_by_rule() {
    let root = num(1);
    let program = format!("{ARITH}\n{DROP_ZERO}");
    let mut space = PrefixSpace::new(arithmetic_grammar(), &program, root).unwrap();
    feed(
        &mut space,
        vec![mark("("), number(1), mark("+"), number(0), mark(")")],
    );
    assert!(!space.realizable());
    space.saturate(10).unwrap();
    assert!(space.asts_equal(&add(num(1), num(0)), &num(1)));
    assert!(space.realizable());
}

#[test]
fn non_ll1_grammar_is_rejected() {
    let result = Grammar::new(
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
                    GrammarSymbol::LexemeKind("number".into()),
                    GrammarSymbol::LexemeKind("number".into()),
                ],
                constructor: "Pair".into(),
                selected_positions: vec![1, 2],
            },
        ],
    );
    assert!(result.is_err());
}

#[test]
fn syntactically_impossible_lexeme_is_an_error() {
    let root = num(1);
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    assert!(space.derivative(mark(")")).is_err());
}

const ARITH_WITH_MUL: &str = "(datatype Ast (Num i64) (Add Ast Ast) (Mul Ast Ast))";

fn two_level_grammar() -> Grammar {
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
                    GrammarSymbol::Nonterminal("Term".into()),
                    GrammarSymbol::LexemeKind("+".into()),
                    GrammarSymbol::Nonterminal("Term".into()),
                    GrammarSymbol::LexemeKind(")".into()),
                ],
                constructor: "Add".into(),
                selected_positions: vec![2, 4],
            },
            Production {
                nonterminal: "Term".into(),
                symbols: vec![GrammarSymbol::LexemeKind("number".into())],
                constructor: "Num".into(),
                selected_positions: vec![1],
            },
        ],
    )
    .unwrap()
}

#[test]
fn nested_exact_program_is_realizable_at_every_prefix() {
    let root = add(add(num(1), num(2)), num(3));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    for lexeme in [
        mark("("),
        mark("("),
        number(1),
        mark("+"),
        number(2),
        mark(")"),
        mark("+"),
        number(3),
        mark(")"),
    ] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn nested_wrong_inner_argument_is_not_realizable() {
    let root = add(add(num(1), num(2)), num(3));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    feed(&mut space, vec![mark("("), mark("("), number(1), mark("+")]);
    assert!(space.realizable());
    space.derivative(number(3)).unwrap();
    assert!(!space.realizable());
}

#[test]
fn nested_commutativity_at_both_levels() {
    let root = add(add(num(1), num(2)), num(3));
    let program = format!("{ARITH}\n{COMMUTATIVITY}");
    let mut space = PrefixSpace::new(arithmetic_grammar(), &program, root).unwrap();
    space.saturate(10).unwrap();
    for lexeme in [
        mark("("),
        number(3),
        mark("+"),
        mark("("),
        number(2),
        mark("+"),
        number(1),
        mark(")"),
        mark(")"),
    ] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
    assert!(space.asts_equal(&add(num(3), add(num(2), num(1))), &root_copy()));
}

fn root_copy() -> Ast {
    add(add(num(1), num(2)), num(3))
}

#[test]
fn underivable_root_is_never_realizable() {
    let root = Ast::constructor("Mul", vec![num(1), num(2)]);
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH_WITH_MUL, root).unwrap();
    assert!(!space.realizable());
    space.derivative(mark("(")).unwrap();
    assert!(!space.realizable());
}

#[test]
fn union_widens_the_open_hole() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    space
        .run_program("(union (Add (Num 1) (Num 2)) (Add (Num 1) (Num 3)))")
        .unwrap();
    feed(&mut space, vec![mark("("), number(1), mark("+")]);
    assert!(space.realizable());
    space.derivative(number(3)).unwrap();
    assert!(space.realizable());
    space.derivative(mark(")")).unwrap();
    assert!(space.realizable());
    assert!(space.asts_equal(&add(num(1), num(3)), &add(num(1), num(2))));
}

#[test]
fn union_does_not_allow_unrelated_arguments() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    space
        .run_program("(union (Add (Num 1) (Num 2)) (Add (Num 1) (Num 3)))")
        .unwrap();
    feed(&mut space, vec![mark("("), number(1), mark("+"), number(4)]);
    assert!(!space.realizable());
}

#[test]
fn saturation_mid_parse_then_more_lexemes() {
    let root = add(num(1), num(2));
    let program = format!("{ARITH}\n{COMMUTATIVITY}");
    let mut space = PrefixSpace::new(arithmetic_grammar(), &program, root).unwrap();
    feed(&mut space, vec![mark("("), number(2)]);
    assert!(!space.realizable());
    space.saturate(10).unwrap();
    assert!(space.realizable());
    for lexeme in [mark("+"), number(1), mark(")")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn unrepresented_number_is_not_realizable_until_saturation_could_help() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    feed(&mut space, vec![mark("("), number(5)]);
    assert!(!space.realizable());
}

#[test]
fn derivative_after_complete_word_is_an_error() {
    let root = num(1);
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    space.derivative(number(1)).unwrap();
    assert!(space.realizable());
    assert!(space.derivative(number(2)).is_err());
}

#[test]
fn plus_cannot_start_a_program() {
    let root = num(1);
    let mut space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    assert!(space.derivative(mark("+")).is_err());
}

#[test]
fn asts_equal_is_false_for_distinct_classes() {
    let root = add(num(1), num(2));
    let space = PrefixSpace::new(arithmetic_grammar(), ARITH, root).unwrap();
    assert!(!space.asts_equal(&num(1), &num(2)));
}

#[test]
fn predict_chain_through_second_nonterminal() {
    let root = add(num(1), num(2));
    let mut space = PrefixSpace::new(two_level_grammar(), ARITH, root).unwrap();
    for lexeme in [mark("("), number(1), mark("+"), number(2), mark(")")] {
        space.derivative(lexeme).unwrap();
        assert!(space.realizable());
    }
}

#[test]
fn left_recursive_grammar_is_rejected() {
    let result = Grammar::new(
        "Expr",
        vec![Production {
            nonterminal: "Expr".into(),
            symbols: vec![
                GrammarSymbol::Nonterminal("Expr".into()),
                GrammarSymbol::LexemeKind("+".into()),
            ],
            constructor: "Inc".into(),
            selected_positions: vec![1],
        }],
    );
    assert!(matches!(result, Err(GrammarError::LeftRecursive(_))));
}

#[test]
fn unknown_nonterminal_is_rejected() {
    let result = Grammar::new(
        "Expr",
        vec![Production {
            nonterminal: "Expr".into(),
            symbols: vec![GrammarSymbol::Nonterminal("Missing".into())],
            constructor: "Wrap".into(),
            selected_positions: vec![1],
        }],
    );
    assert!(matches!(result, Err(GrammarError::UnknownNonterminal(_))));
}

#[test]
fn empty_production_is_rejected() {
    let result = Grammar::new(
        "Expr",
        vec![Production {
            nonterminal: "Expr".into(),
            symbols: vec![],
            constructor: "Nothing".into(),
            selected_positions: vec![],
        }],
    );
    assert!(matches!(result, Err(GrammarError::EmptyProduction(_))));
}

#[test]
fn decreasing_selected_positions_are_rejected() {
    let result = Grammar::new(
        "Expr",
        vec![Production {
            nonterminal: "Expr".into(),
            symbols: vec![
                GrammarSymbol::LexemeKind("number".into()),
                GrammarSymbol::LexemeKind("number".into()),
            ],
            constructor: "Pair".into(),
            selected_positions: vec![2, 1],
        }],
    );
    assert!(matches!(result, Err(GrammarError::InvalidSelectedPositions(_))));
}
