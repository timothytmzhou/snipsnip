use std::collections::HashSet;

use prefixspace::{Grammar, Monitor};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Lexeme {
    terminal: &'static str,
    text: &'static str,
}

impl Lexeme {
    const fn new(terminal: &'static str, text: &'static str) -> Self {
        Self { terminal, text }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Ast {
    Good,
    Bad,
    Zero,
    One,
    Alt,
    A,
    B,
    C,
    Root(Box<Ast>),
    Wrap(Box<Ast>),
    Pair(Box<Ast>, Box<Ast>),
    Var(&'static str),
}

#[derive(Clone, Debug)]
struct Completion {
    word: Vec<Lexeme>,
    ast: Ast,
}

fn boxed(ast: Ast) -> Box<Ast> {
    Box::new(ast)
}

fn has_target_completion(
    completions: &[Completion],
    prefix: &[Lexeme],
    target_class: &HashSet<Ast>,
) -> bool {
    completions.iter().any(|completion| {
        completion.word.starts_with(prefix) && target_class.contains(&completion.ast)
    })
}

fn expected_answer(
    completions: &[Completion],
    prefix: &[Lexeme],
    target_class: &HashSet<Ast>,
) -> Option<bool> {
    if has_target_completion(completions, prefix, target_class) {
        Some(true)
    } else if completions
        .iter()
        .any(|completion| completion.word.starts_with(prefix))
    {
        None
    } else {
        Some(false)
    }
}

fn fixed_length_words(alphabet: &[Lexeme], length: usize) -> Vec<Vec<Lexeme>> {
    let mut words = vec![Vec::new()];
    for _ in 0..length {
        words = words
            .into_iter()
            .flat_map(|prefix| {
                alphabet.iter().copied().map(move |lexeme| {
                    let mut word = prefix.clone();
                    word.push(lexeme);
                    word
                })
            })
            .collect();
    }
    words
}

/// Exhaustively checks every token prefix up to `maximum_length`. Complete
/// words and their action results are supplied independently of the parser.
#[allow(clippy::too_many_arguments)]
fn assert_matches_finite_oracle(
    case_name: &str,
    grammar: &Grammar,
    egraph: &str,
    binding: &str,
    alphabet: &[Lexeme],
    maximum_length: usize,
    completions: &[Completion],
    target_class: &HashSet<Ast>,
) {
    // Every shorter word occurs as a prefix of a word of this fixed length,
    // so this uses fewer monitor constructions while checking all prefixes.
    for stream in fixed_length_words(alphabet, maximum_length) {
        let mut monitor = Monitor::new(grammar, egraph, binding).unwrap();
        let mut prefix = Vec::new();
        let expected = expected_answer(completions, &prefix, target_class);
        assert_eq!(
            monitor.realizability(),
            expected,
            "{case_name}: prefix={prefix:?}"
        );

        for lexeme in stream {
            prefix.push(lexeme);
            let answer = monitor
                .push_token_name(lexeme.terminal, lexeme.text)
                .unwrap();
            let expected = expected_answer(completions, &prefix, target_class);
            assert_eq!(answer, expected, "{case_name}: prefix={prefix:?}");
        }
    }
}

fn ignored_holes_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start start
        %token A B C D
        %%
        start: optional payload trailing { Root(2) };
        optional: A { One() }
                | { Zero() }
                ;
        payload: B { Good() }
               | C { Bad() }
               ;
        trailing: D { Alt() }
                | { Zero() }
                ;
        "#,
    )
    .unwrap()
}

fn ignored_holes_completions() -> Vec<Completion> {
    let a = Lexeme::new("A", "a");
    let b = Lexeme::new("B", "b");
    let c = Lexeme::new("C", "c");
    let d = Lexeme::new("D", "d");
    let mut completions = Vec::new();
    for optional in [false, true] {
        for (payload, ast) in [(b, Ast::Good), (c, Ast::Bad)] {
            for trailing in [false, true] {
                let mut word = Vec::new();
                if optional {
                    word.push(a);
                }
                word.push(payload);
                if trailing {
                    word.push(d);
                }
                completions.push(Completion {
                    word,
                    ast: Ast::Root(boxed(ast.clone())),
                });
            }
        }
    }
    completions
}

const IGNORED_HOLES_EGRAPH: &str = r#"
    (datatype Ast (Good) (Bad) (Zero) (One) (Alt) (Root Ast))
    (let $good (Good))
    (let $bad (Bad))
    (let $root (Root $good))
"#;

#[test]
fn finite_oracle_covers_selected_and_ignored_nullable_holes() {
    let grammar = ignored_holes_grammar();
    let completions = ignored_holes_completions();
    assert_matches_finite_oracle(
        "selected/ignored nullable holes",
        &grammar,
        IGNORED_HOLES_EGRAPH,
        "$root",
        &[
            Lexeme::new("A", "a"),
            Lexeme::new("B", "b"),
            Lexeme::new("C", "c"),
            Lexeme::new("D", "d"),
        ],
        3,
        &completions,
        &HashSet::from([Ast::Root(boxed(Ast::Good))]),
    );
}

const PROJECT_EGRAPH: &str = r#"
    (datatype Ast (Good) (Bad) (Zero) (Alt))
    (let $root (Good))
"#;

#[test]
fn finite_oracle_covers_projected_prior_and_future_children() {
    let g = Lexeme::new("G", "g");
    let b = Lexeme::new("B", "b");
    let x = Lexeme::new("X", "x");
    let target = HashSet::from([Ast::Good]);

    let prior = Grammar::from_yacc(
        r#"
        %start start
        %token G B X
        %%
        start: head tail { $1 };
        head: G { Good() }
            | B { Bad() }
            ;
        tail: X { Alt() }
            | { Zero() }
            ;
        "#,
    )
    .unwrap();
    let prior_completions = [
        Completion {
            word: vec![g],
            ast: Ast::Good,
        },
        Completion {
            word: vec![g, x],
            ast: Ast::Good,
        },
        Completion {
            word: vec![b],
            ast: Ast::Bad,
        },
        Completion {
            word: vec![b, x],
            ast: Ast::Bad,
        },
    ];
    assert_matches_finite_oracle(
        "Project prior child",
        &prior,
        PROJECT_EGRAPH,
        "$root",
        &[g, b, x],
        2,
        &prior_completions,
        &target,
    );

    let future = Grammar::from_yacc(
        r#"
        %start start
        %token G B X
        %%
        start: lead value { $2 };
        lead: X { Alt() }
            | { Zero() }
            ;
        value: G { Good() }
             | B { Bad() }
             ;
        "#,
    )
    .unwrap();
    let future_completions = [
        Completion {
            word: vec![g],
            ast: Ast::Good,
        },
        Completion {
            word: vec![b],
            ast: Ast::Bad,
        },
        Completion {
            word: vec![x, g],
            ast: Ast::Good,
        },
        Completion {
            word: vec![x, b],
            ast: Ast::Bad,
        },
    ];
    assert_matches_finite_oracle(
        "Project future child",
        &future,
        PROJECT_EGRAPH,
        "$root",
        &[g, b, x],
        2,
        &future_completions,
        &target,
    );
}

#[test]
fn finite_oracle_covers_two_ambiguous_tree_shapes() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A B C
        %%
        start: ab c { Pair(1, 2) }
             | a bc { Pair(1, 2) }
             ;
        ab: a b { Pair(1, 2) };
        bc: b c { Pair(1, 2) };
        a: A { A() };
        b: B { B() };
        c: C { C() };
        "#,
    )
    .unwrap();
    let a = Lexeme::new("A", "a");
    let b = Lexeme::new("B", "b");
    let c = Lexeme::new("C", "c");
    let left = Ast::Pair(
        boxed(Ast::Pair(boxed(Ast::A), boxed(Ast::B))),
        boxed(Ast::C),
    );
    let right = Ast::Pair(
        boxed(Ast::A),
        boxed(Ast::Pair(boxed(Ast::B), boxed(Ast::C))),
    );
    let completions = [
        Completion {
            word: vec![a, b, c],
            ast: left.clone(),
        },
        Completion {
            word: vec![a, b, c],
            ast: right.clone(),
        },
    ];
    let egraph = r#"
        (datatype Ast (A) (B) (C) (Pair Ast Ast))
        (let $left (Pair (Pair (A) (B)) (C)))
        (let $right (Pair (A) (Pair (B) (C))))
    "#;
    for (binding, target) in [("$left", left), ("$right", right)] {
        assert_matches_finite_oracle(
            binding,
            &grammar,
            egraph,
            binding,
            &[a, b, c],
            3,
            &completions,
            &HashSet::from([target]),
        );
    }
}

#[test]
fn finite_oracle_covers_epsilon_and_ambiguous_nonempty_parse() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A
        %%
        start: { Zero() }
             | one { Wrap(1) }
             | alt { Wrap(1) }
             ;
        one: A { One() };
        alt: A { Alt() };
        "#,
    )
    .unwrap();
    let a = Lexeme::new("A", "a");
    let completions = [
        Completion {
            word: vec![],
            ast: Ast::Zero,
        },
        Completion {
            word: vec![a],
            ast: Ast::Wrap(boxed(Ast::One)),
        },
        Completion {
            word: vec![a],
            ast: Ast::Wrap(boxed(Ast::Alt)),
        },
    ];
    let target = HashSet::from([Ast::Zero, Ast::Wrap(boxed(Ast::Alt))]);
    assert_matches_finite_oracle(
        "epsilon plus ambiguity",
        &grammar,
        r#"
        (datatype Ast (Zero) (One) (Alt) (Wrap Ast))
        (let $root (Zero))
        (union $root (Wrap (Alt)))
        "#,
        "$root",
        &[a],
        2,
        &completions,
        &target,
    );
}

fn lexical_holes_grammar() -> Grammar {
    Grammar::from_yacc_lex(
        r#"
        %start start
        %token LP ID RP
        %%
        start: lead id trail { Var(2) };
        lead: LP { One() }
            | { Zero() }
            ;
        id: ID { $1 };
        trail: RP { Alt() }
             | { Zero() }
             ;
        "#,
        r#"
        %%
        lp   'LP'
        rp   'RP'
        [xy] 'ID'
        "#,
    )
    .unwrap()
}

fn lexical_holes_completions() -> Vec<Completion> {
    let lp = Lexeme::new("LP", "lp");
    let rp = Lexeme::new("RP", "rp");
    let mut completions = Vec::new();
    for lead in [false, true] {
        for id in ["x", "y"] {
            for trail in [false, true] {
                let mut word = Vec::new();
                if lead {
                    word.push(lp);
                }
                word.push(Lexeme::new("ID", id));
                if trail {
                    word.push(rp);
                }
                completions.push(Completion {
                    word,
                    ast: Ast::Var(id),
                });
            }
        }
    }
    completions
}

const LEXICAL_HOLES_EGRAPH: &str = r#"
    (datatype Ast (Zero) (One) (Alt) (Var String))
    (let $root (Var "x"))
"#;

#[test]
fn finite_oracle_covers_selected_lexeme_behind_nullable_holes() {
    let grammar = lexical_holes_grammar();
    assert_matches_finite_oracle(
        "selected projected lexeme",
        &grammar,
        LEXICAL_HOLES_EGRAPH,
        "$root",
        &[
            Lexeme::new("LP", "lp"),
            Lexeme::new("ID", "x"),
            Lexeme::new("ID", "y"),
            Lexeme::new("RP", "rp"),
        ],
        3,
        &lexical_holes_completions(),
        &HashSet::from([Ast::Var("x")]),
    );
}

#[test]
fn one_grammar_expression_can_supply_distinct_constructor_arguments() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A B
        %%
        deep: B { BVal() };
        value: A { AVal() }
             | deep { $1 }
             ;
        start: value value { Pair(1, 2) };
        "#,
    )
    .unwrap();
    let monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (AVal) (BVal) (Pair Ast Ast))
        (let $root (Pair (AVal) (BVal)))
        "#,
        "$root",
    )
    .unwrap();

    // Both RHS occurrences point to the same cyclic grammar expression.
    // Its AVal fact supplies the first Pair child and its BVal fact supplies
    // the second, so this is a completion of the empty prefix.
    assert_eq!(monitor.realizability(), Some(true));
}
