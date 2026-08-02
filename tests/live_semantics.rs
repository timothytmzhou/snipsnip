use prefixspace::{Grammar, Monitor};

#[test]
fn lexical_sort_flows_through_project_productions() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID
        %%
        start: id { Var(1) };
        id: alias { $1 };
        alias: ID { $1 };
        "#,
        r#"
        %%
        [a-z]+ 'ID'
        "#,
    )
    .unwrap();
    let egraph = r#"
        (datatype Ast (Var String))
        (let $root (Var "x"))
    "#;

    // The Var input schema determines that ID denotes a String even though
    // two Project actions separate the terminal from the constructor.
    let mut accepted = Monitor::new(&grammar, egraph, "$root").unwrap();
    assert_eq!(accepted.realizability(), Some(true));
    assert_eq!(accepted.push_token_name("ID", "x").unwrap(), Some(true));

    let mut resurrected = Monitor::new(&grammar, egraph, "$root").unwrap();
    assert_eq!(resurrected.push_token_name("ID", "y").unwrap(), None);
    assert_eq!(
        resurrected.run_egglog("(union $root (Var \"y\"))").unwrap(),
        Some(true)
    );
}

#[test]
fn nullable_left_recursion_tracks_a_recursive_target_class() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: start X { Cons(1) }
             | { Nil() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Nil) (Cons Ast))
        (let $root (Nil))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(monitor.push_token_name("X", "x").unwrap(), None);

    // The consumed prefix is unchanged.  Making the target class recursive
    // must recover Cons(Nil), Cons(Cons(Nil)), ... incrementally.
    assert_eq!(
        monitor.run_egglog("(union $root (Cons $root))").unwrap(),
        Some(true)
    );
    for _ in 0..8 {
        assert_eq!(monitor.push_token_name("X", "x").unwrap(), Some(true));
    }
}

#[test]
fn ambiguous_left_recursive_grammar_preserves_both_tree_shapes() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A
        %%
        start: start start { Pair(1, 2) }
             | A { Leaf() }
             ;
        "#,
    )
    .unwrap();
    let egraph = r#"
        (datatype Ast (Leaf) (Pair Ast Ast))
        (let $left (Pair (Pair (Leaf) (Leaf)) (Leaf)))
        (let $right (Pair (Leaf) (Pair (Leaf) (Leaf))))
    "#;

    for target in ["$left", "$right"] {
        let mut monitor = Monitor::new(&grammar, egraph, target).unwrap();
        assert_eq!(monitor.realizability(), Some(true));
        assert_eq!(monitor.push_token_name("A", "a").unwrap(), Some(true));
        assert_eq!(monitor.push_token_name("A", "a").unwrap(), Some(true));
        assert_eq!(monitor.push_token_name("A", "a").unwrap(), Some(true));
    }
}

#[test]
fn project_unit_cycle_terminates_and_preserves_the_leaf_value() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A
        %%
        start: value { $1 };
        value: start { $1 }
             | A { Leaf() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Leaf))
        (let $root (Leaf))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(monitor.push_token_name("A", "a").unwrap(), Some(true));
    assert_eq!(monitor.push_token_name("A", "a").unwrap(), Some(false));
}
