use prefixspace::{Grammar, LiveMonitorError, LivePrefixMonitor};

fn monitor_error(grammar: &Grammar, program: &str, target: &str) -> LiveMonitorError {
    match LivePrefixMonitor::from_egglog(grammar, program, target) {
        Ok(_) => panic!("monitor construction unexpectedly succeeded"),
        Err(error) => error,
    }
}

#[test]
fn live_constructor_and_input_errors_are_typed() {
    let leaf = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { Leaf() };
        "#,
    )
    .unwrap();

    assert!(matches!(
        monitor_error(&leaf, "(datatype Ast (Leaf))", "$missing"),
        LiveMonitorError::InvalidBinding { .. }
    ));
    assert!(matches!(
        monitor_error(&leaf, "(let $root 1)", "$root"),
        LiveMonitorError::NonEqualityTarget(name) if name == "i64"
    ));
    assert!(matches!(
        monitor_error(
            &leaf,
            "(datatype Ast (Other)) (let $root (Other))",
            "$root"
        ),
        LiveMonitorError::MissingConstructor(name) if name == "Leaf"
    ));

    let wrong_arity = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { Pair() };
        "#,
    )
    .unwrap();
    assert!(matches!(
        monitor_error(
            &wrong_arity,
            "(datatype Ast (Root) (Pair Ast)) (let $root (Root))",
            "$root"
        ),
        LiveMonitorError::ConstructorArity {
            constructor,
            expected: 0,
            actual: 1
        } if constructor == "Pair"
    ));

    let selected_without_lex = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { Var(1) };
        "#,
    )
    .unwrap();
    assert!(matches!(
        monitor_error(
            &selected_without_lex,
            "(datatype Ast (Var String)) (let $root (Var \"x\"))",
            "$root"
        ),
        LiveMonitorError::SelectedTerminalWithoutLexer(name) if name == "X"
    ));

    let selected_bool = Grammar::from_yacc_lex(
        r#"
        %start start
        %token X
        %%
        start: X { Flag(1) };
        "#,
        "%%\nx 'X'\n",
    )
    .unwrap();
    let error = monitor_error(
        &selected_bool,
        "(datatype Ast (Flag bool)) (let $root (Flag true))",
        "$root",
    );
    assert!(
        matches!(
            &error,
            LiveMonitorError::UnsupportedLexicalSort { terminal, sort }
            if terminal == "X" && sort == "bool"
        ),
        "{error:?}"
    );

    let unsupported_semantic = Grammar::from_yacc(
        r#"
        %start start
        %%
        start: child { Wrap(1) };
        child: { Child() };
        "#,
    )
    .unwrap();
    assert!(matches!(
        monitor_error(
            &unsupported_semantic,
            r#"
            (datatype Ast (Root) (Child))
            (constructor Wrap (bool) Ast)
            (let $root (Root))
            "#,
            "$root"
        ),
        LiveMonitorError::UnsupportedSemanticSort(sort) if sort == "bool"
    ));

    let lexed = Grammar::from_yacc_lex(
        r#"
        %start start
        %token X
        %%
        start: X { Leaf() };
        "#,
        "%%\n[a-z]+ 'X'\n",
    )
    .unwrap();
    let mut monitor =
        LivePrefixMonitor::from_egglog(&lexed, "(datatype Ast (Leaf)) (let $root (Leaf))", "$root")
            .unwrap();
    assert!(matches!(
        monitor.push_token_name("MISSING", "x"),
        Err(LiveMonitorError::UnknownTerminal(name)) if name == "MISSING"
    ));
    assert!(matches!(
        monitor.push_token_name("X", "123"),
        Err(LiveMonitorError::LexemeMismatch { terminal, lexeme })
            if terminal == "X" && lexeme == "123"
    ));
    assert!(matches!(
        monitor.run_egglog("(check (= (Leaf) (Leaf)))"),
        Err(LiveMonitorError::UnsupportedUpdateCommand(name)) if name == "check"
    ));
}

#[test]
fn live_monitor_accepts_punctuated_ranked_constructor_names() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { node::leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (node::leaf)) (let $root (node::leaf))",
        "$root",
    )
    .unwrap();
    assert!(!monitor.intersection_is_empty());
    assert!(!monitor.push_token_name("X", "x").unwrap());
}

#[test]
fn six_ary_sparse_action_survives_a_late_target_union() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A B C D E F SEP
        %%
        start: a SEP b SEP c SEP d SEP e SEP f { Six(1, 3, 5, 7, 9, 11) };
        a: A { ALeaf() };
        b: B { BLeaf() };
        c: C { CLeaf() };
        d: D { DLeaf() };
        e: E { ELeaf() };
        f: F { FLeaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast
          (Old) (ALeaf) (BLeaf) (CLeaf) (DLeaf) (ELeaf) (FLeaf)
          (Six Ast Ast Ast Ast Ast Ast))
        (let $root (Old))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.intersection_is_empty());

    for (terminal, lexeme) in [("A", "a"), ("SEP", ","), ("B", "b")] {
        assert!(monitor.push_token_name(terminal, lexeme).unwrap());
    }
    let lexeme_updates = monitor.stats().lexeme_updates;
    assert!(
        !monitor
            .run_egglog("(union $root (Six (ALeaf) (BLeaf) (CLeaf) (DLeaf) (ELeaf) (FLeaf)))")
            .unwrap()
    );
    assert_eq!(monitor.stats().lexeme_updates, lexeme_updates);

    for (terminal, lexeme) in [
        ("SEP", ","),
        ("C", "c"),
        ("SEP", ","),
        ("D", "d"),
        ("SEP", ","),
        ("E", "e"),
        ("SEP", ","),
        ("F", "f"),
    ] {
        assert!(!monitor.push_token_name(terminal, lexeme).unwrap());
    }
    assert!(!monitor.intersection_is_empty());
}
