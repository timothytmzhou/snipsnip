use prefixspace::{Grammar, Monitor, MonitorError};

#[test]
fn future_i64_spelling_search_handles_signs_and_long_zero_runs_exactly() {
    fn check(regex: &str, value: i64, lexeme: &str) {
        let grammar = Grammar::from_yacc_lex(
            r#"
            %start start
            %token NUMBER
            %%
            start: NUMBER { Num(1) };
            "#,
            &format!("%%\n{regex} 'NUMBER'\n"),
        )
        .unwrap();
        let mut monitor = Monitor::new(
            &grammar,
            &format!(
                r#"
                (datatype Ast (Num i64))
                (let $root (Num {value}))
                "#
            ),
            "$root",
        )
        .unwrap();

        assert_eq!(monitor.realizability(), Some(true), "lexeme {lexeme:?}");
        assert_eq!(
            monitor.push_token_name("NUMBER", lexeme).unwrap(),
            Some(true),
            "lexeme {lexeme:?}"
        );
    }

    check(r"\+0+[0-9]+", 7, "+0007");
    check(r"-0+[0-9]+", -7, "-0007");
    check(r"-0+", 0, "-000");
    check(r"0{128}1", 1, &format!("{}1", "0".repeat(128)));
}

#[test]
fn merging_the_target_with_a_new_nested_tree_reaches_all_of_its_children() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID
        %%
        start: item { Outer(1) };
        item: ID { Var(1) };
        "#,
        "%%\n[a-z]+ 'ID'\n",
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Old) (Var String) (Outer Ast))
        (let $root (Old))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("ID", "y").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog("(union $root (Outer (Var \"y\")))")
            .unwrap(),
        Some(true)
    );
    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn a_late_recursive_rewrite_updates_the_current_and_future_prefixes() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X END
        %%
        start: X start { Step(2) }
             | END { Base() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Base) (Step Ast))
        (let $root (Base))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(monitor.push_token_name("X", "x").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog("(rewrite (Base) (Step (Base)))")
            .unwrap(),
        Some(true)
    );
    for _ in 0..4 {
        assert_eq!(monitor.push_token_name("X", "x").unwrap(), Some(true));
    }
}

#[test]
fn nonmonotone_egglog_commands_are_rejected() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let initial = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Leaf))
        (let $root (Leaf))
        (rule ((= x (Leaf))) ((delete (Leaf))))
        "#,
        "$root",
    );
    assert!(matches!(initial, Err(MonitorError::NonMonotoneUpdate(_))));

    let mut monitor = Monitor::new(
        &grammar,
        "(datatype Ast (Leaf)) (let $root (Leaf))",
        "$root",
    )
    .unwrap();
    for command in [
        "(delete (Leaf))",
        "(rewrite (Leaf) (Leaf) :subsume)",
        "(rule ((= x (Leaf))) ((set (Leaf) x)))",
    ] {
        assert!(
            matches!(
                monitor.run_egglog(command),
                Err(MonitorError::NonMonotoneUpdate(_))
            ),
            "command {command:?}"
        );
    }
}

#[test]
fn foreign_out_of_range_terminal_ids_return_an_error_instead_of_panicking() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token ONLY
        %%
        start: ONLY { Leaf() };
        "#,
    )
    .unwrap();
    let other = Grammar::from_yacc(
        r#"
        %start start
        %token FIRST SECOND
        %%
        start: FIRST { Leaf() }
             | SECOND { Leaf() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        "(datatype Ast (Leaf)) (let $root (Leaf))",
        "$root",
    )
    .unwrap();
    let foreign = other.terminal_by_name("SECOND").unwrap();

    assert!(matches!(
        monitor.push_lexeme(foreign, "second"),
        Err(MonitorError::InvalidTerminalId(_))
    ));
}

#[test]
fn grammar_actions_require_ranked_datatype_constructors() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: X { Table() };
        "#,
    )
    .unwrap();
    let result = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Root))
        (function Table () Ast :merge old)
        (let $root (Root))
        "#,
        "$root",
    );

    assert!(
        matches!(
            &result,
            Err(MonitorError::NonConstructorAction(name)) if name == "Table"
        ),
        "{:?}",
        result.as_ref().err()
    );
}
