use prefixspace::{Grammar, Monitor, MonitorError, Token};

fn identifier_grammar() -> Grammar {
    Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID
        %%
        start: ID { Var(1) };
        "#,
        "%%\n[a-z]+ 'ID'\n",
    )
    .unwrap()
}

const PROGRAM: &str = r#"
    (datatype Ast (Var String))
    (let $root (Var "x"))
"#;

#[test]
fn new_constructs_a_monitor_and_realizability_queries_the_current_prefix() {
    let grammar = identifier_grammar();
    let monitor = Monitor::new(&grammar, PROGRAM, "$root").unwrap();

    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn every_push_method_returns_a_three_valued_answer() {
    let grammar = identifier_grammar();
    let id = grammar.terminal_by_name("ID").unwrap();

    let mut by_name = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert_eq!(by_name.push_token_name("ID", "x").unwrap(), Some(true));

    let mut by_token = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert_eq!(
        by_token
            .push_token(&Token {
                kind: id,
                lexeme: "x".to_owned(),
                start: 0,
                end: 1,
            })
            .unwrap(),
        Some(true)
    );

    let mut by_id = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert_eq!(by_id.push_lexeme(id, "x").unwrap(), Some(true));

    let mut complete_text = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert_eq!(
        complete_text.push_complete_text("x").unwrap(),
        vec![Some(true)]
    );

    let mut unknown = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert_eq!(unknown.push_token_name("ID", "y").unwrap(), None);
}

#[test]
fn run_egglog_applies_a_monotone_update_to_the_current_prefix() {
    let grammar = identifier_grammar();
    let mut monitor = Monitor::new(&grammar, PROGRAM, "$root").unwrap();

    assert_eq!(monitor.push_token_name("ID", "y").unwrap(), None);
    assert_eq!(
        monitor.run_egglog("(union $root (Var \"y\"))").unwrap(),
        Some(true)
    );
    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn conventional_disjoint_relation_can_prove_a_negative_answer() {
    let grammar = identifier_grammar();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Var String))
        (relation Disjoint (Ast Ast))
        (let $root (Var "x"))
        (Disjoint (Var "x") (Var "y"))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("ID", "y").unwrap(), Some(false));
}

#[test]
fn construction_and_lexeme_errors_remain_typed() {
    let grammar = identifier_grammar();
    assert!(matches!(
        Monitor::new(&grammar, PROGRAM, "$missing"),
        Err(MonitorError::InvalidBinding { .. })
    ));
    assert!(matches!(
        Monitor::new(
            &grammar,
            "(datatype Ast (Other)) (let $root (Other))",
            "$root"
        ),
        Err(MonitorError::MissingConstructor(name)) if name == "Var"
    ));

    let mut monitor = Monitor::new(&grammar, PROGRAM, "$root").unwrap();
    assert!(matches!(
        monitor.push_token_name("MISSING", "x"),
        Err(MonitorError::UnknownTerminal(name)) if name == "MISSING"
    ));
    assert!(matches!(
        monitor.push_token_name("ID", "123"),
        Err(MonitorError::LexemeMismatch { terminal, lexeme })
            if terminal == "ID" && lexeme == "123"
    ));
}

#[test]
fn failed_batch_lexing_does_not_partially_derive() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token ID STRING
        %%
        start: ID { Var(1) };
        "#,
        r#"%%
[a-z]+ 'ID'
\"[^\"]*\" 'STRING'
[ \t\r\n]+ ;
"#,
    )
    .unwrap();
    let mut monitor = Monitor::new(&grammar, PROGRAM, "$root").unwrap();

    assert!(monitor.push_complete_text("x \"").is_err());
    assert_eq!(
        monitor.push_token_name("ID", "x").unwrap(),
        Some(true),
        "the failed batch must not have advanced PwZ past the complete ID"
    );
}
