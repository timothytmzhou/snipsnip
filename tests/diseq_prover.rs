use prefixspace::{Grammar, LivePrefixMonitor};

const TYPE_LEX: &str = r#"
%%
number                      'NUMBER'
string                      'STRING'
boolean                     'BOOLEAN'
=>                          'ARROW'
\[                          'LBRACKET'
\]                          'RBRACKET'
[A-Za-z_][A-Za-z0-9_]*      'IDENT'
[ \t\r\n]+                  ;
"#;

const FREE_TYPES: &str = r#"
(datatype Type
  (Number)
  (StringType)
  (Boolean)
  (Named String)
  (Function Type Type)
  (Array Type))
(free Type TypeDisjoint)
"#;

fn monitor(yacc: &str, lex: &str, suffix: &str, target: &str) -> LivePrefixMonitor {
    let grammar = Grammar::from_yacc_lex(yacc, lex).unwrap();
    LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        &format!("{FREE_TYPES}\n{suffix}"),
        target,
        "TypeDisjoint",
    )
    .unwrap()
}

#[test]
fn free_constructor_mismatch_proves_unrealizable() {
    let mut monitor = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: NUMBER { Number() }
          | STRING { StringType() }
          ;
        "#,
        TYPE_LEX,
        "(let $target (Number))",
        "$target",
    );

    assert_eq!(monitor.realizability(), Some(true));
    assert!(monitor.push_token_name("STRING", "string").unwrap());
    assert_eq!(monitor.realizability(), Some(false));
}

#[test]
fn nested_function_mismatch_is_propagated_through_the_streaming_zipper() {
    let mut monitor = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: atom { $1 }
          | atom ARROW ty { Function(1, 3) }
          ;
        atom: NUMBER { Number() }
            | STRING { StringType() }
            ;
        "#,
        TYPE_LEX,
        "(let $target (Function (Number) (Function (Number) (Number))))",
        "$target",
    );

    let trace = [
        ("NUMBER", "number"),
        ("ARROW", "=>"),
        ("NUMBER", "number"),
        ("ARROW", "=>"),
    ];
    for (terminal, lexeme) in trace {
        monitor.push_token_name(terminal, lexeme).unwrap();
        assert_eq!(
            monitor.realizability(),
            Some(true),
            "after {terminal} {lexeme:?}"
        );
    }
    monitor.push_token_name("STRING", "string").unwrap();
    assert_eq!(monitor.realizability(), Some(false));
}

#[test]
fn free_constructor_fields_cover_arrays_and_primitive_names() {
    let mut array = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: atom LBRACKET RBRACKET { Array(1) };
        atom: NUMBER { Number() }
            | STRING { StringType() }
            ;
        "#,
        TYPE_LEX,
        "(let $target (Array (Number)))",
        "$target",
    );
    array.push_token_name("STRING", "string").unwrap();
    array.push_token_name("LBRACKET", "[").unwrap();
    array.push_token_name("RBRACKET", "]").unwrap();
    assert_eq!(array.realizability(), Some(false));

    let mut named = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: IDENT { Named(1) };
        "#,
        TYPE_LEX,
        "(let $target (Named \"User\"))",
        "$target",
    );
    named.push_token_name("IDENT", "Order").unwrap();
    assert_eq!(named.realizability(), Some(false));
}

#[test]
fn missing_negative_knowledge_is_unknown_not_unrealizable() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: NUMBER { Number() }
          | STRING { StringType() }
          ;
        "#,
        TYPE_LEX,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Number) (StringType))
        (relation TypeDisjoint (Type Type))
        (let $target (Number))
        "#,
        "$target",
        "TypeDisjoint",
    )
    .unwrap();

    monitor.push_token_name("STRING", "string").unwrap();
    assert!(monitor.intersection_is_empty());
    assert_eq!(monitor.realizability(), None);
}

#[test]
fn an_equality_witness_takes_precedence_over_negative_uncertainty() {
    let mut monitor = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: NUMBER { Number() }
          | STRING { StringType() }
          ;
        "#,
        TYPE_LEX,
        "(let $target (Number))",
        "$target",
    );
    monitor.push_token_name("NUMBER", "number").unwrap();
    assert!(!monitor.intersection_is_empty());
    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn syntax_death_is_definitively_unrealizable() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD
        %%
        start: GOOD { Number() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        &format!("{FREE_TYPES}\n(let $target (Number))"),
        "$target",
        "TypeDisjoint",
    )
    .unwrap();

    monitor.push_token_name("BAD", "bad").unwrap();
    assert_eq!(monitor.realizability(), Some(false));
}

#[test]
fn merging_a_free_disjoint_pair_triggers_the_invariant() {
    let mut monitor = monitor(
        r#"
        %start ty
        %token NUMBER STRING BOOLEAN ARROW LBRACKET RBRACKET IDENT
        %%
        ty: NUMBER { Number() };
        "#,
        TYPE_LEX,
        "(let $target (Number))",
        "$target",
    );

    let error = monitor
        .run_egglog("(union (Number) (StringType))")
        .unwrap_err();
    assert!(error.to_string().contains("disjoint"), "{error}");
}

// This is intentionally a small real-TypeScript rule, not ChopChop's custom
// typechecker: under `tsc --strict`, a value assigned to an annotated binding
// must be assignable to the annotation. These cases were checked against
// TypeScript 5.9.3. The semicolon is syntactically pending when the bad literal
// already makes every completion invalid.
#[test]
fn strict_typescript_annotated_initializer_becomes_unrealizable_early() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start declaration
        %token LET IDENT COLON NUMBER EQ NUM TRUE STRING_LITERAL SEMI
        %%
        declaration: LET IDENT COLON NUMBER EQ expression SEMI { $6 };
        expression: NUM            { Number() }
                  | TRUE           { Boolean() }
                  | STRING_LITERAL { StringType() }
                  ;
        "#,
        r#"
        %%
        let                         'LET'
        number                      'NUMBER'
        true                        'TRUE'
        [0-9]+                      'NUM'
        \"[^\"]*\"                  'STRING_LITERAL'
        [A-Za-z_][A-Za-z0-9_]*      'IDENT'
        :                           'COLON'
        =                           'EQ'
        ;                           'SEMI'
        [ \t\r\n]+                  ;
        "#,
    )
    .unwrap();
    let program = format!("{FREE_TYPES}\n(let $required (Number))");

    let mut valid = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        &program,
        "$required",
        "TypeDisjoint",
    )
    .unwrap();
    for (terminal, lexeme) in [
        ("LET", "let"),
        ("IDENT", "x"),
        ("COLON", ":"),
        ("NUMBER", "number"),
        ("EQ", "="),
        ("NUM", "1"),
    ] {
        valid.push_token_name(terminal, lexeme).unwrap();
        assert_eq!(valid.realizability(), Some(true));
    }

    let mut invalid = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        &program,
        "$required",
        "TypeDisjoint",
    )
    .unwrap();
    for (terminal, lexeme) in [
        ("LET", "let"),
        ("IDENT", "x"),
        ("COLON", ":"),
        ("NUMBER", "number"),
        ("EQ", "="),
    ] {
        invalid.push_token_name(terminal, lexeme).unwrap();
        assert_eq!(invalid.realizability(), Some(true));
    }
    invalid.push_token_name("TRUE", "true").unwrap();
    assert_eq!(invalid.realizability(), Some(false));
}

#[test]
fn completed_prefix_tree_is_automatically_run_through_local_eqsat() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD TAIL END
        %%
        start: atom TAIL END { $1 };
        atom: BAD { Bad() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $wanted (Good))
        "#,
        "$wanted",
    )
    .unwrap();
    monitor
        .add_managed_rewrites("(rewrite (Bad) (Good))")
        .unwrap();

    // BAD fixes the projected AST even though TAIL END is still pending. The
    // monitor reconstructs that zipper root, focuses it, and runs the rule.
    assert!(!monitor.push_token_name("BAD", "bad").unwrap());
    assert_eq!(monitor.realizability(), Some(true));
    // The proof remains cached as the surrounding syntax advances.
    assert!(!monitor.push_token_name("TAIL", "tail").unwrap());
    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn analyzed_fixed_error_proves_the_unfinished_prefix_unrealizable() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token ONE DOT LENGTH TAIL END
        %%
        start: access TAIL END { $1 };
        access: ONE DOT LENGTH { BadLength() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Valid) (Error) (BadLength))
        (relation TypeDisjoint (Type Type))
        (TypeDisjoint (Error) (Valid))
        (let $wanted (Valid))
        "#,
        "$wanted",
        "TypeDisjoint",
    )
    .unwrap();
    monitor
        .add_managed_rewrites("(rewrite (BadLength) (Error))")
        .unwrap();

    for (terminal, lexeme) in [("ONE", "1"), ("DOT", "."), ("LENGTH", "length")] {
        monitor.push_token_name(terminal, lexeme).unwrap();
    }
    assert_eq!(monitor.realizability(), Some(false));

    // TAIL completes the selected access subtree, but END is still missing.
    // The same proof remains valid when the zipper switches from a known
    // enclosing action to a completed fixed tree.
    monitor.push_token_name("TAIL", "tail").unwrap();
    assert_eq!(monitor.realizability(), Some(false));
}

#[test]
fn malformed_disjoint_relation_is_rejected() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token NUMBER
        %%
        ty: NUMBER { Number() };
        "#,
    )
    .unwrap();
    let error = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Number))
        (relation Wrong (Type))
        (let $wanted (Number))
        "#,
        "$wanted",
        "Wrong",
    )
    .err()
    .expect("wrong relation schema must be rejected");
    assert!(error.to_string().contains("must have signature"), "{error}");
}

#[test]
fn manual_disjoint_relation_also_enforces_irreflexivity() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token NUMBER
        %%
        ty: NUMBER { Number() };
        "#,
    )
    .unwrap();
    let error = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Number))
        (relation D (Type Type))
        (D (Number) (Number))
        (let $wanted (Number))
        "#,
        "$wanted",
        "D",
    )
    .err()
    .expect("a reflexive disjoint pair must be rejected");
    assert!(error.to_string().contains("equal pair"), "{error}");
}

#[test]
fn explicit_disjoint_proof_survives_unrelated_representative_changes() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token ERROR
        %%
        ty: ERROR { Error() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
        &grammar,
        r#"
        (datatype Type (Valid) (Error) (ValidAlias) (ErrorAlias))
        (relation D (Type Type))
        (D (Error) (Valid))
        (let $wanted (Valid))
        "#,
        "$wanted",
        "D",
    )
    .unwrap();

    monitor.push_token_name("ERROR", "error").unwrap();
    assert_eq!(monitor.realizability(), Some(false));
    monitor
        .run_egglog("(union (ErrorAlias) (Error)) (union (ValidAlias) (Valid))")
        .unwrap();
    assert_eq!(monitor.realizability(), Some(false));
}
