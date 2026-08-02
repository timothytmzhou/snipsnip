use prefixspace::{Grammar, Monitor};

const TYPE_GRAMMAR: &str = r#"
%start ty
%token NUMBER STRING ARROW
%%
ty: atom                         { $1 }
  | atom ARROW atom              { Function(1, 3) }
  ;
atom: NUMBER                     { Number() }
    | STRING                     { StringType() }
    ;
"#;

const TYPE_LEX: &str = r#"
%%
number                           'NUMBER'
string                           'STRING'
=>                               'ARROW'
[ \t\r\n]+                       ;
"#;

const TYPE_DECLARATIONS: &str = r#"
(datatype Type
  (Number)
  (StringType)
  (Boolean)
  (Array Type)
  (Function Type Type)
  (Error))
(relation Disjoint (Type Type))
"#;

fn type_monitor(disjoint_facts: &str, target: &str) -> Monitor {
    let grammar = Grammar::from_yacc_lex(TYPE_GRAMMAR, TYPE_LEX).unwrap();
    let program = format!("{TYPE_DECLARATIONS}\n{disjoint_facts}\n(let $target {target})");
    Monitor::new(&grammar, &program, "$target").unwrap()
}

#[test]
fn explicit_disjoint_fact_proves_a_concrete_type_unrealizable() {
    let mut monitor = type_monitor("(Disjoint (StringType) (Number))", "(Number)");

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(
        monitor.push_token_name("STRING", "string").unwrap(),
        Some(false)
    );
}

#[test]
fn explicit_disjoint_fact_can_describe_nested_type_constructors() {
    let mut monitor = type_monitor(
        r#"
        (Disjoint
          (Function (Number) (StringType))
          (Function (Number) (Number)))
        "#,
        "(Function (Number) (Number))",
    );

    assert_eq!(
        monitor.push_token_name("NUMBER", "number").unwrap(),
        Some(true)
    );
    assert_eq!(monitor.push_token_name("ARROW", "=>").unwrap(), Some(true));
    assert_eq!(
        monitor.push_token_name("STRING", "string").unwrap(),
        Some(false)
    );
}

#[test]
fn absence_of_a_disjointness_proof_is_unknown() {
    let mut monitor = type_monitor("", "(Number)");

    assert_eq!(monitor.push_token_name("STRING", "string").unwrap(), None);
}

#[test]
fn syntactically_dead_prefix_is_definitively_unrealizable() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD
        %%
        start: GOOD { Number() };
        "#,
    )
    .unwrap();
    let program = format!("{TYPE_DECLARATIONS}\n(let $target (Number))");
    let mut monitor = Monitor::new(&grammar, &program, "$target").unwrap();

    assert_eq!(monitor.push_token_name("BAD", "bad").unwrap(), Some(false));
}

#[test]
fn an_equal_completion_wins_when_an_ambiguous_parse_is_also_disjoint() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token VALUE
        %%
        ty: VALUE { Number() }
          | VALUE { StringType() }
          ;
        "#,
    )
    .unwrap();
    let program = format!(
        r#"
        {TYPE_DECLARATIONS}
        (Disjoint (StringType) (Number))
        (let $target (Number))
        "#
    );
    let mut monitor = Monitor::new(&grammar, &program, "$target").unwrap();

    assert_eq!(
        monitor.push_token_name("VALUE", "value").unwrap(),
        Some(true)
    );
}

fn locally_rewritten_monitor() -> Monitor {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD TAIL
        %%
        start: atom TAIL { $1 };
        atom: GOOD { GoodSyntax() }
            | BAD  { BadSyntax() }
            ;
        "#,
    )
    .unwrap();
    Monitor::new(
        &grammar,
        r#"
        (datatype Result
          (Wanted)
          (GoodSyntax)
          (BadSyntax)
          (Error))
        (relation Disjoint (Result Result))
        (Disjoint (Error) (Wanted))
        (let $target (Wanted))

        (birewrite (GoodSyntax) (Wanted))
        (rewrite (BadSyntax) (Error))
        "#,
        "$target",
    )
    .unwrap()
}

#[test]
fn initial_rewrites_are_run_locally_before_the_parse_is_complete() {
    let mut valid = locally_rewritten_monitor();
    assert_eq!(valid.push_token_name("GOOD", "good").unwrap(), Some(true));

    let mut invalid = locally_rewritten_monitor();
    assert_eq!(invalid.push_token_name("BAD", "bad").unwrap(), Some(false));

    assert_eq!(
        invalid.push_token_name("TAIL", "tail").unwrap(),
        Some(false)
    );
}

#[test]
fn disjoint_relation_must_have_the_target_sort_twice() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token NUMBER
        %%
        ty: NUMBER { Number() };
        "#,
    )
    .unwrap();
    let error = Monitor::new(
        &grammar,
        r#"
        (datatype Type (Number))
        (relation Disjoint (Type))
        (let $target (Number))
        "#,
        "$target",
    )
    .err()
    .expect("an invalid Disjoint relation must be rejected");

    assert!(error.to_string().contains("signature"), "{error}");
}

#[test]
fn disjoint_relation_is_irreflexive() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token NUMBER
        %%
        ty: NUMBER { Number() };
        "#,
    )
    .unwrap();
    let error = Monitor::new(
        &grammar,
        r#"
        (datatype Type (Number))
        (relation Disjoint (Type Type))
        (Disjoint (Number) (Number))
        (let $target (Number))
        "#,
        "$target",
    )
    .err()
    .expect("Disjoint(x, x) must be rejected");
    let message = error.to_string().to_lowercase();

    assert!(
        message.contains("disjoint")
            && (message.contains("equal") || message.contains("irreflexive")),
        "{error}"
    );
}
