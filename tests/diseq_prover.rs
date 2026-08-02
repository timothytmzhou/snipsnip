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
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token STRING
        %%
        ty: STRING { StringType() };
        "#,
    )
    .unwrap();
    let program =
        format!("{TYPE_DECLARATIONS}\n(Disjoint (StringType) (Number))\n(let $target (Number))");
    let mut monitor = Monitor::new(&grammar, &program, "$target").unwrap();

    assert_eq!(
        monitor.push_token_name("STRING", "string").unwrap(),
        Some(false)
    );
}

#[test]
fn disjoint_facts_are_read_in_either_order() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token STRING
        %%
        ty: STRING { StringType() };
        "#,
    )
    .unwrap();
    let program =
        format!("{TYPE_DECLARATIONS}\n(Disjoint (Number) (StringType))\n(let $target (Number))");
    let mut monitor = Monitor::new(&grammar, &program, "$target").unwrap();

    assert_eq!(
        monitor.push_token_name("STRING", "string").unwrap(),
        Some(false)
    );
}

#[test]
fn one_disjoint_completion_does_not_hide_other_possible_completions() {
    let mut monitor = type_monitor("(Disjoint (StringType) (Number))", "(Number)");

    assert_eq!(monitor.push_token_name("STRING", "string").unwrap(), None);
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
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Type (Number) (StringType))
        (let $target (Number))
        "#,
        "$target",
    )
    .unwrap();

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

#[test]
fn every_ambiguous_output_needs_its_own_disjoint_proof() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token VALUE
        %%
        ty: VALUE { StringType() }
          | VALUE { Boolean() }
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

    assert_eq!(monitor.push_token_name("VALUE", "value").unwrap(), None);
}

#[test]
fn a_recursive_continuation_is_unknown_until_its_whole_output_is_fixed() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X END
        %%
        start: X start { Wrap(2) }
             | END     { Base() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Result (Target) (Base) (Wrap Result))
        (relation Disjoint (Result Result))
        (Disjoint (Wrap (Base)) (Target))
        (let $target (Target))
        "#,
        "$target",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("X", "x").unwrap(), None);
    assert_eq!(monitor.push_token_name("END", "end").unwrap(), Some(false));
}

#[test]
fn a_late_disjoint_fact_updates_the_current_prefix() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token STRING
        %%
        ty: STRING { StringType() };
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Type (Number) (StringType))
        (let $target (Number))
        "#,
        "$target",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("STRING", "string").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog("(relation Disjoint (Type Type)) (Disjoint (StringType) (Number))",)
            .unwrap(),
        Some(false)
    );
}

#[test]
fn a_positive_prefix_still_records_every_fixed_ambiguous_branch() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token X B C
        %%
        start: atom suffix { Whole(1, 2) };
        atom: X { A() }
            | X { Z() }
            ;
        suffix: B { C1() }
              | C { C2() }
              ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (A) (Z) (C1) (C2) (Whole Ast Ast))
        (relation Disjoint (Ast Ast))
        (let $target (Whole (A) (C1)))
        (Disjoint (Whole (A) (C2)) $target)
        "#,
        "$target",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("X", "x").unwrap(), Some(true));
    assert_eq!(
        monitor
            .run_egglog("(rewrite (Whole (Z) (C2)) $target)")
            .unwrap(),
        Some(true)
    );
    assert_eq!(monitor.push_token_name("C", "c").unwrap(), Some(true));
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
fn an_existing_disjoint_proof_does_not_run_unneeded_productive_rules() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD BAD
        %%
        start: GOOD { Good() }
             | BAD  { Bad() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Result (Good) (Bad))
        (relation Disjoint (Result Result))
        (relation Next (i64))
        (Next 0)
        (rule ((Next n)) ((Next (+ n 1))))
        (Disjoint (Bad) (Good))
        (let $target (Good))
        "#,
        "$target",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("BAD", "bad").unwrap(), Some(false));
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
fn a_constructor_named_disjoint_is_not_a_proof_relation() {
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
        (datatype Type (Number) (Disjoint Type Type))
        (let $target (Number))
        "#,
        "$target",
    )
    .err()
    .expect("a datatype constructor is not a relation");

    assert!(error.to_string().contains("signature"), "{error}");
}

#[test]
fn a_failed_relation_declaration_does_not_bless_an_existing_constructor() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token STRING
        %%
        ty: STRING { StringType() };
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Type (Number) (StringType))
        (let $target (Number))
        "#,
        "$target",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("STRING", "string").unwrap(), None);
    let error = monitor
        .run_egglog(
            r#"
            (datatype Proof (Disjoint Type Type))
            (Disjoint (StringType) (Number))
            (relation Disjoint (Type Type))
            "#,
        )
        .unwrap_err();

    assert!(error.to_string().contains("Disjoint"), "{error}");
    assert_eq!(monitor.realizability(), None);
}

#[test]
fn a_primitive_output_constructor_named_disjoint_is_not_a_relation() {
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
        (constructor Disjoint (Type Type) i64)
        (let $target (Number))
        "#,
        "$target",
    )
    .err()
    .expect("a constructor with a primitive output is not a relation");

    assert!(
        error.to_string().contains("signature")
            || error.to_string().contains("output type of constructor"),
        "{error}"
    );
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

#[test]
fn a_late_union_cannot_make_a_disjoint_pair_equal() {
    let grammar = Grammar::from_yacc(
        r#"
        %start ty
        %token STRING
        %%
        ty: STRING { StringType() };
        "#,
    )
    .unwrap();
    let program =
        format!("{TYPE_DECLARATIONS}\n(Disjoint (StringType) (Number))\n(let $target (Number))");
    let mut monitor = Monitor::new(&grammar, &program, "$target").unwrap();

    let error = monitor
        .run_egglog("(union (StringType) (Number))")
        .unwrap_err();
    assert!(error.to_string().contains("irreflexive"), "{error}");
}
