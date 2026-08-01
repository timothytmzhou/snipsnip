use prefixspace::{
    DEFAULT_PREFIX_FOCUS_WORK_LIMIT, DEFAULT_UNREALIZABILITY_WORK_LIMIT, Grammar, LivePrefixMonitor,
};
use prefixspace_web::{
    DEFAULT_EGGLOG_PROGRAM, RealizabilityState, TYPESCRIPT_YACC, TypeScriptAnalyzer,
};

// Representative complete-lexeme adaptations of ChopChop's public
// TypeScript cases. The grammar below is independent: it produces syntax,
// while the editable Egglog program performs the primitive type analysis.

const NO_TYPING_RULES: &str = r#"
(datatype Expr
  (NumberLiteral)
  (StringLiteral)
  (TrueLiteral)
  (FalseLiteral)
  (Add Expr Expr)
  (Subtract Expr Expr)
  (Multiply Expr Expr)
  (Divide Expr Expr)
  (Modulo Expr Expr)
  (LessThan Expr Expr)
  (Property Expr String)
  (NumberExpression)
  (StringExpression)
  (BooleanExpression)
  (ExpressionError))
(datatype Annotation
  (NumberAnnotation)
  (StringAnnotation)
  (BooleanAnnotation))
(datatype Declaration
  (LetDeclaration Annotation Expr))
(datatype Goal
  (Analyze Declaration)
  (Accept)
  (Reject))
(relation GoalDisjoint (Goal Goal))
(GoalDisjoint (Reject) (Accept))
(let $required (Accept))
"#;

fn analyze(source: &str) -> prefixspace_web::AnalysisReport {
    TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM)
        .unwrap()
        .analyze(source)
        .unwrap()
}

#[test]
fn grammar_builds_syntax_and_the_program_visibly_contains_typing_rules() {
    for constructor in [
        "Analyze(1)",
        "LetDeclaration(4, 6)",
        "NumberLiteral()",
        "Add(1, 3)",
        "Property(1, 3)",
    ] {
        assert!(
            TYPESCRIPT_YACC.contains(constructor),
            "missing AST action {constructor}"
        );
    }
    assert!(!TYPESCRIPT_YACC.contains("{ Number() }"));
    assert!(DEFAULT_EGGLOG_PROGRAM.contains("TypeScript typing rules"));
    assert!(DEFAULT_EGGLOG_PROGRAM.contains("(rewrite"));
    assert!(DEFAULT_EGGLOG_PROGRAM.contains("(birewrite"));
}

#[test]
fn primitive_annotation_checks_require_egglog_typing() {
    for source in [
        "let answer: number = 42;",
        "let answer: string = \"hello\";",
        "let answer: string = 'hello';",
        r#"let answer: string = "say \"hello\"";"#,
        "let answer: boolean = true;",
    ] {
        assert_eq!(
            analyze(source).realizability,
            RealizabilityState::Realizable,
            "{source}"
        );
    }

    for source in [
        "let answer: number = true;",
        "let answer: string = 42;",
        "let answer: boolean = \"hello\";",
    ] {
        assert_eq!(
            analyze(source).realizability,
            RealizabilityState::Unrealizable,
            "{source}"
        );
    }
}

#[test]
fn operators_are_typed_compositionally() {
    for source in [
        "let answer: number = 5 + 16;",
        "let answer: number = 17 + 12 * 8;",
        "let answer: boolean = 17 + 12 * 8 < 114;",
        "let answer: boolean = true < false;",
        "let answer: string = \"count: \" + 5;",
        "let answer: string = 5 + \" items\";",
        "let answer: string = true + \"!\";",
        "let answer: number = \"hello\".length;",
        "let length: number = 1;",
        "let answer: number = 20 - 3 * 4 / 2 % 5;",
    ] {
        assert_eq!(
            analyze(source).realizability,
            RealizabilityState::Realizable,
            "{source}"
        );
    }

    for source in [
        "let answer: number = 5 + true;",
        "let answer: number = \"five\" + 1;",
        "let answer: number = (1).length;",
        "let answer: boolean = 1 < \"2\";",
        "let answer: number = false * 2;",
        "let answer: number = (5 + true) * 2;",
        "let answer: number = \"x\".missing;",
    ] {
        assert_eq!(
            analyze(source).realizability,
            RealizabilityState::Unrealizable,
            "{source}"
        );
    }
}

#[test]
fn an_open_operator_prefix_keeps_a_valid_completion() {
    let report = analyze("let answer: number = 5 +");
    assert_eq!(report.realizability, RealizabilityState::Realizable);
    assert_eq!(
        report.tokens.last().unwrap().realizability,
        RealizabilityState::Realizable
    );
}

#[test]
fn deleting_typing_rules_removes_both_positive_and_negative_semantic_proofs() {
    let mut without_rules = TypeScriptAnalyzer::new(NO_TYPING_RULES).unwrap();
    assert_eq!(
        without_rules
            .analyze("let answer: number = 42;")
            .unwrap()
            .realizability,
        RealizabilityState::Unknown
    );

    let mut without_rules = TypeScriptAnalyzer::new(NO_TYPING_RULES).unwrap();
    assert_eq!(
        without_rules
            .analyze("let answer: number = true;")
            .unwrap()
            .realizability,
        RealizabilityState::Unknown
    );
}

#[test]
fn deleting_one_literal_rule_changes_a_previously_valid_program_to_unknown() {
    let without_number_typing =
        DEFAULT_EGGLOG_PROGRAM.replace("(birewrite (NumberLiteral) (NumberExpression))", "");
    let mut analyzer = TypeScriptAnalyzer::new(without_number_typing).unwrap();
    assert_eq!(
        analyzer
            .analyze("let answer: number = 42;")
            .unwrap()
            .realizability,
        RealizabilityState::Unknown
    );
}

#[test]
fn syntax_failure_is_still_definitive_without_typing_rules() {
    let mut without_rules = TypeScriptAnalyzer::new(NO_TYPING_RULES).unwrap();
    assert_eq!(
        without_rules.analyze("let =").unwrap().realizability,
        RealizabilityState::Unrealizable
    );
}

#[test]
fn ordinary_typescript_tokens_do_not_hit_emergency_zipper_budgets() {
    let grammar = Grammar::from_yacc_lex(TYPESCRIPT_YACC, prefixspace_web::TYPESCRIPT_LEX).unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog_with_local_saturation_and_disjointness(
        &grammar,
        DEFAULT_EGGLOG_PROGRAM,
        "$required",
        "GoalDisjoint",
    )
    .unwrap();

    for token in grammar.lex("let answer: number = 5 + true;").unwrap() {
        monitor.push_token(&token).unwrap();
        let stats = monitor.stats();
        assert!(
            stats.last_prefix_focus_work < DEFAULT_PREFIX_FOCUS_WORK_LIMIT,
            "focus exhausted its emergency budget after {:?}: {stats:?}",
            token.lexeme
        );
        assert!(
            stats.last_prefix_output_work < DEFAULT_UNREALIZABILITY_WORK_LIMIT,
            "negative checking exhausted its emergency budget after {:?}: {stats:?}",
            token.lexeme
        );
    }
}
