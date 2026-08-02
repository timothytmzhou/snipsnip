use egglog::EGraph;
use prefixspace_web::DEFAULT_EGGLOG_PROGRAM;

const TYPING_RULES_MARKER: &str = ";; TypeScript typing rules";
const MAX_TEST_ROUNDS: usize = 12;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Classification {
    Accept,
    Reject,
}

fn equivalent(egraph: &mut EGraph, left: &str, right: &str) -> bool {
    let commands = egraph
        .parser
        .get_program_from_string(None, &format!("(check (= {left} {right}))"))
        .expect("equality check should parse");
    egraph.run_program(commands).is_ok()
}

fn classify(term: &str) -> Option<Classification> {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, DEFAULT_EGGLOG_PROGRAM)
        .expect("TypeScript Egglog program should load");
    egraph
        .parse_and_run_program(None, &format!("(let $case {term})"))
        .expect("concrete AST should load");

    for _ in 0..=MAX_TEST_ROUNDS {
        let accept = equivalent(&mut egraph, "$case", "(Accept)");
        let reject = equivalent(&mut egraph, "$case", "(Reject)");
        assert!(!(accept && reject), "Accept and Reject merged for {term}");
        if accept {
            return Some(Classification::Accept);
        }
        if reject {
            return Some(Classification::Reject);
        }
        egraph
            .step_rules("")
            .expect("TypeScript rules should execute");
    }
    None
}

#[test]
fn concrete_valid_ast_terms_rewrite_to_accept() {
    for term in [
        "(Analyze (LetDeclaration (NumberAnnotation) (NumberLiteral)))",
        "(Analyze (LetDeclaration (StringAnnotation) (Add (TrueLiteral) (StringLiteral))))",
        "(Analyze (LetDeclaration (NumberAnnotation) (Property (StringLiteral) \"length\")))",
        "(Analyze (LetDeclaration (BooleanAnnotation) (LessThan (TrueLiteral) (FalseLiteral))))",
        "(Analyze (LetDeclaration (NumberAnnotation) (Call (Identifier \"Number\") (Call (Identifier \"Number\") (NumberLiteral)))))",
    ] {
        assert_eq!(classify(term), Some(Classification::Accept), "{term}");
    }
}

#[test]
fn concrete_invalid_ast_terms_rewrite_to_reject() {
    for term in [
        "(Analyze (LetDeclaration (NumberAnnotation) (TrueLiteral)))",
        "(Analyze (LetDeclaration (BooleanAnnotation) (LessThan (NumberLiteral) (StringLiteral))))",
        "(Analyze (LetDeclaration (NumberAnnotation) (Property (NumberLiteral) \"length\")))",
        "(Analyze (LetDeclaration (NumberAnnotation) (Property (StringLiteral) \"missing\")))",
    ] {
        assert_eq!(classify(term), Some(Classification::Reject), "{term}");
    }
}

#[test]
fn expression_error_is_poison_through_enclosing_operators() {
    let term = concat!(
        "(Analyze (LetDeclaration (NumberAnnotation) ",
        "(Multiply (NumberLiteral) (Add (NumberLiteral) (TrueLiteral)))))"
    );
    assert_eq!(classify(term), Some(Classification::Reject));
}

#[test]
fn number_expression_has_a_recursive_call_representative() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, DEFAULT_EGGLOG_PROGRAM)
        .expect("TypeScript Egglog program should load");
    for _ in 0..=MAX_TEST_ROUNDS {
        if equivalent(
            &mut egraph,
            "(NumberExpression)",
            "(Call (NumberFunctionExpression) (NumberExpression))",
        ) {
            return;
        }
        egraph
            .step_rules("")
            .expect("TypeScript rules should execute");
    }
    panic!("NumberExpression did not acquire its recursive call representative");
}

#[test]
fn declarations_without_typing_rules_classify_nothing() {
    let declarations = DEFAULT_EGGLOG_PROGRAM
        .split_once(TYPING_RULES_MARKER)
        .expect("typing-rule marker should remain in the standalone program")
        .0;
    let term = "(Analyze (LetDeclaration (NumberAnnotation) (NumberLiteral)))";
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, declarations)
        .expect("TypeScript declarations should load without the typing rules");
    egraph
        .parse_and_run_program(None, &format!("(let $case {term})"))
        .expect("concrete AST should load");
    let report = egraph
        .step_rules("")
        .expect("an empty ruleset should be executable");

    assert!(!report.updated);
    assert!(!equivalent(&mut egraph, "$case", "(Accept)"));
    assert!(!equivalent(&mut egraph, "$case", "(Reject)"));
}
