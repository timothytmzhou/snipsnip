use prefixspace::{AutomatonError, RegularTreeGrammar};

const EGRAPH: &str = r#"
(datatype Ast
  (Leaf)
  (Bad)
  (Wrap Ast)
  (Pair Ast Ast))

(let $root (Leaf))
(union $root (Wrap (Leaf)))
(let $pair (Pair (Leaf) (Bad)))
"#;

#[test]
fn imports_egglog_eclasses_as_a_regular_tree_grammar() {
    let (automaton, root) = RegularTreeGrammar::from_egglog(EGRAPH, "$root").unwrap();
    let leaf = automaton
        .transitions()
        .iter()
        .find(|transition| transition.constructor == "Leaf")
        .unwrap();
    assert_eq!(leaf.output, root);
    assert!(automaton.transitions().iter().any(|transition| {
        transition.constructor == "Wrap"
            && transition.children == [root]
            && transition.output == root
    }));
}

#[test]
fn resolves_a_non_root_distinguished_binding() {
    let (automaton, pair) = RegularTreeGrammar::from_egglog(EGRAPH, "pair").unwrap();
    assert!(
        automaton
            .transitions()
            .iter()
            .any(|transition| transition.constructor == "Pair" && transition.output == pair)
    );
}

#[test]
fn reports_missing_bindings_and_invalid_programs() {
    assert!(RegularTreeGrammar::from_egglog(EGRAPH, "$missing").is_err());
    assert!(RegularTreeGrammar::from_egglog(EGRAPH, "(Leaf)").is_err());
    assert!(RegularTreeGrammar::from_egglog("(datatype", "$root").is_err());
}

#[test]
fn reports_hyphenated_equality_sort_names_without_panicking() {
    let result =
        RegularTreeGrammar::from_egglog("(datatype My-Ast (Leaf)) (let $root (Leaf))", "$root");
    assert!(matches!(
        result,
        Err(AutomatonError::UnsupportedSortName(name)) if name == "My-Ast"
    ));
}

#[test]
fn reports_an_irrelevant_hyphenated_sort_without_panicking() {
    let result = RegularTreeGrammar::from_egglog(
        r#"
        (datatype Ast (Good))
        (datatype My-Ast (Bad))
        (let $root (Good))
        (let $junk (Bad))
        "#,
        "$root",
    );
    assert!(result.is_err());
}

#[test]
fn accepts_egglog_global_names_with_symbol_punctuation() {
    let (automaton, root) = RegularTreeGrammar::from_egglog(
        "(datatype Ast (Leaf)) (let $root/value (Leaf))",
        "$root/value",
    )
    .unwrap();
    assert!(
        automaton
            .transitions()
            .iter()
            .any(|transition| transition.constructor == "Leaf" && transition.output == root)
    );
}
