use prefixspace::{Grammar, PrefixMonitor, RegularTreeGrammar};

fn monitor(grammar: &str, egraph: &str, root: &str) -> PrefixMonitor {
    let grammar = Grammar::from_yacc(grammar).unwrap();
    let (automaton, target) = RegularTreeGrammar::from_egglog(egraph, root).unwrap();
    PrefixMonitor::compile(&grammar, &automaton, target).unwrap()
}

const AST_EGRAPH: &str = r#"
(datatype Ast
  (Good)
  (Bad)
  (Keep Ast)
  (Pair Ast Ast))
(let $good (Good))
(let $kept (Keep (Good)))
(let $pair (Pair (Good) (Bad)))
"#;

#[test]
fn reports_nonempty_exactly_while_a_target_completion_exists() {
    let grammar = r#"
        %start start
        %token A B C
        %%
        start: A B { Good() }
             | A C { Bad() }
             ;
    "#;
    let mut stream = monitor(grammar, AST_EGRAPH, "$good");

    assert!(!stream.intersection_is_empty());
    assert!(!stream.push_token_name("A").unwrap());
    assert!(stream.has_completion());
    assert!(!stream.push_token_name("B").unwrap());
    assert!(!stream.intersection_is_empty());
    assert!(stream.push_token_name("C").unwrap());
    assert!(stream.intersection_is_empty());
}

#[test]
fn filters_on_selected_child_eclasses() {
    let grammar = r#"
        %start start
        %token G B
        %%
        start: left right { Pair(1, 2) };
        left: G { Good() }
            | B { Bad() }
            ;
        right: G { Good() }
             | B { Bad() }
             ;
    "#;

    let mut accepted = monitor(grammar, AST_EGRAPH, "$pair");
    assert!(!accepted.push_token_name("G").unwrap());
    assert!(!accepted.push_token_name("B").unwrap());

    let mut rejected = monitor(grammar, AST_EGRAPH, "$pair");
    assert!(rejected.push_token_name("B").unwrap());
}

#[test]
fn unselected_children_are_semantically_ignored() {
    let grammar = r#"
        %start start
        %token G B X Y
        %%
        start: value junk { Keep(1) };
        value: G { Good() }
             | B { Bad() }
             ;
        junk: X { Bad() }
            | Y { Good() }
            ;
    "#;

    for suffix in ["X", "Y"] {
        let mut stream = monitor(grammar, AST_EGRAPH, "$kept");
        assert!(!stream.push_token_name("G").unwrap());
        assert!(!stream.push_token_name(suffix).unwrap());
    }
}

#[test]
fn supports_epsilon_productions() {
    let grammar = r#"
        %start start
        %%
        start: { Good() };
    "#;
    let mut stream = monitor(grammar, AST_EGRAPH, "$good");
    assert!(!stream.intersection_is_empty());
    assert!(stream.push_token_name("anything").is_err());
}

#[test]
fn supports_left_recursion_and_recursive_eclasses() {
    let grammar = r#"
        %start start
        %token X Z
        %%
        start: X start { Wrap(2) }
             | Z { Leaf() }
             ;
    "#;
    let egraph = r#"
        (datatype Ast (Leaf) (Wrap Ast))
        (let $root (Leaf))
        (union $root (Wrap $root))
    "#;
    let mut stream = monitor(grammar, egraph, "$root");
    for _ in 0..128 {
        assert!(!stream.push_token_name("X").unwrap());
    }
    assert!(!stream.push_token_name("Z").unwrap());
}

#[test]
fn dead_prefix_is_absorbing() {
    let grammar = r#"
        %start start
        %token A B
        %%
        start: A { Good() };
    "#;
    let mut stream = monitor(grammar, AST_EGRAPH, "$good");
    assert!(stream.push_token_name("\"not-declared\"").is_err());
    assert!(stream.push_token_name("B").unwrap());
    assert!(stream.push_token_name("B").unwrap());
    assert_eq!(stream.stats().derivatives, 1);
    assert_eq!(stream.stats().cached_answers, 2);
}

#[test]
fn text_frontend_uses_regex_lexemes() {
    let grammar = r#"
        %start start
        %token WORD BANG
        %%
        start: WORD BANG { Good() };
    "#;
    let lexer = r#"
        %%
        [a-z]+     'WORD'
        !          'BANG'
        [ \t\n]+   ;
    "#;
    let grammar = Grammar::from_yacc_lex(grammar, lexer).unwrap();
    let (automaton, target) = RegularTreeGrammar::from_egglog(AST_EGRAPH, "$good").unwrap();
    let mut stream = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
    let answers = stream.push_complete_text("hello !").unwrap();
    assert_eq!(answers, [false, false]);
}

#[test]
fn punctuated_action_constructor_matches_egglog_constructor() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A
        %%
        start: A { good-node() };
        "#,
    )
    .unwrap();
    let (automaton, target) = RegularTreeGrammar::from_egglog(
        "(datatype Ast (good-node)) (let $root/value (good-node))",
        "$root/value",
    )
    .unwrap();
    let mut stream = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
    assert!(!stream.push_token_name("A").unwrap());
}
