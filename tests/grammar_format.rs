use prefixspace::{Action, Grammar, GrammarError, Symbol};

const YACC: &str = r#"
%start start
%token IDENT NUMBER EQ LET
%%
start: IDENT EQ NUMBER       { Assign() }
     | LET IDENT EQ NUMBER   { Let() }
     ;
"#;

const LEX: &str = r#"
%%
let                         'LET'
[A-Za-z_][A-Za-z0-9_]*      'IDENT'
[0-9]+                      'NUMBER'
=                           'EQ'
[ \t\r\n]+                  ;
"#;

#[test]
fn parses_yacc_actions_and_basic_lex_regexes() {
    let grammar = Grammar::from_yacc_lex(YACC, LEX).unwrap();
    assert_eq!(grammar.nonterminal_name(grammar.start()), "start");
    assert_eq!(grammar.productions().len(), 2);
    assert!(matches!(
        &grammar.productions()[0].action,
        Action::Construct {
            constructor,
            arguments
        } if constructor == "Assign" && arguments.is_empty()
    ));
    assert!(matches!(
        grammar.productions()[0].rhs[0],
        Symbol::Terminal(_)
    ));
}

#[test]
fn lexer_uses_longest_match_then_rule_priority_and_skips_ignores() {
    let grammar = Grammar::from_yacc_lex(YACC, LEX).unwrap();
    let tokens = grammar.lex("let answer = 123").unwrap();
    let names: Vec<_> = tokens
        .iter()
        .map(|token| grammar.terminal_name(token.kind))
        .collect();
    assert_eq!(names, ["LET", "IDENT", "EQ", "NUMBER"]);
    assert_eq!(tokens[1].lexeme, "answer");
    assert_eq!(tokens[3].lexeme, "123");
}

#[test]
fn rejects_non_linear_or_non_increasing_actions() {
    let duplicate = r#"
        %start s
        %token A
        %%
        s: child child { Pair(1, 1) };
        child: A { Leaf() };
    "#;
    let decreasing = r#"
        %start s
        %token A
        %%
        s: child child { Pair(2, 1) };
        child: A { Leaf() };
    "#;
    assert!(Grammar::from_yacc(duplicate).is_err());
    assert!(Grammar::from_yacc(decreasing).is_err());
}

#[test]
fn accepts_terminal_values_but_rejects_out_of_range_actions() {
    let terminal = r#"
        %start s
        %token A
        %%
        s: A { Bad(1) };
    "#;
    let out_of_range = r#"
        %start s
        %%
        s: child { Bad(2) };
        child: { Leaf() };
    "#;
    assert!(Grammar::from_yacc(terminal).is_ok());
    assert!(Grammar::from_yacc(out_of_range).is_err());
}

#[test]
fn rejects_nullable_lexer_rules() {
    let yacc = r#"
        %start s
        %token EMPTY
        %%
        s: EMPTY { Leaf() };
    "#;
    let lex = "%%\na* 'EMPTY'";
    assert!(Grammar::from_yacc_lex(yacc, lex).is_err());
}

#[test]
fn rejects_context_dependent_zero_width_lexer_rules() {
    let yacc = r#"
        %start s
        %token A
        %%
        s: A { Leaf() };
    "#;
    for lex in ["%%\n\\b 'A'", "%%\n\\b ;\na 'A'"] {
        let result = Grammar::from_yacc_lex(yacc, lex);
        assert!(
            matches!(
                &result,
                Err(GrammarError::NullableLexRule(rule)) if rule == "\\b"
            ),
            "unexpected result: {result:?}"
        );
    }
}

#[test]
fn distinguishes_missing_and_unused_lex_rules() {
    let yacc = r#"
        %start s
        %token A B
        %%
        s: A B { Pair() };
    "#;
    assert!(matches!(
        Grammar::from_yacc_lex(yacc, "%%\na 'A'"),
        Err(GrammarError::MissingLexRules(names)) if names == "B"
    ));

    let yacc = r#"
        %start s
        %token A
        %%
        s: A { Leaf() };
    "#;
    assert!(matches!(
        Grammar::from_yacc_lex(yacc, "%%\na 'A'\nc 'C'"),
        Err(GrammarError::UnusedLexRules(names)) if names == "C"
    ));
}

#[test]
fn matches_standard_lex_default_regex_flags_and_rejects_custom_flags() {
    let yacc = r#"
        %start s
        %token A
        %%
        s: A { Leaf() };
    "#;
    let octal = Grammar::from_yacc_lex(yacc, "%%\n\\141 'A'").unwrap();
    assert_eq!(octal.lex("a").unwrap().len(), 1);

    let dot_newline = Grammar::from_yacc_lex(yacc, "%%\n. 'A'").unwrap();
    assert_eq!(dot_newline.lex("\n").unwrap().len(), 1);

    let custom = "%grmtools { case_insensitive }\n%%\na 'A'";
    assert!(matches!(
        Grammar::from_yacc_lex(yacc, custom),
        Err(GrammarError::UnsupportedLexFeature(_))
    ));
}

#[test]
fn accepts_punctuated_egglog_constructor_symbols_in_actions() {
    let grammar = Grammar::from_yacc(
        r#"
        %start s
        %token A
        %%
        s: A { foo-bar/baz?() };
        "#,
    )
    .unwrap();
    assert_eq!(
        grammar.productions()[0].action.constructor(),
        Some("foo-bar/baz?")
    );
}

#[test]
fn lexer_memoizes_long_failed_maximal_munch_candidates() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start s
        %token A B
        %%
        s: A s { Cons(2) }
         | B   { Last() }
         ;
        "#,
        r#"
        %%
        a*b 'B'
        a   'A'
        "#,
    )
    .unwrap();
    let input = "a".repeat(50_000);
    let tokens = grammar.lex(&input).unwrap();
    assert_eq!(tokens.len(), input.len());
    assert!(
        tokens
            .iter()
            .all(|token| grammar.terminal_name(token.kind) == "A")
    );
}

#[test]
fn lexer_anchors_restart_at_each_token_boundary_like_lrlex() {
    let yacc = r#"
        %start s
        %token A
        %%
        s: A { Leaf() };
    "#;
    for anchored_rule in ["^a", r"\Aa", r"\ba"] {
        let lex = format!("%%\nx ;\n{anchored_rule} 'A'");
        let grammar = Grammar::from_yacc_lex(yacc, &lex).unwrap();
        let tokens = grammar.lex("xa").unwrap();
        assert_eq!(tokens.len(), 1, "rule {anchored_rule}");
        assert_eq!(grammar.terminal_name(tokens[0].kind), "A");
        assert_eq!((tokens[0].start, tokens[0].end), (1, 2));
    }

    let grammar = Grammar::from_yacc_lex(yacc, "%%\nx ;\n\\bβ 'A'").unwrap();
    let tokens = grammar.lex("xβ").unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].lexeme, "β");
    assert_eq!((tokens[0].start, tokens[0].end), (1, 3));
}

#[test]
fn ignored_rule_ids_never_collide_with_emitted_token_ids() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start s
        %token A
        %%
        s: A { Leaf() };
        "#,
        "%%\nx ;\na 'A'",
    )
    .unwrap();
    let tokens = grammar.lex("xa").unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].lexeme, "a");
    assert_eq!(grammar.terminal_name(tokens[0].kind), "A");
}

#[test]
fn lexer_preserves_ordered_alternation_and_lazy_quantifiers_within_rules() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start s
        %token A B C
        %%
        s: item s { Cons(2) }
         |          { Nil() }
         ;
        item: A { ANode() }
            | B { BNode() }
            | C { CNode() }
            ;
        "#,
        r#"
        %%
        a|ab 'A'
        b    'B'
        \bβ  'C'
        "#,
    )
    .unwrap();
    let ascii = grammar.lex("ab").unwrap();
    assert_eq!(
        ascii
            .iter()
            .map(|token| token.lexeme.as_str())
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    let unicode = grammar.lex("abβ").unwrap();
    assert_eq!(
        unicode
            .iter()
            .map(|token| token.lexeme.as_str())
            .collect::<Vec<_>>(),
        ["a", "b", "β"]
    );

    let lazy = Grammar::from_yacc_lex(
        r#"
        %start s
        %token A
        %%
        s: A s { Cons(2) }
         |     { Nil() }
         ;
        "#,
        "%%\na+? 'A'",
    )
    .unwrap();
    assert_eq!(lazy.lex("aaa").unwrap().len(), 3);
}
