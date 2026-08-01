use prefixspace::{Grammar, PrefixMonitor, RegularTreeGrammar};

#[test]
fn deep_300_state_egraph_and_301_rule_grammar_stream_end_to_end() {
    const DEPTH: usize = 300;

    let mut yacc = String::from("%start n0\n%token");
    for index in 0..DEPTH {
        yacc.push_str(&format!(" T{index}"));
    }
    yacc.push_str(" END\n%%\n");
    for index in 0..DEPTH {
        yacc.push_str(&format!(
            "n{index}: T{index} n{} {{ C{index}(2) }};\n",
            index + 1
        ));
    }
    yacc.push_str(&format!("n{DEPTH}: END {{ Leaf() }};\n"));

    let mut egglog = String::from("(datatype Ast (Leaf)");
    for index in 0..DEPTH {
        egglog.push_str(&format!(" (C{index} Ast)"));
    }
    egglog.push_str(")\n");
    egglog.push_str(&format!("(let $q{DEPTH} (Leaf))\n"));
    for index in (0..DEPTH).rev() {
        egglog.push_str(&format!("(let $q{index} (C{index} $q{}))\n", index + 1));
    }
    egglog.push_str("(let $root $q0)\n");

    let grammar = Grammar::from_yacc(&yacc).unwrap();
    let (tree_grammar, root) = RegularTreeGrammar::from_egglog(&egglog, "$root").unwrap();
    assert_eq!(tree_grammar.state_count(), DEPTH + 1);
    assert_eq!(tree_grammar.transitions().len(), DEPTH + 1);

    let mut monitor = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
    for index in 0..DEPTH {
        assert!(
            !monitor.push_token_name(&format!("T{index}")).unwrap(),
            "lost the unique completion at depth {index}"
        );
    }
    assert!(!monitor.push_token_name("END").unwrap());
    assert_eq!(monitor.stats().derivatives, DEPTH + 1);
}

#[test]
fn wide_recursive_eclass_and_grammar_remain_linear_for_a_long_stream() {
    const WIDTH: usize = 128;
    const TOKENS: usize = 100_000;

    let mut yacc = String::from("%start start\n%token END");
    for index in 0..WIDTH {
        yacc.push_str(&format!(" K{index}"));
    }
    yacc.push_str("\n%%\nstart:\n");
    for index in 0..WIDTH {
        let separator = if index == 0 { "  " } else { "| " };
        yacc.push_str(&format!("{separator}K{index} start {{ C{index}(2) }}\n"));
    }
    yacc.push_str("| END { Leaf() }\n;\n");

    let mut egglog = String::from("(datatype Ast (Leaf)");
    for index in 0..WIDTH {
        egglog.push_str(&format!(" (C{index} Ast)"));
    }
    egglog.push_str(")\n(let $root (Leaf))\n");
    for index in 0..WIDTH {
        egglog.push_str(&format!("(union $root (C{index} $root))\n"));
    }

    let grammar = Grammar::from_yacc(&yacc).unwrap();
    let (tree_grammar, root) = RegularTreeGrammar::from_egglog(&egglog, "$root").unwrap();
    assert_eq!(tree_grammar.state_count(), 1);
    assert_eq!(tree_grammar.transitions().len(), WIDTH + 1);

    let mut monitor = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
    let terminals = (0..WIDTH)
        .map(|index| grammar.terminal_by_name(&format!("K{index}")).unwrap())
        .collect::<Vec<_>>();
    for index in 0..TOKENS {
        assert!(!monitor.push_terminal(terminals[index % WIDTH]).unwrap());
    }
    assert!(!monitor.push_token_name("END").unwrap());

    let stats = monitor.stats();
    assert_eq!(stats.derivatives, TOKENS + 1);
    assert_eq!(stats.cached_answers, TOKENS + 2);
    assert!(
        stats.pwz_events <= TOKENS * 20 + WIDTH * 8,
        "wide SELECT dispatch lost linear behavior: {stats:?}"
    );
}

#[test]
fn two_thousand_unreachable_eclasses_are_removed_before_monitoring() {
    const JUNK_CLASSES: usize = 2_000;

    let mut egglog = String::from(
        "(datatype Ast (Good) (Junk Ast))\n\
         (let $root (Good))\n\
         (let $junk0 (Junk (Good)))\n",
    );
    for index in 1..JUNK_CLASSES {
        egglog.push_str(&format!("(let $junk{index} (Junk $junk{}))\n", index - 1));
    }

    let (tree_grammar, root) = RegularTreeGrammar::from_egglog(&egglog, "$root").unwrap();
    assert_eq!(tree_grammar.state_count(), 1);
    assert_eq!(tree_grammar.transitions().len(), 1);

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
    let mut monitor = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
    assert!(!monitor.push_token_name("GOOD").unwrap());

    let mut rejected = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
    assert!(rejected.push_token_name("BAD").unwrap());
}

#[test]
fn rows_256_for_one_constructor_dispatch_by_child_state() {
    const ROWS: usize = 256;

    let mut yacc = String::from("%start start\n%token");
    for index in 0..ROWS {
        yacc.push_str(&format!(" K{index}"));
    }
    yacc.push_str("\n%%\nstart: leaf leaf { Pair(1, 2) };\nleaf:\n");
    for index in 0..ROWS {
        let separator = if index == 0 { "  " } else { "| " };
        yacc.push_str(&format!("{separator}K{index} {{ Leaf{index}() }}\n"));
    }
    yacc.push_str(";\n");

    let mut egglog = String::from("(datatype Ast (Pair Ast Ast)");
    for index in 0..ROWS {
        egglog.push_str(&format!(" (Leaf{index})"));
    }
    egglog.push_str(")\n(let $root (Pair (Leaf0) (Leaf0)))\n");
    for index in 1..ROWS {
        egglog.push_str(&format!(
            "(union $root (Pair (Leaf{index}) (Leaf{index})))\n"
        ));
    }

    let grammar = Grammar::from_yacc(&yacc).unwrap();
    let (tree_grammar, root) = RegularTreeGrammar::from_egglog(&egglog, "$root").unwrap();
    assert_eq!(tree_grammar.state_count(), ROWS + 1);
    assert_eq!(tree_grammar.transitions().len(), ROWS * 2);

    for selected in [0, ROWS / 2, ROWS - 1] {
        let token = format!("K{selected}");
        let mut accepted = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
        assert!(!accepted.push_token_name(&token).unwrap());
        assert!(!accepted.push_token_name(&token).unwrap());

        let mut rejected = PrefixMonitor::compile(&grammar, &tree_grammar, root).unwrap();
        assert!(!rejected.push_token_name(&token).unwrap());
        assert!(
            rejected
                .push_token_name(&format!("K{}", (selected + 1) % ROWS))
                .unwrap()
        );
    }
}
