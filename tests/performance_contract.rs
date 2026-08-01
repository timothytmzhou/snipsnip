use prefixspace::{Grammar, PrefixMonitor, PwzRecognizer, RegularTreeGrammar};

const COUNT: usize = 50_000;

fn list_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start start
        %token X
        %%
        start: items { List(1) };
        items: X items { Cons(2) }
             | { Nil() }
             ;
        "#,
    )
    .unwrap()
}

fn list_egraph() -> (RegularTreeGrammar, prefixspace::StateId) {
    RegularTreeGrammar::from_egglog(
        r#"
        (datatype Ast (List Ast) (Cons Ast) (Nil))
        (let $nil (Nil))
        (union $nil (Cons $nil))
        (let $root (List $nil))
        "#,
        "$root",
    )
    .unwrap()
}

#[test]
fn ll1_hot_path_has_linear_structural_work_and_constant_query_work() {
    let grammar = list_grammar();
    let (automaton, target) = list_egraph();
    let mut stream = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();

    for _ in 0..COUNT {
        assert!(!stream.push_token_name("X").unwrap());
    }

    let stats = stream.stats();
    assert_eq!(stats.derivatives, COUNT);
    assert_eq!(stats.cached_answers, COUNT + 1);
    assert!(
        stats.pwz_events <= COUNT * 20 + 64,
        "PwZ work was not linear: {stats:?}"
    );
    assert!(
        stats.memo_records <= COUNT * 8 + 64,
        "PwZ memory was not linear: {stats:?}"
    );
}

#[test]
fn monitored_and_vanilla_pwz_share_the_same_engine_contract() {
    let grammar = list_grammar();
    let mut vanilla = PwzRecognizer::compile(&grammar).unwrap();
    let x = grammar.terminal_by_name("X").unwrap();
    for _ in 0..COUNT {
        assert!(vanilla.push(x).unwrap());
    }
    let vanilla_stats = vanilla.stats();

    let (automaton, target) = list_egraph();
    let mut monitored = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
    for _ in 0..COUNT {
        assert!(!monitored.push_terminal(x).unwrap());
    }
    let monitored_stats = monitored.stats();

    // The product changes preprocessing constants, but not input-length complexity.
    assert!(vanilla_stats.events <= COUNT * 20 + 64);
    assert!(monitored_stats.pwz_events <= COUNT * 20 + 64);
    assert_eq!(monitored_stats.pwz_events, vanilla_stats.events);
    assert_eq!(monitored_stats.memo_records, vanilla_stats.memo_records);
}

#[test]
fn regex_text_path_streams_one_hundred_thousand_lexemes_linearly() {
    let grammar = Grammar::from_yacc_lex(
        r#"
        %start start
        %token X
        %%
        start: items { List(1) };
        items: X items { Cons(2) }
             | { Nil() }
             ;
        "#,
        r#"
        %%
        x    'X'
        [ ]+ ;
        "#,
    )
    .unwrap();
    let (automaton, target) = list_egraph();
    let mut monitored = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
    let input = "x ".repeat(100_000);
    let answers = monitored.push_complete_text(&input).unwrap();

    assert_eq!(answers.len(), 100_000);
    assert!(answers.iter().all(|is_empty| !is_empty));
    let stats = monitored.stats();
    assert_eq!(stats.derivatives, 100_000);
    assert!(stats.pwz_events <= 100_000 * 20 + 64);
}
