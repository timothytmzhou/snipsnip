use prefixspace::{Grammar, Monitor};

fn grammar_with_action(action: &str) -> Grammar {
    Grammar::from_yacc(&format!(
        r#"
        %start start
        %token TOKEN
        %%
        start: TOKEN {{ {action} }};
        "#
    ))
    .unwrap()
}

fn numbered_state_grammar(alternative: bool) -> Grammar {
    let alternative = alternative.then_some("| NUMBER { Bad() }").unwrap_or("");
    Grammar::from_yacc_lex(
        &format!(
            r#"
            %start start
            %token NUMBER
            %%
            start: NUMBER {{ State(1) }}
                 {alternative}
                 ;
            "#
        ),
        "%%\n[0-9]+ 'NUMBER'\n",
    )
    .unwrap()
}

fn state_program(goal: i64, target: &str, extra: &str) -> String {
    format!(
        r#"
        (datatype Ast (State i64) (Bad) (Wrap Ast))
        (relation Disjoint (Ast Ast))
        {extra}
        (let $root {target})
        (rewrite (State n) (State (+ n 1)) :when ((< n {goal})))
        "#
    )
}

fn deeply_wrapped_state_grammar(depth: usize, number_pattern: &str) -> Grammar {
    let mut source = String::from("%start layer0\n%token NUMBER\n%%\n");
    for layer in 0..depth {
        source.push_str(&format!(
            "layer{layer}: layer{} {{ Wrap(1) }};\n",
            layer + 1
        ));
    }
    source.push_str(&format!("layer{depth}: NUMBER {{ State(1) }};\n"));
    Grammar::from_yacc_lex(&source, &format!("%%\n{number_pattern} 'NUMBER'\n")).unwrap()
}

fn wrap(term: &str, depth: usize) -> String {
    let mut result = String::with_capacity(term.len() + depth * 7);
    for _ in 0..depth {
        result.push_str("(Wrap ");
    }
    result.push_str(term);
    for _ in 0..depth {
        result.push(')');
    }
    result
}

#[test]
fn initial_rewrite_applies_to_a_later_prefix() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        (rewrite (Bad) (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(
        monitor.push_token_name("TOKEN", "token").unwrap(),
        Some(true)
    );
}

#[test]
fn late_rewrite_reconsiders_the_current_prefix() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        "(datatype Ast (Good) (Bad)) (let $root (Good))",
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
    assert_eq!(
        monitor.run_egglog("(rewrite (Bad) (Good))").unwrap(),
        Some(true)
    );
}

#[test]
fn forward_rewrites_do_not_run_backwards() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Middle))
        (let $root (Good))
        (rewrite (Middle) (Bad))
        (rewrite (Middle) (Good))
        "#,
        "$root",
    )
    .unwrap();

    // Running the first rule backwards would create Middle(), after which the
    // second rule would incorrectly connect this prefix to Good().
    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
}

#[test]
fn birewrite_works_in_both_directions() {
    for (candidate, bridge) in [
        ("Left()", "(rewrite (Right) (Goal))"),
        ("Right()", "(rewrite (Left) (Goal))"),
    ] {
        let grammar = grammar_with_action(candidate);
        let program = format!(
            r#"
            (datatype Ast (Goal) (Left) (Right))
            (let $root (Goal))
            (birewrite (Left) (Right))
            {bridge}
            "#
        );
        let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

        assert_eq!(
            monitor.push_token_name("TOKEN", "token").unwrap(),
            Some(true),
            "candidate {candidate}"
        );
    }
}

#[test]
fn rewrites_ignore_large_unrelated_data() {
    let grammar = grammar_with_action("Bad()");
    let mut program = String::from(
        r#"
        (datatype Ast (Good) (Bad) (Middle) (Junk i64))
        (let $root (Good))
        (rewrite (Junk value) (Middle))
        (rewrite (Middle) (Bad))
        (rewrite (Middle) (Good))
        "#,
    );
    for value in 0..512 {
        program.push_str(&format!("(let $junk-{value} (Junk {value}))\n"));
    }
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

    // If the first rule scanned outside the target/fixed-prefix focus, any
    // Junk value would connect Bad() and Good() through Middle().
    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
}

#[test]
fn fixed_prefix_focus_crosses_ignored_pending_syntax() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD TAIL
        %%
        start: atom TAIL { Wrap(1) };
        atom: BAD { Bad() };
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Wrap Ast))
        (let $root (Good))
        (rewrite (Wrap (Bad)) (Good))
        "#,
        "$root",
    )
    .unwrap();

    // TAIL is still pending, but it is absent from the semantic action. The
    // zipper therefore exposes the fixed Wrap(Bad()) root to rewriting now.
    assert_eq!(monitor.push_token_name("BAD", "bad").unwrap(), Some(true));
}

#[test]
fn a_dead_parse_branch_is_not_used_by_a_late_rewrite() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token A B
        %%
        start: A   { Dead() }
             | A B { Bad() }
             ;
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Dead) (Bridge))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.push_token_name("A", "a").unwrap(), None);
    assert_eq!(monitor.push_token_name("B", "b").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog(
                r#"
                (rewrite (Dead) (Bridge))
                (rewrite (Bridge) (Bad))
                (rewrite (Bridge) (Good))
                "#,
            )
            .unwrap(),
        None
    );
}

#[test]
fn a_deep_rewrite_chain_added_by_the_next_token_reaches_its_fixpoint() {
    let grammar = numbered_state_grammar(false);
    let mut monitor =
        Monitor::new(&grammar, &state_program(1_200, "(State 1200)", ""), "$root").unwrap();

    assert_eq!(monitor.push_token_name("NUMBER", "0").unwrap(), Some(true));
}

#[test]
fn initial_rewrites_reach_a_completion_through_a_deep_term() {
    let depth = 128;
    let grammar = deeply_wrapped_state_grammar(depth, "1800");
    let target = wrap("(State 0)", depth);
    let program = state_program(
        1_800,
        "$deep-target",
        &format!("(let $deep-target {target})"),
    );
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(
        monitor.push_token_name("NUMBER", "1800").unwrap(),
        Some(true)
    );
}

#[test]
fn a_later_rule_extends_existing_equalities_to_the_current_prefix() {
    let grammar = numbered_state_grammar(false);
    let mut monitor =
        Monitor::new(&grammar, &state_program(600, "(State 0)", ""), "$root").unwrap();

    assert_eq!(monitor.push_token_name("NUMBER", "1200").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog(r#"(rewrite (State n) (State (+ n 1)) :when ((< n 1200)))"#,)
            .unwrap(),
        Some(true)
    );
}

#[test]
fn a_deep_witness_prevents_an_ambiguous_prefix_from_being_rejected() {
    let grammar = numbered_state_grammar(true);
    let program = state_program(1_200, "(State 1200)", "(Disjoint (Bad) (State 1200))");
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

    let answer = monitor.push_token_name("NUMBER", "0").unwrap();
    assert_ne!(
        answer,
        Some(false),
        "an unfinished equality proof is not an impossibility proof"
    );
    assert_eq!(
        answer,
        Some(true),
        "the deep equal parse must be found despite the disjoint parse"
    );
}
