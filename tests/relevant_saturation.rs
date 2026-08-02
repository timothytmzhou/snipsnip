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

fn lexeme_dependent_bad_grammar() -> Grammar {
    Grammar::from_yacc_lex(
        r#"
        %start start
        %token TOKEN
        %%
        start: TOKEN { Bad(1) };
        "#,
        "%%\nbad 'TOKEN'\n",
    )
    .unwrap()
}

const PAIR_REWRITES: &str = r#"
    (rewrite (Pair left right) left)
    (rewrite (Pair left right) right)
"#;

fn pair_bridge_program(include_pair: bool, include_rewrites: bool) -> String {
    let pair = if include_pair {
        "(let $bridge (Pair (Bad) (Good)))"
    } else {
        ""
    };
    let rewrites = if include_rewrites { PAIR_REWRITES } else { "" };
    format!(
        r#"
        (datatype Ast (Good) (Bad) (Pair Ast Ast))
        (let $root (Good))
        {pair}
        {rewrites}
        "#
    )
}

fn numbered_state_grammar(alternative: bool) -> Grammar {
    let alternative = if alternative {
        "| NUMBER { Bad() }"
    } else {
        ""
    };
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
    let grammar = lexeme_dependent_bad_grammar();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad String))
        (let $root (Good))
        (rewrite (Bad value) (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), None);
    assert_eq!(monitor.push_token_name("TOKEN", "bad").unwrap(), Some(true));
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
fn rhs_relevance_uses_an_existing_predecessor_without_running_backwards() {
    let grammar = grammar_with_action("Bad()");

    for (include_pair, expected) in [(false, None), (true, Some(true))] {
        let program = pair_bridge_program(include_pair, true);
        let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

        assert_eq!(
            monitor.push_token_name("TOKEN", "token").unwrap(),
            expected,
            "include_pair={include_pair}"
        );
    }
}

#[test]
fn a_new_candidate_focus_includes_children_of_its_existing_enodes() {
    let grammar = grammar_with_action("Candidate()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Candidate) (B0) (B1) (Done) (Wrap Ast))
        (let $candidate (Candidate))
        (let $hidden (Wrap (B0)))
        (union $candidate $hidden)
        (let $root (Wrap (Done)))
        (rewrite (B0) (B1))
        (rewrite (B1) (Done))
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
fn late_rhs_relevant_rules_reconsider_existing_terms() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(&grammar, &pair_bridge_program(true, false), "$root").unwrap();

    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
    assert_eq!(monitor.run_egglog(PAIR_REWRITES).unwrap(), Some(true));
}

#[test]
fn a_late_predecessor_is_seen_by_existing_rules() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(&grammar, &pair_bridge_program(false, true), "$root").unwrap();

    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
    assert_eq!(
        monitor
            .run_egglog("(let $bridge (Pair (Bad) (Good)))")
            .unwrap(),
        Some(true)
    );
}

#[test]
fn productive_infinite_rewrite_stops_when_the_target_is_reached() {
    let grammar = numbered_state_grammar(false);
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (State i64))
        (let $root (State 2))
        (rewrite (State n) (State (+ n 1)))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), Some(true));
    assert_eq!(monitor.push_token_name("NUMBER", "0").unwrap(), Some(true));
}

#[test]
fn an_unrelated_productive_rewrite_is_not_run() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Noise i64))
        (let $root (Good))
        (let $noise (Noise 0))
        (rewrite (Noise n) (Noise (+ n 1)))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), None);
    assert_eq!(monitor.push_token_name("TOKEN", "token").unwrap(), None);
}

#[test]
fn an_ordinary_rule_runs_when_one_of_its_facts_touches_the_focus() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (relation Edge (Ast Ast))
        (let $root (Good))
        (Edge (Bad) (Good))
        (rule ((Edge left right)) ((union left right)))
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
fn ordinary_rules_follow_helper_facts_to_the_target() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Middle1) (Middle2))
        (relation Edge (Ast Ast))
        (let $root (Good))
        (Edge (Bad) (Middle1))
        (Edge (Middle1) (Middle2))
        (Edge (Middle2) (Good))
        (rule ((Edge left right)) ((union left right)))
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
fn a_constant_rule_head_is_not_hidden_by_an_unrelated_body_value() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Trigger))
        (relation Mark (Ast))
        (let $root (Good))
        (Mark (Trigger))
        (rule ((Mark value)) ((union (Bad) (Good))))
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
fn duplicate_user_rule_names_are_scheduled_independently() {
    let grammar = grammar_with_action("Bad()");
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Middle))
        (let $root (Good))
        (rule ((= value (Bad))) ((union value (Middle))) :name "same")
        (rule ((= value (Middle))) ((union value (Good))) :name "same")
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
fn a_deep_witness_is_found_in_an_ambiguous_prefix() {
    let grammar = numbered_state_grammar(true);
    let program = state_program(1_200, "(State 1200)", "");
    let mut monitor = Monitor::new(&grammar, &program, "$root").unwrap();

    assert_eq!(
        monitor.push_token_name("NUMBER", "0").unwrap(),
        Some(true),
        "the deep equal parse must be found despite the other parse"
    );
}
