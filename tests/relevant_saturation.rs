use prefixspace::{Grammar, LiveMonitorError, LivePrefixMonitor};

fn leaf_grammar() -> Grammar {
    Grammar::from_yacc(
        r#"
        %start start
        %token BAD
        %%
        start: BAD { Bad() };
        "#,
    )
    .unwrap()
}

#[test]
fn managed_directed_rewrite_does_not_scan_an_unreachable_lhs() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token OTHER
        %%
        start: OTHER { Other() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Other))
        (let $root (Good))
        (let $bad (Bad))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("OTHER", "other").unwrap());
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    assert!(monitor.intersection_is_empty());
    assert_eq!(monitor.stats().managed_rewrite_declarations, 1);
    assert_eq!(monitor.stats().total_basin_rule_matches, 0);
}

#[test]
fn rewrite_installed_after_a_complete_prefix_uses_the_current_zipper_root() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Good) (Bad)) (let $root (Good))",
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(monitor.intersection_is_empty());
    assert!(
        !monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    assert_eq!(monitor.realizability(), Some(true));
}

#[test]
fn managed_directed_rewrites_close_a_chain_in_either_declaration_order() {
    let grammar = leaf_grammar();
    for rewrites in [
        r#"
        (rewrite (Good) (Middle))
        (rewrite (Middle) (Bad))
        "#,
        r#"
        (rewrite (Middle) (Bad))
        (rewrite (Good) (Middle))
        "#,
    ] {
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            r#"
            (datatype Ast (Good) (Middle) (Bad))
            (let $root (Good))
            (let $bad (Bad))
            "#,
            "$root",
        )
        .unwrap();
        assert!(monitor.push_token_name("BAD", "bad").unwrap());
        assert!(!monitor.add_managed_rewrites(rewrites).unwrap());
    }
}

#[test]
fn managed_birewrites_construct_a_missing_intermediate_in_the_target_basin() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Middle) (Bad))
        (let $root (Good))
        (let $bad (Bad))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        !monitor
            .add_managed_rewrites(
                r#"
                (birewrite (Bad) (Middle))
                (birewrite (Middle) (Good))
                "#,
            )
            .unwrap()
    );
    let stats = monitor.stats();
    assert!(stats.total_basin_rule_matches > 0);
}

#[test]
fn managed_birewrite_descends_through_an_existing_unmentioned_context() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Child (U) (V))
        (datatype Ast (Good) (Leaf) (F Child))
        (let $root (Good))
        (let $fu (F (U)))
        (let $fv (F (V)))
        (let $leaf (Leaf))
        (union $root $fu)
        (union $leaf $fv)
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());

    // F occurs in neither the grammar nor the rewrite. Target-basin
    // saturation merges U/V and then connects Good/Leaf by congruence, so the
    // basin must nevertheless project through the existing F rows.
    assert!(!monitor.add_managed_rewrites("(birewrite (U) (V))").unwrap());
    assert!(monitor.stats().total_basin_rule_matches > 0);
}

#[test]
fn late_context_declaration_recloses_existing_birewrites() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Child (U) (V))
        (datatype Ast (Good) (Leaf))
        (let $root (Good))
        (let $leaf (Leaf))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());
    assert!(monitor.add_managed_rewrites("(birewrite (U) (V))").unwrap());
    assert!(
        !monitor
            .run_egglog(
                r#"
                (constructor F (Child) Ast)
                (let $fu (F (U)))
                (let $fv (F (V)))
                (union $root $fu)
                (union $leaf $fv)
                "#,
            )
            .unwrap()
    );
}

#[test]
fn context_declared_before_a_partial_update_error_is_still_projected() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Child (U) (V))
        (datatype Ast (Good) (Leaf))
        (let $root (Good))
        (let $leaf (Leaf))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());
    assert!(monitor.add_managed_rewrites("(birewrite (U) (V))").unwrap());
    let result = monitor.run_egglog(
        r#"
        (constructor F (Child) Ast)
        (let $fu (F (U)))
        (let $fv (F (V)))
        (union $root $fu)
        (union $leaf $fv)
        (let $oops (missing-function))
        "#,
    );
    assert!(matches!(result, Err(LiveMonitorError::Egglog(_))));
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn managed_directed_rules_skip_an_unrelated_common_ancestor_path() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Leaf) (U) (Middle))
        (let $root (Good))
        (let $leaf (Leaf))
        (let $unrelated (U))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());
    assert!(
        monitor
            .add_managed_rewrites(
                r#"
                (rewrite (U) (Middle))
                (rewrite (Middle) (Good))
                (rewrite (Middle) (Leaf))
                "#,
            )
            .unwrap()
    );
    assert!(monitor.intersection_is_empty());
    assert_eq!(monitor.stats().total_basin_rule_matches, 0);
}

#[test]
fn managed_directions_reclose_regardless_of_registration_order() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token U_TOKEN
        %%
        start: U_TOKEN { U() };
        "#,
    )
    .unwrap();
    for ordinary_first in [false, true] {
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            r#"
            (datatype Ast (Good) (U) (Middle))
            (let $root (Good))
            (let $source (U))
            "#,
            "$root",
        )
        .unwrap();
        assert!(monitor.push_token_name("U_TOKEN", "u").unwrap());
        if ordinary_first {
            assert!(
                monitor
                    .add_managed_rewrites("(rewrite (Middle) (U))")
                    .unwrap()
            );
            assert!(
                !monitor
                    .add_managed_rewrites("(birewrite (Good) (Middle))")
                    .unwrap()
            );
        } else {
            assert!(
                monitor
                    .add_managed_rewrites("(birewrite (Good) (Middle))")
                    .unwrap()
            );
            assert!(
                !monitor
                    .add_managed_rewrites("(rewrite (Middle) (U))")
                    .unwrap()
            );
        }
        assert!(monitor.stats().total_basin_rule_matches > 0);
    }
}

#[test]
fn large_managed_birewrite_chain_stays_in_the_target_basin() {
    const DEPTH: usize = 128;
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token TOKEN
        %%
        start: TOKEN { N0() };
        "#,
    )
    .unwrap();
    let mut program = String::from("(datatype Ast");
    for index in 0..=DEPTH {
        program.push_str(&format!(" (N{index})"));
    }
    program.push_str(")\n");
    program.push_str(&format!("(let $root (N{DEPTH}))\n"));
    let mut rewrites = String::new();
    for index in 0..DEPTH {
        rewrites.push_str(&format!("(birewrite (N{index}) (N{}))\n", index + 1));
    }

    let mut monitor = LivePrefixMonitor::from_egglog(&grammar, &program, "$root").unwrap();
    assert!(monitor.push_token_name("TOKEN", "token").unwrap());
    assert!(!monitor.add_managed_rewrites(&rewrites).unwrap());
    let stats = monitor.stats();
    assert!(stats.total_basin_rule_matches >= DEPTH);
}

#[test]
fn expanding_managed_saturation_is_round_limited_and_resumable() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token TOKEN
        %%
        start: atom { F(1) };
        atom: TOKEN { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Leaf) (F Ast) (G Ast))
        (let $source (F (Leaf)))
        "#,
        "$source",
    )
    .unwrap();
    assert!(!monitor.push_token_name("TOKEN", "token").unwrap());

    let error = monitor
        .add_managed_rewrites_with_round_limit("(rewrite (F x) (F (G x)))", 3)
        .unwrap_err();
    assert!(matches!(
        error,
        LiveMonitorError::ManagedSaturationRoundLimit { rounds: 3 }
    ));
    let error = monitor.continue_managed_saturation(2).unwrap_err();
    assert!(matches!(
        error,
        LiveMonitorError::ManagedSaturationRoundLimit { rounds: 2 }
    ));
}

#[test]
fn zero_round_install_is_observable_and_can_be_resumed_to_a_fixed_point() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    let error = monitor
        .add_managed_rewrites_with_round_limit("(birewrite (Bad) (Good))", 0)
        .unwrap_err();
    assert!(matches!(
        error,
        LiveMonitorError::ManagedSaturationRoundLimit { rounds: 0 }
    ));
    assert!(monitor.intersection_is_empty());
    assert_eq!(monitor.stats().managed_rewrite_declarations, 1);
    assert_eq!(monitor.stats().last_basin_rule_matches, 0);

    assert!(!monitor.continue_managed_saturation(8).unwrap());
    assert!(!monitor.intersection_is_empty());
    assert!(monitor.stats().last_basin_rule_matches > 0);
}

#[test]
fn run_egglog_round_limit_keeps_the_partial_update_and_allows_resume() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (F Ast))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (F x) (Bad))")
            .unwrap()
    );
    let error = monitor
        .run_egglog_with_managed_saturation_round_limit(
            "(let $late-context (F $root)) (union $root $late-context)",
            0,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        LiveMonitorError::ManagedSaturationRoundLimit { rounds: 0 }
    ));
    assert!(monitor.intersection_is_empty());

    assert!(!monitor.continue_managed_saturation(8).unwrap());
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn managed_birewrite_can_construct_the_missing_reverse_term() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        !monitor
            .add_managed_rewrites("(birewrite (Bad) (Good))")
            .unwrap()
    );
}

#[test]
fn registered_managed_rewrites_are_reclosed_after_later_egraph_updates() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (F Ast))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();

    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (F x) (Bad))")
            .unwrap()
    );
    assert!(
        !monitor
            .run_egglog("(let $late-context (F $root)) (union $root $late-context)")
            .unwrap()
    );
    assert!(!monitor.intersection_is_empty());
}

#[test]
fn managed_directed_rewrite_does_not_construct_a_missing_lhs() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token OTHER
        %%
        start: OTHER { Other() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Good) (Bad) (Other)) (let $root (Good))",
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("OTHER", "other").unwrap());
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    assert!(monitor.intersection_is_empty());
}

#[test]
fn managed_directed_rewrite_discovers_an_existing_simplifier_lhs() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token TOKEN
        %%
        start: TOKEN { Good() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (F Ast))
        (let $good (Good))
        (let $root (F $good))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("TOKEN", "token").unwrap());
    assert!(!monitor.add_managed_rewrites("(rewrite (F x) x)").unwrap());
}

#[test]
fn managed_birewrite_does_not_fire_outside_the_target_basin() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad) (Junk i64) (OtherJunk i64))
        (let $root (Good))
        (let $bad (Bad))
        (let $junk-1 (Junk 1))
        (let $junk-2 (Junk 2))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());

    assert!(
        monitor
            .add_managed_rewrites("(birewrite (Junk value) (OtherJunk value))")
            .unwrap()
    );
    assert_eq!(monitor.stats().last_basin_rule_matches, 0);
    assert_eq!(monitor.stats().total_basin_rule_matches, 0);
}

#[test]
fn target_basin_descends_through_non_grammar_constructors_used_by_birewrites() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token LEAF
        %%
        start: LEAF { Leaf() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Bad) (Good) (Leaf) (Aux Ast))
        (let $root (Aux (Bad)))
        (let $leaf (Leaf))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("LEAF", "leaf").unwrap());

    assert!(
        !monitor
            .add_managed_rewrites(
                r#"
                (birewrite (Bad) (Good))
                (birewrite (Leaf) (Aux (Good)))
                "#,
            )
            .unwrap()
    );
}

#[test]
fn canonicalized_old_rows_are_reconsidered_after_a_late_union() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token WANTED
        %%
        start: WANTED { Wanted() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Expected) (Bad) (Good) (Wanted) (Box Ast))
        (let $expected (Expected))
        (let $bad (Bad))
        (let $root (Box $expected))
        (let $wanted (Wanted))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("WANTED", "wanted").unwrap());
    assert!(
        monitor
            .add_managed_rewrites(
                r#"
                (rewrite (Bad) (Good))
                (rewrite (Box (Good)) (Wanted))
                "#,
            )
            .unwrap()
    );
    assert!(!monitor.run_egglog("(union $expected $bad)").unwrap());
}

#[test]
fn false_condition_blocks_a_managed_directed_rewrite() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token GOOD
        %%
        start: GOOD { Good() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Bad))
        (let $good (Good))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("GOOD", "good").unwrap());
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Bad) (Good) :when ((= 0 1)))")
            .unwrap()
    );
}

#[test]
fn duplicate_managed_rewrite_registration_is_idempotent() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        (let $bad (Bad))
        "#,
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        !monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    let before = monitor.stats();
    assert!(
        !monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    let after = monitor.stats();
    assert_eq!(
        after.managed_rewrite_declarations,
        before.managed_rewrite_declarations
    );
    assert_eq!(
        after.total_basin_rule_matches,
        before.total_basin_rule_matches
    );
}

#[test]
fn upgrading_a_managed_rewrite_to_birewrite_installs_only_the_missing_direction() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Good) (Bad)) (let $root (Good))",
        "$root",
    )
    .unwrap();
    assert!(monitor.push_token_name("BAD", "bad").unwrap());
    assert!(
        !monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );
    assert!(
        !monitor
            .add_managed_rewrites("(birewrite (Bad) (Good))")
            .unwrap()
    );
}

#[test]
fn managed_reflexive_directed_rewrite_is_safe_and_idempotent() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Good) (Bad)) (let $root (Good))",
        "$root",
    )
    .unwrap();
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Good) (Good))")
            .is_ok()
    );
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Good) (Good))")
            .is_ok()
    );
}

#[test]
fn managed_saturation_api_rejects_commands_that_are_not_rewrites() {
    let grammar = leaf_grammar();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        "(datatype Ast (Good) (Bad)) (let $root (Good))",
        "$root",
    )
    .unwrap();

    assert!(matches!(
        monitor.add_managed_rewrites("(run 1)"),
        Err(LiveMonitorError::UnsupportedManagedSaturationCommand(command)) if command == "run-schedule"
    ));
    assert!(matches!(
        monitor.add_managed_rewrites("(rule ((= x (Bad))) ((union x (Good))))"),
        Err(LiveMonitorError::UnsupportedManagedSaturationCommand(command)) if command == "rule"
    ));
}

#[test]
fn lexeme_updates_run_registered_managed_rules_on_newly_fixed_trees() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token BAD TAIL END
        %%
        start: atom TAIL END { $1 };
        atom: BAD { Bad() };
        "#,
    )
    .unwrap();
    let mut monitor = LivePrefixMonitor::from_egglog(
        &grammar,
        r#"
        (datatype Ast (Good) (Bad))
        (let $root (Good))
        "#,
        "$root",
    )
    .unwrap();
    assert!(
        monitor
            .add_managed_rewrites("(rewrite (Bad) (Good))")
            .unwrap()
    );

    let before = monitor.stats().total_basin_rule_matches;
    // BAD fixes the projected semantic root while TAIL END is still pending.
    // The derivative materializes Bad(), focuses it, and automatically
    // recloses the installed rule immediately.
    assert!(!monitor.push_token_name("BAD", "bad").unwrap());
    assert!(monitor.stats().total_basin_rule_matches > before);
    let before = monitor.stats().total_basin_rule_matches;
    assert!(!monitor.push_token_name("TAIL", "tail").unwrap());
    assert_eq!(monitor.stats().total_basin_rule_matches, before);
    assert!(!monitor.intersection_is_empty());
}
