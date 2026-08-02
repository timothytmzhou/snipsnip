use crate::{
    egglog_backend::{
        BackendDelta, EgglogBackend, ExactToken, MutationResult, SaturationRun, ValueId,
    },
    error::LiveMonitorError,
    grammar::{Grammar, RuntimeInput, TerminalId, Token},
    paper_pwz::{Edit, ExpressionId, Pwz, Token as PwzToken},
    pwz::PwzStats,
    pwz_grammar,
    realizability::{ConstructorSchema, RealizabilityEngine, TypedClass},
};
use smallvec::SmallVec;

pub const DEFAULT_MANAGED_SATURATION_ROUND_LIMIT: usize = 1_024;
pub const DEFAULT_PREFIX_SATURATION_ROUND_LIMIT: usize = 64;
pub const DEFAULT_UNREALIZABILITY_WORK_LIMIT: usize = 100_000;
pub const DEFAULT_PREFIX_FOCUS_WORK_LIMIT: usize = 100_000;

#[deprecated(since = "0.1.0", note = "use DEFAULT_MANAGED_SATURATION_ROUND_LIMIT")]
pub const DEFAULT_RELEVANT_SATURATION_ROUNDS: usize = DEFAULT_MANAGED_SATURATION_ROUND_LIMIT;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LiveMonitorStats {
    pub lexeme_updates: usize,
    pub egraph_updates: usize,
    pub prefix_space_states: usize,
    pub prefix_space_facts: usize,
    pub realizability_facts: usize,
    pub fixed_tree_bindings: usize,
    pub last_prefix_output_work: usize,
    pub total_prefix_output_work: usize,
    pub last_prefix_focus_work: usize,
    pub total_prefix_focus_work: usize,
    pub last_delta_rule_matches: usize,
    pub total_delta_rule_matches: usize,
    pub managed_rewrite_declarations: usize,
    pub last_basin_rule_matches: usize,
    pub total_basin_rule_matches: usize,
    pub last_delta_join_probes: usize,
    pub total_delta_join_probes: usize,
    pub full_rebuilds: usize,
    pub pwz: PwzStats,
}

type Payload = SmallVec<[TypedClass<ValueId>; 2]>;

/// A PwZ parser, a semantic e-graph, and only the relation linking
/// them. No parse tree or e-node is copied into this facade.
pub struct LivePrefixMonitor {
    input: RuntimeInput,
    parser: Pwz<Payload>,
    realizability: RealizabilityEngine<ValueId>,
    backend: EgglogBackend,
    exact_tokens: Vec<ExactToken>,
    empty: bool,
    stats: LiveMonitorStats,
}

impl LivePrefixMonitor {
    pub fn from_egglog(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, false)
    }

    pub fn from_egglog_with_disjointness(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        _disjoint_relation: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, false)
    }

    pub fn from_egglog_with_local_saturation(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, true)
    }

    pub fn from_egglog_with_local_saturation_and_disjointness(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        _disjoint_relation: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, true)
    }

    fn from_egglog_internal(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        local_saturation: bool,
    ) -> Result<Self, LiveMonitorError> {
        let input = grammar.runtime_input();
        let init = EgglogBackend::initialize(
            grammar,
            &input,
            program,
            target_binding,
            local_saturation,
            DEFAULT_PREFIX_SATURATION_ROUND_LIMIT,
        )?;
        let semantic_schema = pwz_grammar::semantics(
            grammar,
            |name| init.schema.constructor_id(name),
            init.schema
                .constructors
                .iter()
                .map(|schema| ConstructorSchema {
                    inputs: schema.inputs.clone(),
                    output: schema.output,
                })
                .collect(),
        );
        let parser = Pwz::new(pwz_grammar::compile(grammar)?);
        let realizability = RealizabilityEngine::new(semantic_schema, &parser, &init.backend);
        let mut stats = LiveMonitorStats {
            managed_rewrite_declarations: init.initial_managed_rewrites,
            prefix_space_states: parser.expressions.len()
                + parser.contexts.len()
                + parser.memos.len(),
            prefix_space_facts: parser.expressions.len()
                + parser.contexts.len()
                + parser.memos.len(),
            ..LiveMonitorStats::default()
        };
        record_saturation(&mut stats, init.delta.saturation);
        let mut monitor = Self {
            input,
            parser,
            realizability,
            backend: init.backend,
            exact_tokens: Vec::new(),
            empty: true,
            stats,
        };
        monitor.refresh();
        Ok(monitor)
    }

    pub fn push_token_name(
        &mut self,
        terminal_name: &str,
        lexeme: &str,
    ) -> Result<bool, LiveMonitorError> {
        let terminal = self
            .input
            .terminal(terminal_name)
            .ok_or_else(|| LiveMonitorError::UnknownTerminal(terminal_name.to_owned()))?;
        if self.input.has_lexer() && !self.input.lexeme_matches(terminal, lexeme) {
            return Err(LiveMonitorError::LexemeMismatch {
                terminal: terminal_name.to_owned(),
                lexeme: lexeme.to_owned(),
            });
        }
        self.push_lexeme(terminal, lexeme)
    }

    pub fn push_token(&mut self, token: &Token) -> Result<bool, LiveMonitorError> {
        self.push_lexeme(token.kind, &token.lexeme)
    }

    pub fn push_complete_text(&mut self, text: &str) -> Result<Vec<bool>, LiveMonitorError> {
        self.input
            .lex(text)?
            .iter()
            .map(|token| self.push_token(token))
            .collect()
    }

    pub fn push_lexeme(
        &mut self,
        terminal: TerminalId,
        lexeme: &str,
    ) -> Result<bool, LiveMonitorError> {
        if terminal.index() >= self.backend.terminal_count() {
            return Err(LiveMonitorError::InvalidTerminalId(terminal.index()));
        }
        self.begin_update();
        if self.parser.zippers.is_empty() {
            self.stats.lexeme_updates = self.stats.lexeme_updates.saturating_add(1);
            return Ok(true);
        }
        self.backend
            .exact_tokens(terminal, lexeme, &mut self.exact_tokens)?;
        let payload = self
            .exact_tokens
            .iter()
            .map(|token| TypedClass {
                sort: token.sort,
                class: token.value,
            })
            .collect();
        let (edit_count, fixed, work) = {
            let derivative = self.parser.derive(PwzToken {
                terminal: u32::try_from(terminal.index())
                    .map_err(|_| LiveMonitorError::InvalidTerminalId(terminal.index()))?,
                payload,
            });
            let fixed = self.backend.focus_enabled().then(|| {
                derivative
                    .edits
                    .iter()
                    .filter_map(|edit| match edit {
                        Edit::NewExpression(expression) => Some(*expression),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            });
            let work =
                self.realizability
                    .update_pwz(derivative.pwz, derivative.edits, &self.backend);
            (derivative.edits.len(), fixed, work)
        };
        self.stats.lexeme_updates = self.stats.lexeme_updates.saturating_add(1);
        self.stats.prefix_space_facts = self.stats.prefix_space_facts.saturating_add(edit_count);
        self.stats.pwz.events = self.stats.pwz.events.saturating_add(edit_count);
        self.record_work(work);
        if let Some(fixed) = fixed {
            self.materialize(&fixed)?;
            let delta = self
                .backend
                .saturate_local(DEFAULT_PREFIX_SATURATION_ROUND_LIMIT)?;
            self.apply_delta(delta);
        }
        self.refresh();
        Ok(self.empty)
    }

    pub fn run_egglog(&mut self, update: &str) -> Result<bool, LiveMonitorError> {
        self.run_egglog_with_managed_saturation_round_limit(
            update,
            DEFAULT_MANAGED_SATURATION_ROUND_LIMIT,
        )
    }

    pub fn run_egglog_with_managed_saturation_round_limit(
        &mut self,
        update: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.begin_update();
        let mutation = self.backend.apply_monotone_update(update)?;
        self.stats.egraph_updates = self.stats.egraph_updates.saturating_add(1);
        let partial = match mutation {
            MutationResult::Applied => None,
            MutationResult::PartiallyApplied(error) => Some(error),
        };
        let result = self.finish_egraph_update(round_limit);
        match (partial, result) {
            (None, result) => result,
            (Some(error), Ok(_)) => Err(error),
            (Some(error), Err(sync)) => Err(LiveMonitorError::Egglog(format!(
                "{error}; additionally failed to synchronize the partial update: {sync}"
            ))),
        }
    }

    #[deprecated(
        since = "0.1.0",
        note = "use run_egglog_with_managed_saturation_round_limit"
    )]
    pub fn run_egglog_with_relevant_limit(
        &mut self,
        update: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.run_egglog_with_managed_saturation_round_limit(update, round_limit)
    }

    pub fn add_managed_rewrites(&mut self, rewrites: &str) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites_with_round_limit(rewrites, DEFAULT_MANAGED_SATURATION_ROUND_LIMIT)
    }

    pub fn add_managed_rewrites_with_round_limit(
        &mut self,
        rewrites: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.begin_update();
        let added = self.backend.install_managed_rewrites(rewrites)?;
        self.stats.managed_rewrite_declarations = self
            .stats
            .managed_rewrite_declarations
            .saturating_add(added);
        self.stats.egraph_updates = self.stats.egraph_updates.saturating_add(1);
        let fixed = self
            .parser
            .expressions
            .iter()
            .filter_map(|(&id, expression)| expression.fixed.then_some(id))
            .collect::<Vec<_>>();
        self.materialize(&fixed)?;
        self.finish_egraph_update(round_limit)
    }

    #[deprecated(since = "0.1.0", note = "use add_managed_rewrites")]
    pub fn add_relevant_rewrites(&mut self, rewrites: &str) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites(rewrites)
    }

    #[deprecated(since = "0.1.0", note = "use add_managed_rewrites_with_round_limit")]
    pub fn add_relevant_rewrites_with_limit(
        &mut self,
        rewrites: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites_with_round_limit(rewrites, round_limit)
    }

    pub fn continue_managed_saturation(
        &mut self,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.begin_update();
        self.stats.egraph_updates = self.stats.egraph_updates.saturating_add(1);
        self.finish_egraph_update(round_limit)
    }

    #[deprecated(since = "0.1.0", note = "use continue_managed_saturation")]
    pub fn continue_relevant_saturation(
        &mut self,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.continue_managed_saturation(round_limit)
    }

    pub fn intersection_is_empty(&self) -> bool {
        self.empty
    }

    pub fn realizability(&self) -> Option<bool> {
        (!self.empty).then_some(true)
    }

    pub fn stats(&self) -> LiveMonitorStats {
        let mut stats = self.stats;
        stats.prefix_space_states =
            self.parser.expressions.len() + self.parser.contexts.len() + self.parser.memos.len();
        stats.realizability_facts = self.realizability.fact_count();
        stats.pwz.derivatives = stats.lexeme_updates;
        stats.pwz.memo_records = self.parser.memos.len();
        stats
    }

    fn finish_egraph_update(&mut self, round_limit: usize) -> Result<bool, LiveMonitorError> {
        let delta = self.backend.saturate_local(round_limit)?;
        let complete = delta.saturation.complete;
        self.apply_delta(delta);
        self.refresh();
        if complete {
            Ok(self.empty)
        } else {
            Err(LiveMonitorError::ManagedSaturationRoundLimit {
                rounds: round_limit,
            })
        }
    }

    fn apply_delta(&mut self, delta: BackendDelta) {
        record_saturation(&mut self.stats, delta.saturation);
        let work = self
            .realizability
            .update_egraph(&self.parser, &delta.changes, &self.backend);
        self.record_work(work);
    }

    fn materialize(&mut self, expressions: &[ExpressionId]) -> Result<(), LiveMonitorError> {
        let mut work =
            self.realizability
                .materialize_fixed(&self.parser, expressions, &mut self.backend)?;
        work = work.saturating_add(
            self.realizability
                .materialize_focus(&self.parser, &mut self.backend)?,
        );
        self.stats.last_prefix_focus_work = self.stats.last_prefix_focus_work.saturating_add(work);
        self.stats.total_prefix_focus_work =
            self.stats.total_prefix_focus_work.saturating_add(work);
        self.record_work(work);
        Ok(())
    }

    fn begin_update(&mut self) {
        self.stats.last_delta_rule_matches = 0;
        self.stats.last_delta_join_probes = 0;
        self.stats.last_basin_rule_matches = 0;
        self.stats.last_prefix_focus_work = 0;
        self.stats.last_prefix_output_work = 0;
    }

    fn record_work(&mut self, work: usize) {
        self.stats.last_delta_rule_matches =
            self.stats.last_delta_rule_matches.saturating_add(work);
        self.stats.total_delta_rule_matches =
            self.stats.total_delta_rule_matches.saturating_add(work);
        self.stats.last_delta_join_probes = self.stats.last_delta_join_probes.saturating_add(work);
        self.stats.total_delta_join_probes =
            self.stats.total_delta_join_probes.saturating_add(work);
    }

    fn refresh(&mut self) {
        self.empty = !self
            .realizability
            .is_realizable(&self.parser.zippers, &self.backend);
    }
}

fn record_saturation(stats: &mut LiveMonitorStats, saturation: SaturationRun) {
    let matches = saturation
        .projection_matches
        .saturating_add(saturation.basin_matches);
    stats.last_delta_rule_matches = stats.last_delta_rule_matches.saturating_add(matches);
    stats.total_delta_rule_matches = stats.total_delta_rule_matches.saturating_add(matches);
    stats.last_basin_rule_matches = stats
        .last_basin_rule_matches
        .saturating_add(saturation.basin_matches);
    stats.total_basin_rule_matches = stats
        .total_basin_rule_matches
        .saturating_add(saturation.basin_matches);
}

#[cfg(test)]
mod tests {
    use super::LivePrefixMonitor;
    use crate::grammar::Grammar;

    #[test]
    fn checks_each_prefix_and_applies_late_equality_without_parser_replay() {
        let grammar = Grammar::from_yacc_lex(
            r#"
            %start start
            %token ID
            %%
            start: ID { Var(1) };
            "#,
            "%%\n[a-z]+ 'ID'\n",
        )
        .unwrap();
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            r#"
            (datatype Ast (Var String))
            (let $root (Var "x"))
            "#,
            "$root",
        )
        .unwrap();

        assert!(!monitor.intersection_is_empty());
        assert!(monitor.push_token_name("ID", "y").unwrap());
        let prefixes = monitor.stats().lexeme_updates;
        assert!(!monitor.run_egglog("(union $root (Var \"y\"))").unwrap());
        assert_eq!(monitor.stats().lexeme_updates, prefixes);
    }

    #[test]
    fn ignored_future_syntax_uses_the_value_independent_relation() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token TAIL
            %%
            start: TAIL { Good() };
            "#,
        )
        .unwrap();
        let monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            "(datatype Ast (Good)) (let $root (Good))",
            "$root",
        )
        .unwrap();
        assert!(!monitor.intersection_is_empty());
    }

    #[test]
    fn focus_materialization_crosses_ignored_pending_syntax() {
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
        let mut monitor = LivePrefixMonitor::from_egglog(
            &grammar,
            "(datatype Ast (Good) (Bad) (Wrap Ast)) (let $root (Good))",
            "$root",
        )
        .unwrap();
        assert!(
            monitor
                .add_managed_rewrites("(rewrite (Wrap (Bad)) (Good))")
                .unwrap()
        );

        assert!(!monitor.push_token_name("BAD", "bad").unwrap());
    }
}
