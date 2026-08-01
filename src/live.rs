use thiserror::Error;

use crate::{
    egglog_backend::{
        BackendFact, EgglogBackend, ExactToken, MutationResult, SaturationRun, ValueId,
    },
    fixed_tree::{BindingId, FixedTreeMaterializer, MaterializedCandidate, TypedExact},
    forest::{ForestPwz, SpaceFact, ZipperFact},
    grammar::{Grammar, GrammarError, RuntimeInput, TerminalId, Token},
    prefix_output::{DEFAULT_PREFIX_OUTPUT_WORK_BUDGET, PrefixOutputBuilder},
    pwz::{PwzError, PwzStats},
    realizability::{ConstructorId, RealizabilityEngine, SortId},
};

/// Joint fixed-point round limit used by the convenience managed-saturation
/// APIs.
///
/// This limits rounds, not the amount of work performed within a round. A
/// single egglog round may apply many matches and may allocate many e-nodes.
/// Use the explicit round-limit variants to choose another limit or resume an
/// interrupted expanding rewrite system.
pub const DEFAULT_MANAGED_SATURATION_ROUND_LIMIT: usize = 1_024;

/// Maximum joint local-saturation rounds performed automatically after one
/// lexeme. Reaching this limit leaves a sound partial e-graph; the three-way
/// answer remains `None` unless equality or disjointness has already proved a
/// result.
pub const DEFAULT_PREFIX_SATURATION_ROUND_LIMIT: usize = 64;

/// Maximum zipper states and concrete constructor combinations inspected by
/// one explicit disjointness proof attempt. Exhaustion produces `None`, never
/// a guessed negative answer.
pub const DEFAULT_UNREALIZABILITY_WORK_LIMIT: usize = DEFAULT_PREFIX_OUTPUT_WORK_BUDGET;

/// Maximum incremental zipper-focus events processed automatically after one
/// lexeme. Ordinary LL(1) updates consume only their newly added delta; the
/// limit prevents a term-generating context cycle from monopolizing a push.
pub const DEFAULT_PREFIX_FOCUS_WORK_LIMIT: usize = DEFAULT_PREFIX_OUTPUT_WORK_BUDGET;

/// Deprecated name for [`DEFAULT_MANAGED_SATURATION_ROUND_LIMIT`].
#[deprecated(since = "0.1.0", note = "use DEFAULT_MANAGED_SATURATION_ROUND_LIMIT")]
pub const DEFAULT_RELEVANT_SATURATION_ROUNDS: usize = DEFAULT_MANAGED_SATURATION_ROUND_LIMIT;

#[derive(Debug, Error)]
pub enum LiveMonitorError {
    #[error(transparent)]
    Grammar(#[from] GrammarError),
    #[error(transparent)]
    Pwz(#[from] PwzError),
    #[error("egglog update failed: {0}")]
    Egglog(String),
    #[error("unknown disjointness relation `{0}`")]
    UnknownDisjointRelation(String),
    #[error("disjointness relation `{relation}` must have signature ({sort} {sort}) -> Unit")]
    InvalidDisjointRelation { relation: String, sort: String },
    #[error("unknown terminal `{0}`")]
    UnknownTerminal(String),
    #[error("terminal id {0} is outside this monitor grammar's terminal range")]
    InvalidTerminalId(usize),
    #[error("lexeme `{lexeme}` is not one complete `{terminal}` token")]
    LexemeMismatch { terminal: String, lexeme: String },
    #[error("invalid distinguished binding `{binding}`: {reason}")]
    InvalidBinding { binding: String, reason: String },
    #[error("the distinguished binding has non-equality sort `{0}`")]
    NonEqualityTarget(String),
    #[error("action constructor `{0}` is not declared in the live e-graph")]
    MissingConstructor(String),
    #[error("action symbol `{0}` is an egglog function, not a datatype constructor")]
    NonConstructorAction(String),
    #[error(
        "action constructor `{constructor}` has arity {actual}, but the annotation selects {expected} child(ren)"
    )]
    ConstructorArity {
        constructor: String,
        expected: usize,
        actual: usize,
    },
    #[error(
        "terminal `{terminal}` is selected as `{sort}` data, but only String and i64 lexical children are supported"
    )]
    UnsupportedLexicalSort { terminal: String, sort: String },
    #[error(
        "semantic sort `{0}` is unsupported; live matching accepts equality sorts plus String and i64 lexical sorts"
    )]
    UnsupportedSemanticSort(String),
    #[error("terminal `{0}` is selected by an action but the grammar has no Lex specification")]
    SelectedTerminalWithoutLexer(String),
    #[error("the live monitor supports monotone egglog updates only; found `{0}`")]
    NonMonotoneUpdate(String),
    #[error("the live monitor does not execute operational egglog command `{0}`")]
    UnsupportedUpdateCommand(String),
    #[error("egglog update refers to reserved monitor namespace `{0}`")]
    ReservedNamespace(String),
    #[error("managed saturation accepts only rewrite and birewrite commands; found `{0}`")]
    UnsupportedManagedSaturationCommand(String),
    #[error("managed rewrite has no equality-sorted root tracked by the monitor")]
    UnsupportedManagedRewrite,
    #[error(
        "managed equality saturation did not reach a fixed point within {rounds} joint round(s); the e-graph and monitor contain the sound partial result and saturation can be resumed"
    )]
    ManagedSaturationRoundLimit { rounds: usize },
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LiveMonitorStats {
    pub lexeme_updates: usize,
    pub egraph_updates: usize,
    pub prefix_space_states: usize,
    pub prefix_space_facts: usize,
    /// Total materialized `Produces`, `RealizableFor`, and `Realizable` facts.
    pub realizability_facts: usize,
    /// Concrete parsed terms inserted into private egglog bindings.
    pub fixed_tree_bindings: usize,
    /// Bounded zipper-output states inspected for the latest explicit
    /// disjointness proof attempt.
    pub last_prefix_output_work: usize,
    /// Cumulative zipper-output states inspected for explicit disjointness.
    pub total_prefix_output_work: usize,
    /// Incremental zipper-focus events processed by the latest update.
    pub last_prefix_focus_work: usize,
    /// Cumulative incremental zipper-focus events.
    pub total_prefix_focus_work: usize,
    pub last_delta_rule_matches: usize,
    pub total_delta_rule_matches: usize,
    /// Number of user rewrite declarations installed through the managed
    /// saturation API. One birewrite counts as one declaration.
    pub managed_rewrite_declarations: usize,
    /// Focus-basin-guarded managed rewrite matches applied during the most
    /// recent update. The target and fixed prefix terms mark the relevant area.
    pub last_basin_rule_matches: usize,
    /// Focus-basin-guarded managed rewrite matches applied over the monitor's
    /// lifetime.
    pub total_basin_rule_matches: usize,
    /// Candidate e-node/product rows inspected by the indexed local joins in
    /// the most recent lexeme or e-graph update.
    pub last_delta_join_probes: usize,
    /// Cumulative candidate e-node/product rows inspected by local joins.
    pub total_delta_join_probes: usize,
    /// Always zero: this architecture never rebuilds an explicit product.
    pub full_rebuilds: usize,
    pub pwz: PwzStats,
}

/// A value-producing PwZ monitor whose e-graph remains live.
///
/// A private egglog ruleset exports only newly target-reachable e-nodes. A
/// typed Rust worklist joins that delta with persistent PwZ space and zipper
/// facts. When focused analyses or managed rewrites are installed, a lexeme
/// push materializes newly fixed prefix trees and runs bounded local egglog
/// saturation around them. Neither this focused work nor a separate e-graph
/// update replays parser history.
pub struct LivePrefixMonitor {
    input: RuntimeInput,
    parser: ForestPwz,
    realizability: RealizabilityEngine,
    backend: EgglogBackend,
    target_sort_id: SortId,
    space_fact_buffer: Vec<SpaceFact>,
    zipper_fact_buffer: Vec<ZipperFact>,
    epoch: i64,
    current_terminal: Option<TerminalId>,
    current_exact_tokens: Vec<ExactToken>,
    current_lexeme_values: Vec<(SortId, ValueId)>,
    current_lexeme_sources: Vec<TypedExact>,
    fixed_trees: FixedTreeMaterializer<ValueId>,
    materialized_buffer: Vec<MaterializedCandidate<ValueId>>,
    prefix_outputs: PrefixOutputBuilder,
    current_output_roots: Vec<BindingId>,
    current_outputs_complete: bool,
    explicit_disjoint_prefix: bool,
    last_prefix_output_work: usize,
    total_prefix_output_work: usize,
    last_prefix_focus_work: usize,
    total_prefix_focus_work: usize,
    empty: bool,
    prefix_realizability: Option<bool>,
    lexeme_updates: usize,
    egraph_updates: usize,
    last_delta_rule_matches: usize,
    total_delta_rule_matches: usize,
    managed_rewrite_declarations: usize,
    last_basin_rule_matches: usize,
    total_basin_rule_matches: usize,
}

impl LivePrefixMonitor {
    /// Builds a live monitor which also reads positive disjointness proofs
    /// from `disjoint_relation`.
    pub fn from_egglog_with_disjointness(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        disjoint_relation: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(
            grammar,
            program,
            target_binding,
            Some(disjoint_relation),
            false,
        )
    }

    pub fn from_egglog(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, None, false)
    }

    /// Builds a monitor and automatically runs every rewrite and birewrite in
    /// `program` only around the distinguished target and concrete syntax
    /// exposed by the current prefix. Automatic closure is bounded by
    /// [`DEFAULT_PREFIX_SATURATION_ROUND_LIMIT`]; an unfinished closure remains
    /// sound and yields `None` unless a proof has already been found.
    ///
    /// Explicit run schedules are rejected by this constructor because the
    /// extracted rewrites belong to the private local scheduler, not Egglog's
    /// global ruleset.
    pub fn from_egglog_with_local_saturation(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(grammar, program, target_binding, None, true)
    }

    /// [`Self::from_egglog_with_local_saturation`] plus a positive
    /// disjointness relation used to prove negative answers.
    pub fn from_egglog_with_local_saturation_and_disjointness(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        disjoint_relation: &str,
    ) -> Result<Self, LiveMonitorError> {
        Self::from_egglog_internal(
            grammar,
            program,
            target_binding,
            Some(disjoint_relation),
            true,
        )
    }

    fn from_egglog_internal(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
        disjoint_relation: Option<&str>,
        locally_saturate_initial_rewrites: bool,
    ) -> Result<Self, LiveMonitorError> {
        let input = grammar.runtime_input();
        let init = EgglogBackend::initialize(
            grammar,
            &input,
            program,
            target_binding,
            disjoint_relation,
            locally_saturate_initial_rewrites,
            DEFAULT_PREFIX_SATURATION_ROUND_LIMIT,
        )?;
        let schema = init.schema;
        let parser = ForestPwz::compile(
            grammar,
            |constructor| {
                u32::try_from(schema.constructor_id(constructor))
                    .expect("constructor count was already bounded by grammar size")
            },
            &schema.selected_terminals,
        )?;
        let realizability = RealizabilityEngine::new(
            input.clone(),
            grammar.terminal_count(),
            schema.sort_count,
            schema.constructors.clone(),
            schema.terminal_sorts.clone(),
        );
        let fixed_trees = FixedTreeMaterializer::new(
            grammar.nonterminal_count() + grammar.terminal_count(),
            schema.sort_count,
            schema.constructors,
        );
        let mut monitor = Self {
            input,
            parser,
            realizability,
            backend: init.backend,
            target_sort_id: schema.target_sort,
            space_fact_buffer: Vec::new(),
            zipper_fact_buffer: Vec::new(),
            epoch: 0,
            current_terminal: None,
            current_exact_tokens: Vec::new(),
            current_lexeme_values: Vec::new(),
            current_lexeme_sources: Vec::new(),
            fixed_trees,
            materialized_buffer: Vec::new(),
            prefix_outputs: PrefixOutputBuilder::new(),
            current_output_roots: Vec::new(),
            current_outputs_complete: false,
            explicit_disjoint_prefix: false,
            last_prefix_output_work: 0,
            total_prefix_output_work: 0,
            last_prefix_focus_work: 0,
            total_prefix_focus_work: 0,
            empty: true,
            prefix_realizability: None,
            lexeme_updates: 0,
            egraph_updates: 0,
            last_delta_rule_matches: 0,
            total_delta_rule_matches: 0,
            managed_rewrite_declarations: init.initial_managed_rewrites,
            last_basin_rule_matches: 0,
            total_basin_rule_matches: 0,
        };
        monitor.realizability.begin_update();
        monitor.flush_prefix_delta()?;
        monitor.record_saturation(init.delta.saturation);
        monitor.apply_backend_facts(init.delta.facts);
        let local_matches = monitor.realizability.finish_update();
        monitor.record_realizability_matches(local_matches);
        monitor.refresh_answer();
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

    /// Lexes a complete source string and reports the answer after each emitted
    /// lexeme. The stream itself remains lexeme-granular: ignored text does not
    /// create an epoch and a token's complete spelling is retained when an
    /// action selects that terminal.
    pub fn push_complete_text(&mut self, text: &str) -> Result<Vec<bool>, LiveMonitorError> {
        let tokens = self.input.lex(text)?;
        tokens.iter().map(|token| self.push_token(token)).collect()
    }

    /// Advances the syntax stream by one complete lexeme.
    ///
    /// If focused egglog work is enabled, newly concrete prefix trees are
    /// inserted once and the installed local rules are automatically reclosed
    /// before the cached answer is returned.
    pub fn push_lexeme(
        &mut self,
        terminal: TerminalId,
        lexeme: &str,
    ) -> Result<bool, LiveMonitorError> {
        if terminal.index() >= self.backend.terminal_count() {
            return Err(LiveMonitorError::InvalidTerminalId(terminal.index()));
        }
        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.last_prefix_output_work = 0;
        self.last_prefix_focus_work = 0;
        self.realizability.begin_update();
        let parser_live = self.parser.push(terminal, lexeme)?;
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or(PwzError::ArenaCapacityExceeded)?;
        self.lexeme_updates = self.lexeme_updates.saturating_add(1);
        self.current_terminal = Some(terminal);
        self.current_exact_tokens.clear();
        self.current_lexeme_values.clear();
        self.current_lexeme_sources.clear();
        if !parser_live {
            // Syntactic death is absorbing. Facts emitted while discovering
            // the dead frontier and lexical values from all later pushes can
            // never affect an answer, so do not grow the parser or
            // realizability state.
            self.parser.swap_space_facts(&mut self.space_fact_buffer);
            self.parser.swap_zipper_facts(&mut self.zipper_fact_buffer);
            self.space_fact_buffer.clear();
            self.zipper_fact_buffer.clear();
            self.current_terminal = None;
            let matches = self.realizability.finish_update();
            self.record_realizability_matches(matches);
            self.empty = true;
            self.reset_current_prefix_proof();
            self.refresh_realizability_status();
            return Ok(true);
        }
        self.backend
            .exact_tokens(terminal, lexeme, &mut self.current_exact_tokens)?;
        for exact in &self.current_exact_tokens {
            self.current_lexeme_values.push((exact.sort, exact.value));
            self.current_lexeme_sources.push(TypedExact {
                sort: exact.sort,
                source: exact.source.clone(),
            });
        }
        self.flush_prefix_delta()?;
        self.reset_current_prefix_proof();
        let mut saturation_rounds = DEFAULT_PREFIX_SATURATION_ROUND_LIMIT;
        self.finish_prefix_phase(&mut saturation_rounds)?;
        if self.empty && self.backend.needs_disjoint_candidates() && self.parser.is_live() {
            // A finite concrete root snapshot serves both as local rewrite
            // focus and as the explicit universal negative proof. Reachable
            // zipper cycles fail this phase immediately and leave Unknown.
            self.realizability.begin_update();
            self.enumerate_current_outputs_for_disjointness()?;
            self.finish_prefix_phase(&mut saturation_rounds)?;
        } else if self.empty && self.backend.managed_rules_enabled() && self.parser.is_live() {
            // Without an explicit negative checker, reconstruct a bounded
            // concrete zipper focus only to give managed rewrites a chance to
            // establish a positive witness.
            self.realizability.begin_update();
            self.propagate_current_prefix_focus()?;
            self.finish_prefix_phase(&mut saturation_rounds)?;
        }
        Ok(self.empty)
    }

    /// Runs a monotone user update, then incrementally closes the private
    /// target-projection ruleset, any installed managed equality rules, and
    /// local realizability relations. No parser state is replayed.
    pub fn run_egglog(&mut self, update: &str) -> Result<bool, LiveMonitorError> {
        self.run_egglog_with_managed_saturation_round_limit(
            update,
            DEFAULT_MANAGED_SATURATION_ROUND_LIMIT,
        )
    }

    /// Like [`Self::run_egglog`], with an explicit joint-round limit for
    /// persistent managed equality rules.
    ///
    /// Limit exhaustion leaves a synchronized, resumable, sound partial
    /// saturation and returns
    /// [`LiveMonitorError::ManagedSaturationRoundLimit`]. The limit is not a
    /// bound on matches, running time, e-node allocation, or memory: one
    /// egglog round may perform an unbounded amount of work relative to this
    /// number.
    pub fn run_egglog_with_managed_saturation_round_limit(
        &mut self,
        update: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        let mutation = self.backend.apply_monotone_update(update)?;
        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.realizability.begin_update();
        let partial_error = match mutation {
            MutationResult::Applied => {
                self.egraph_updates = self.egraph_updates.saturating_add(1);
                None
            }
            MutationResult::PartiallyApplied(error) => Some(error),
        };
        let synchronized = self.finish_egraph_delta_with_round_limit(round_limit);
        match (partial_error, synchronized) {
            (None, result) => result,
            (Some(error), Ok(_)) => Err(error),
            (Some(error), Err(sync)) => Err(LiveMonitorError::Egglog(format!(
                "{error}; additionally failed to synchronize the partial update: {sync}"
            ))),
        }
    }

    /// Deprecated name for
    /// [`Self::run_egglog_with_managed_saturation_round_limit`].
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

    /// Installs managed equality rewrites and closes them jointly with the
    /// monitor's constructor projection.
    ///
    /// Every directed rewrite is guarded by target-basin reachability of its
    /// left-hand side. A `birewrite` installs two such forward directions.
    /// The distinguished target and concrete terms fixed by the current prefix
    /// are marked relevant. That relevance is projected through every declared
    /// e-graph function context with equality-sorted children, so unrelated
    /// e-graph components are not scanned.
    ///
    /// Rules remain installed and are automatically reclosed after later
    /// [`Self::run_egglog`] updates and after lexeme pushes expose newly fixed
    /// prefix trees in the focused basin.
    pub fn add_managed_rewrites(&mut self, rewrites: &str) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites_with_round_limit(rewrites, DEFAULT_MANAGED_SATURATION_ROUND_LIMIT)
    }

    /// Installs managed rewrites and performs at most `round_limit` joint
    /// saturation rounds. A zero limit installs the rules but deliberately
    /// performs no saturation round.
    ///
    /// The round limit is not a bound on matches, running time, e-node
    /// allocation, or memory. One egglog round may do substantial work.
    pub fn add_managed_rewrites_with_round_limit(
        &mut self,
        rewrites: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.realizability.begin_update();
        let added = self.backend.install_managed_rewrites(rewrites)?;
        self.managed_rewrite_declarations = self.managed_rewrite_declarations.saturating_add(added);
        if self.parser.is_live() {
            // The current semantic root can still live only in the zipper
            // (for example, a just-completed start production). Reconstruct
            // every bounded concrete root now so a rewrite installed after
            // the lexeme sees the same focus as a rewrite installed before it.
            self.propagate_current_prefix_focus()?;
        }
        self.egraph_updates = self.egraph_updates.saturating_add(1);
        self.finish_egraph_delta_with_round_limit(round_limit)
    }

    /// Deprecated name for [`Self::add_managed_rewrites`].
    #[deprecated(since = "0.1.0", note = "use add_managed_rewrites")]
    pub fn add_relevant_rewrites(&mut self, rewrites: &str) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites(rewrites)
    }

    /// Deprecated name for [`Self::add_managed_rewrites_with_round_limit`].
    #[deprecated(since = "0.1.0", note = "use add_managed_rewrites_with_round_limit")]
    pub fn add_relevant_rewrites_with_limit(
        &mut self,
        rewrites: &str,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.add_managed_rewrites_with_round_limit(rewrites, round_limit)
    }

    /// Resumes already-installed managed equality rules without changing the
    /// parser or adding user e-graph commands.
    ///
    /// At most `round_limit` joint rounds are executed. This is not a bound on
    /// work within a round.
    pub fn continue_managed_saturation(
        &mut self,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.realizability.begin_update();
        self.egraph_updates = self.egraph_updates.saturating_add(1);
        self.finish_egraph_delta_with_round_limit(round_limit)
    }

    /// Deprecated name for [`Self::continue_managed_saturation`].
    #[deprecated(since = "0.1.0", note = "use continue_managed_saturation")]
    pub fn continue_relevant_saturation(
        &mut self,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        self.continue_managed_saturation(round_limit)
    }

    fn finish_egraph_delta_with_round_limit(
        &mut self,
        round_limit: usize,
    ) -> Result<bool, LiveMonitorError> {
        if !self.parser.is_live() {
            let matches = self.realizability.finish_update();
            self.record_realizability_matches(matches);
            self.refresh_answer();
            return Ok(self.empty);
        }
        let delta = self.backend.saturate_local(round_limit)?;
        let complete = delta.saturation.complete;
        self.record_saturation(delta.saturation);
        self.apply_backend_facts(delta.facts);
        let local_matches = self.realizability.finish_update();
        self.record_realizability_matches(local_matches);
        self.refresh_answer();
        if complete {
            Ok(self.empty)
        } else {
            Err(LiveMonitorError::ManagedSaturationRoundLimit {
                rounds: round_limit,
            })
        }
    }

    pub fn intersection_is_empty(&self) -> bool {
        self.empty
    }

    /// Returns the strongest currently justified three-way answer.
    /// `Some(true)` is a witnessed completion, `Some(false)` is a proof that
    /// every completion is impossible, and `None` means neither is proved.
    pub fn realizability(&self) -> Option<bool> {
        self.prefix_realizability
    }

    pub fn stats(&self) -> LiveMonitorStats {
        LiveMonitorStats {
            lexeme_updates: self.lexeme_updates,
            egraph_updates: self.egraph_updates,
            prefix_space_states: self.parser.representation_state_count(),
            prefix_space_facts: self.parser.representation_fact_count(),
            realizability_facts: self.realizability.fact_count(),
            fixed_tree_bindings: self.fixed_trees.binding_count(),
            last_prefix_output_work: self.last_prefix_output_work,
            total_prefix_output_work: self.total_prefix_output_work,
            last_prefix_focus_work: self.last_prefix_focus_work,
            total_prefix_focus_work: self.total_prefix_focus_work,
            last_delta_rule_matches: self.last_delta_rule_matches,
            total_delta_rule_matches: self.total_delta_rule_matches,
            managed_rewrite_declarations: self.managed_rewrite_declarations,
            last_basin_rule_matches: self.last_basin_rule_matches,
            total_basin_rule_matches: self.total_basin_rule_matches,
            last_delta_join_probes: self.realizability.last_join_probes(),
            total_delta_join_probes: self.realizability.total_join_probes(),
            full_rebuilds: 0,
            pwz: self.parser.stats(),
        }
    }

    fn flush_prefix_delta(&mut self) -> Result<(), LiveMonitorError> {
        self.parser.swap_space_facts(&mut self.space_fact_buffer);
        self.parser.swap_zipper_facts(&mut self.zipper_fact_buffer);
        if self.space_fact_buffer.is_empty() && self.zipper_fact_buffer.is_empty() {
            return Ok(());
        }
        while let Some(fact) = self.space_fact_buffer.pop() {
            self.fixed_trees
                .add_space_fact(fact.clone(), &self.current_lexeme_sources);
            match fact {
                SpaceFact::Alias { output, child } => self.realizability.add_alias(output, child),
                SpaceFact::Constructor {
                    constructor,
                    output,
                    children,
                } => self.realizability.add_space_constructor(
                    constructor as ConstructorId,
                    output,
                    children,
                ),
                SpaceFact::TokenAny { output, terminal } => {
                    self.realizability.add_token_any(output, terminal);
                }
                SpaceFact::TokenExact { output, terminal } => {
                    debug_assert_eq!(Some(terminal), self.current_terminal);
                    for &(sort, value) in &self.current_lexeme_values {
                        self.realizability.add_token_exact(sort, output, value);
                    }
                }
            }
        }
        while let Some(fact) = self.zipper_fact_buffer.pop() {
            self.prefix_outputs.add_fact(&fact);
            match fact {
                ZipperFact::Parent { memo, context } => {
                    self.realizability.add_parent(memo, context)
                }
                ZipperFact::Alternative { context, memo } => {
                    self.realizability.add_alternative(context, memo);
                }
                ZipperFact::ConstructHole {
                    constructor,
                    context,
                    memo,
                    hole_argument,
                    fixed_children,
                } => self.realizability.add_construct_hole(
                    constructor as ConstructorId,
                    context,
                    memo,
                    hole_argument,
                    fixed_children,
                ),
                ZipperFact::ConstructIgnored {
                    constructor,
                    context,
                    memo,
                    children,
                } => self.realizability.add_construct_ignored(
                    constructor as ConstructorId,
                    context,
                    memo,
                    children,
                ),
                ZipperFact::ProjectHole { context, memo } => {
                    self.realizability.add_project_hole(context, memo);
                }
                ZipperFact::ProjectFixed {
                    context,
                    memo,
                    child,
                } => self.realizability.add_project_fixed(context, memo, child),
            }
        }
        if self.backend.focus_enabled() {
            self.materialize_fixed_trees()?;
        }
        Ok(())
    }

    fn reset_current_prefix_proof(&mut self) {
        self.current_output_roots.clear();
        self.current_outputs_complete = false;
        self.explicit_disjoint_prefix = false;
        self.last_prefix_output_work = 0;
        self.last_prefix_focus_work = 0;
    }

    fn finish_prefix_phase(
        &mut self,
        remaining_saturation_rounds: &mut usize,
    ) -> Result<(), LiveMonitorError> {
        if self.backend.focus_enabled()
            && !self.backend.local_saturation_complete()
            && *remaining_saturation_rounds != 0
        {
            let delta = self.backend.saturate_local(*remaining_saturation_rounds)?;
            *remaining_saturation_rounds =
                remaining_saturation_rounds.saturating_sub(delta.saturation.rounds);
            self.record_saturation(delta.saturation);
            self.apply_backend_facts(delta.facts);
        }
        let matches = self.realizability.finish_update();
        self.record_realizability_matches(matches);
        self.refresh_answer();
        Ok(())
    }

    fn propagate_current_prefix_focus(&mut self) -> Result<(), LiveMonitorError> {
        if !self.backend.managed_rules_enabled() {
            return Ok(());
        }
        self.prefix_outputs
            .mark_frontier_relevant(self.parser.current_frontier());
        let work = self
            .prefix_outputs
            .drain_focus(&mut self.fixed_trees, DEFAULT_PREFIX_FOCUS_WORK_LIMIT);
        self.last_prefix_focus_work = work;
        self.total_prefix_focus_work = self.total_prefix_focus_work.saturating_add(work);
        // Focus propagation constructs only one shallow node at a time.
        self.materialize_fixed_trees()
    }

    fn enumerate_current_outputs_for_disjointness(&mut self) -> Result<(), LiveMonitorError> {
        if !self.backend.needs_disjoint_candidates() {
            return Ok(());
        }
        let output = self.prefix_outputs.enumerate(
            self.parser.current_frontier(),
            &mut self.fixed_trees,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        self.current_output_roots = output.roots;
        self.current_outputs_complete = output.complete;
        self.last_prefix_output_work = output.work;
        self.total_prefix_output_work = self.total_prefix_output_work.saturating_add(output.work);
        // Bounded snapshot reconstruction may have created shallow detached
        // terms. They are evaluated only after positive intersection failed.
        self.materialize_fixed_trees()
    }

    fn record_saturation(&mut self, saturation: SaturationRun) {
        let matches = saturation
            .projection_matches
            .saturating_add(saturation.basin_matches);
        self.last_delta_rule_matches = self.last_delta_rule_matches.saturating_add(matches);
        self.total_delta_rule_matches = self.total_delta_rule_matches.saturating_add(matches);
        self.last_basin_rule_matches = self
            .last_basin_rule_matches
            .saturating_add(saturation.basin_matches);
        self.total_basin_rule_matches = self
            .total_basin_rule_matches
            .saturating_add(saturation.basin_matches);
    }

    fn record_realizability_matches(&mut self, matches: usize) {
        self.last_delta_rule_matches = self.last_delta_rule_matches.saturating_add(matches);
        self.total_delta_rule_matches = self.total_delta_rule_matches.saturating_add(matches);
    }

    fn apply_backend_facts(&mut self, facts: Vec<BackendFact>) {
        for fact in facts {
            match fact {
                BackendFact::Target { sort, value } => {
                    self.realizability.add_target(sort, value);
                }
                BackendFact::Enode {
                    constructor,
                    output,
                    children,
                } => self.realizability.add_enode(constructor, output, children),
                BackendFact::Domain {
                    sort,
                    value,
                    lexical_form,
                    integer,
                } => self
                    .realizability
                    .add_domain(sort, value, lexical_form, integer),
            }
        }
    }

    fn materialize_fixed_trees(&mut self) -> Result<(), LiveMonitorError> {
        let backend = &mut self.backend;
        self.fixed_trees
            .drain_pending_batches(|requests| backend.bind_concrete_asts(requests))?;

        self.fixed_trees
            .drain_materialized(&mut self.materialized_buffer);
        for candidate in self.materialized_buffer.drain(..) {
            self.prefix_outputs
                .notify_focus_candidate(candidate.space, candidate.binding);
        }
        Ok(())
    }

    fn refresh_answer(&mut self) {
        if self.epoch == 0 {
            self.empty = self
                .parser
                .initial_root()
                .is_none_or(|root| !self.realizability.initial_viable(self.target_sort_id, root));
            self.refresh_realizability_status();
            return;
        }
        if self.current_terminal.is_none() {
            self.empty = true;
            self.refresh_realizability_status();
            return;
        }
        self.empty = !self.realizability.frontier_viable(
            &self.current_lexeme_values,
            self.parser
                .current_frontier()
                .iter()
                .map(|frontier| frontier.memo),
        );
        self.refresh_realizability_status();
    }

    fn refresh_realizability_status(&mut self) {
        self.refresh_explicit_disjoint_proof();
        self.prefix_realizability = if !self.empty {
            Some(true)
        } else if !self.parser.is_live()
            || self.explicit_disjoint_prefix
            || self.backend.proves_disjoint_from_target(false, &[])
        {
            Some(false)
        } else {
            None
        };
    }

    fn refresh_explicit_disjoint_proof(&mut self) {
        self.explicit_disjoint_prefix = false;
        if !self.backend.disjoint_enabled()
            || !self.empty
            || !self.current_outputs_complete
            || self.current_output_roots.is_empty()
        {
            return;
        }
        let candidates = self
            .current_output_roots
            .iter()
            .filter_map(|&binding| {
                self.fixed_trees
                    .binding_value(binding)
                    .map(|value| (self.fixed_trees.binding_sort(binding), value))
            })
            .collect::<Vec<_>>();
        if candidates.len() != self.current_output_roots.len() {
            return;
        }
        self.explicit_disjoint_prefix = self
            .backend
            .proves_disjoint_from_target(self.current_outputs_complete, &candidates);
    }
}
