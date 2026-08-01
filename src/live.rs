use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::{Arc, Mutex},
};

use egglog::{
    ArcSort, EGraph, ExecutionState, Primitive, Value,
    ast::{
        Action as EggAction, Change, Command, Expr, Fact, GenericActions, Literal, Rewrite, Rule,
        Subdatatypes,
    },
    constraint::{SimpleTypeConstraint, TypeConstraint},
    prelude::{BaseSort, RustSpan, Span, UnitSort},
    sort::S,
};
use thiserror::Error;

use crate::{
    disjoint::expand_free_commands,
    fixed_tree::{
        BindingId, BindingRhs, ExactSource, FixedTreeMaterializer, MaterializedCandidate,
        PendingBinding, TypedExact,
    },
    forest::{ForestPwz, SpaceFact, ZipperFact},
    grammar::{Action, Grammar, GrammarError, RuntimeInput, Symbol, TerminalId, Token},
    prefix_output::{DEFAULT_PREFIX_OUTPUT_WORK_BUDGET, PrefixOutputBuilder},
    pwz::{PwzError, PwzStats},
    realizability::{ConstructorId, ConstructorSchema, RealizabilityEngine, SortId},
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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PrimitiveKind {
    String,
    I64,
}

impl PrimitiveKind {
    fn from_sort(sort: &ArcSort) -> Option<Self> {
        match sort.name() {
            "String" => Some(Self::String),
            "i64" => Some(Self::I64),
            _ => None,
        }
    }
}

#[derive(Clone)]
struct SortSpec {
    id: SortId,
    name: String,
    reach: Option<String>,
    domain: Option<String>,
    capture_domain: Option<String>,
    primitive: Option<PrimitiveKind>,
}

#[derive(Clone)]
struct ConstructorSpec {
    id: ConstructorId,
    name: String,
    capture: String,
    inputs: Vec<String>,
    output: String,
}

#[derive(Clone, Debug)]
enum CapturedFact {
    Enode {
        constructor: ConstructorId,
        output: Value,
        children: Vec<Value>,
    },
    Domain {
        sort: SortId,
        value: Value,
        lexical_form: String,
        integer: Option<i64>,
    },
    Disjoint {
        left: Value,
        right: Value,
    },
}

type CaptureBuffer = Arc<Mutex<Vec<CapturedFact>>>;

#[derive(Clone)]
struct CaptureEnode {
    name: String,
    sorts: Vec<ArcSort>,
    constructor: ConstructorId,
    buffer: CaptureBuffer,
}

impl Primitive for CaptureEnode {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &egglog::ast::Span) -> Box<dyn TypeConstraint> {
        let mut sorts = self.sorts.clone();
        sorts.push(UnitSort.to_arcsort());
        SimpleTypeConstraint::new(self.name(), sorts, span.clone()).into_box()
    }

    fn apply(&self, state: &mut ExecutionState<'_>, arguments: &[Value]) -> Option<Value> {
        let (&output, children) = arguments.split_first()?;
        self.buffer.lock().unwrap().push(CapturedFact::Enode {
            constructor: self.constructor,
            output,
            children: children.to_vec(),
        });
        Some(state.base_values().get::<()>(()))
    }
}

#[derive(Clone)]
struct CaptureDomain {
    name: String,
    sort: ArcSort,
    sort_id: SortId,
    kind: PrimitiveKind,
    buffer: CaptureBuffer,
}

impl Primitive for CaptureDomain {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &egglog::ast::Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.sort.clone(), UnitSort.to_arcsort()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, state: &mut ExecutionState<'_>, arguments: &[Value]) -> Option<Value> {
        let (lexical_form, integer) = match self.kind {
            PrimitiveKind::String => (
                state
                    .base_values()
                    .unwrap::<S>(arguments[0])
                    .as_str()
                    .to_owned(),
                None,
            ),
            PrimitiveKind::I64 => {
                let value = state.base_values().unwrap::<i64>(arguments[0]);
                (value.to_string(), Some(value))
            }
        };
        self.buffer.lock().unwrap().push(CapturedFact::Domain {
            sort: self.sort_id,
            value: arguments[0],
            lexical_form,
            integer,
        });
        Some(state.base_values().get::<()>(()))
    }
}

#[derive(Clone)]
struct CaptureDisjoint {
    name: String,
    sort: ArcSort,
    buffer: CaptureBuffer,
}

impl Primitive for CaptureDisjoint {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &egglog::ast::Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.sort.clone(), self.sort.clone(), UnitSort.to_arcsort()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, state: &mut ExecutionState<'_>, arguments: &[Value]) -> Option<Value> {
        let [left, right] = arguments else {
            return None;
        };
        self.buffer.lock().unwrap().push(CapturedFact::Disjoint {
            left: *left,
            right: *right,
        });
        Some(state.base_values().get::<()>(()))
    }
}

#[derive(Clone)]
struct TokenSortSpec {
    sort: String,
    kind: PrimitiveKind,
}

struct MatcherNames {
    target_sort: String,
    ruleset: String,
    saturation_ruleset: String,
    relevant_ruleset: String,
    free_ruleset: Option<String>,
    free_reach: BTreeMap<String, String>,
    disjoint_relation: Option<String>,
    capture_disjoint: Option<String>,
    targets: String,
    sorts: BTreeMap<String, SortSpec>,
    saturation_reach: BTreeMap<String, String>,
    saturation_initialized: bool,
    projected_functions: BTreeSet<String>,
    /// User-declared functions which may occur as congruence contexts.
    /// Managed target-basin demand must descend through all of them, not
    /// merely the constructors mentioned by the grammar or by a rewrite.
    known_functions: BTreeSet<String>,
    installed_rewrite_directions: BTreeSet<String>,
    constructors: HashMap<String, ConstructorSpec>,
    token_sorts: Vec<Vec<TokenSortSpec>>,
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
    egraph: EGraph,
    names: MatcherNames,
    private_prefix: String,
    captures: CaptureBuffer,
    target_sort: ArcSort,
    target_sort_id: SortId,
    target_value: Value,
    space_fact_buffer: Vec<SpaceFact>,
    zipper_fact_buffer: Vec<ZipperFact>,
    epoch: i64,
    current_terminal: Option<TerminalId>,
    current_lexeme_values: Vec<(SortId, Value)>,
    current_lexeme_sources: Vec<TypedExact>,
    fixed_trees: FixedTreeMaterializer<Value>,
    materialized_buffer: Vec<MaterializedCandidate<Value>>,
    constructor_names: Vec<String>,
    sort_metadata: Vec<(String, ArcSort)>,
    relevance_marked_values: HashSet<(SortId, Value)>,
    disjoint_pairs: HashSet<(Value, Value)>,
    complete_free_constructor_ids: HashSet<ConstructorId>,
    complete_disjoint_candidate: bool,
    local_saturation_complete: bool,
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
    disjoint_relation: Option<String>,
    complete_disjoint_target: bool,
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
        let mut egraph = EGraph::default();
        let prefix = choose_prefix(&egraph, program);
        let free_ruleset = format!("{prefix}_free_rules");
        let initial_commands = egraph
            .parser
            .get_program_from_string(None, program)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        // A nonmonotone rule installed now could be triggered by a later
        // otherwise-innocent `(run)`, after local delta facts already exist.
        // Validate definitions as well as each subsequent update.
        reject_nonmonotone_commands(&initial_commands)?;
        let (initial_rewrites, setup_commands) = if locally_saturate_initial_rewrites {
            let mut rewrites = Vec::new();
            let mut setup = Vec::new();
            for command in initial_commands {
                match command {
                    Command::Rewrite(..) | Command::BiRewrite(..) => rewrites.push(command),
                    Command::RunSchedule(..) => {
                        return Err(LiveMonitorError::UnsupportedUpdateCommand(
                            "run-schedule".to_owned(),
                        ));
                    }
                    _ => setup.push(command),
                }
            }
            (rewrites, setup)
        } else {
            (Vec::new(), initial_commands)
        };
        let expansion = expand_free_commands(setup_commands, &free_ruleset)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        let declared_constructors = collect_declared_constructors(&expansion.commands);
        let declared_functions = collect_declared_functions(&expansion.commands);
        let free_sorts = expansion.free_sorts;
        egraph
            .run_program(expansion.commands)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;

        let binding_source = normalize_binding(target_binding)?;
        let binding_expression = egraph
            .parser
            .get_expr_from_string(None, &binding_source)
            .map_err(|error| LiveMonitorError::InvalidBinding {
                binding: target_binding.to_owned(),
                reason: error.to_string(),
            })?;
        if !matches!(binding_expression, Expr::Var(_, _)) {
            return Err(LiveMonitorError::InvalidBinding {
                binding: target_binding.to_owned(),
                reason: "expected one global name".to_owned(),
            });
        }
        let (target_sort, target_value) =
            egraph.eval_expr(&binding_expression).map_err(|error| {
                LiveMonitorError::InvalidBinding {
                    binding: target_binding.to_owned(),
                    reason: error.to_string(),
                }
            })?;
        if !target_sort.is_eq_sort() {
            return Err(LiveMonitorError::NonEqualityTarget(
                target_sort.name().to_owned(),
            ));
        }

        let complete_free_spec = match disjoint_relation {
            Some(relation) => {
                validate_disjoint_relation(&egraph, relation, target_sort.name())?;
                free_sorts.iter().any(|spec| {
                    spec.sort == target_sort.name() && spec.relation == relation && spec.complete
                })
            }
            None => false,
        };

        let input = grammar.runtime_input();
        let mut names = build_specs(
            grammar,
            &egraph,
            &input,
            &prefix,
            target_sort.name(),
            &declared_constructors,
            declared_functions,
        )?;
        names.free_ruleset = (!free_sorts.is_empty()).then_some(free_ruleset);
        names.free_reach = free_sorts
            .iter()
            .map(|spec| (spec.sort.clone(), spec.reach.clone()))
            .collect();
        if let Some(relation) = disjoint_relation {
            names.disjoint_relation = Some(relation.to_owned());
            names.capture_disjoint = Some(format!("{prefix}_capture_disjoint"));
        }
        let selected_terminals = names
            .token_sorts
            .iter()
            .map(|sorts| !sorts.is_empty())
            .collect::<Vec<_>>();
        let parser = ForestPwz::compile(
            grammar,
            |constructor| {
                u32::try_from(names.constructors[constructor].id)
                    .expect("constructor count was already bounded by grammar size")
            },
            &selected_terminals,
        )?;
        let captures = Arc::new(Mutex::new(Vec::new()));
        register_capture_primitives(&mut egraph, &names, captures.clone());
        let rules = build_matcher_program(&names, target_sort.name());
        egraph
            .parse_and_run_program(None, &rules)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        insert_target(&mut egraph, &names.targets, binding_expression.clone())?;
        if let Some(reach) = names.free_reach.get(target_sort.name()) {
            egraph
                .run_program(vec![call_command(reach, vec![binding_expression])])
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        }
        let target_sort_id = names.sorts[target_sort.name()].id;
        let constructor_schemas = constructor_schemas(&names);
        let realizability = build_realizability_engine(grammar, &input, &names);
        let fixed_trees = FixedTreeMaterializer::new(
            grammar.nonterminal_count() + grammar.terminal_count(),
            names.sorts.len(),
            constructor_schemas,
        );
        let mut constructor_names = vec![String::new(); names.constructors.len()];
        for constructor in names.constructors.values() {
            constructor_names[constructor.id] = constructor.name.clone();
        }
        let mut sort_metadata = vec![None; names.sorts.len()];
        for sort in names.sorts.values() {
            let egglog_sort = egraph
                .get_sort_by_name(&sort.name)
                .expect("monitored sort still exists")
                .clone();
            sort_metadata[sort.id] = Some((sort.name.clone(), egglog_sort));
        }
        let sort_metadata = sort_metadata
            .into_iter()
            .map(|sort| sort.expect("sort IDs are dense"))
            .collect();
        let complete_free_names = free_sorts
            .iter()
            .filter(|spec| spec.complete)
            .flat_map(|spec| spec.constructors.iter().cloned())
            .collect::<BTreeSet<_>>();
        let complete_free_constructor_ids = names
            .constructors
            .values()
            .filter(|constructor| complete_free_names.contains(&constructor.name))
            .map(|constructor| constructor.id)
            .collect::<HashSet<_>>();
        let grammar_is_in_complete_free_family = names
            .constructors
            .values()
            .all(|constructor| complete_free_names.contains(&constructor.name));

        let mut monitor = Self {
            input,
            parser,
            realizability,
            egraph,
            names,
            private_prefix: prefix,
            captures,
            target_sort,
            target_sort_id,
            target_value,
            space_fact_buffer: Vec::new(),
            zipper_fact_buffer: Vec::new(),
            epoch: 0,
            current_terminal: None,
            current_lexeme_values: Vec::new(),
            current_lexeme_sources: Vec::new(),
            fixed_trees,
            materialized_buffer: Vec::new(),
            constructor_names,
            sort_metadata,
            relevance_marked_values: HashSet::new(),
            disjoint_pairs: HashSet::new(),
            complete_free_constructor_ids,
            complete_disjoint_candidate: complete_free_spec && grammar_is_in_complete_free_family,
            local_saturation_complete: true,
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
            disjoint_relation: disjoint_relation.map(str::to_owned),
            complete_disjoint_target: false,
            lexeme_updates: 0,
            egraph_updates: 0,
            last_delta_rule_matches: 0,
            total_delta_rule_matches: 0,
            managed_rewrite_declarations: 0,
            last_basin_rule_matches: 0,
            total_basin_rule_matches: 0,
        };
        monitor.realizability.begin_update();
        monitor.flush_prefix_delta()?;
        // Without managed user rewrites, these rules only project a finite
        // e-graph, so this closure cannot generate an unbounded term sequence.
        let base = monitor.saturate_matcher(usize::MAX)?;
        debug_assert!(base.complete);
        monitor.record_saturation(base);
        if !initial_rewrites.is_empty() {
            monitor.install_managed_commands(initial_rewrites)?;
            let managed = monitor.saturate_matcher(DEFAULT_PREFIX_SATURATION_ROUND_LIMIT)?;
            monitor.local_saturation_complete = managed.complete;
            monitor.record_saturation(managed);
        } else {
            monitor.local_saturation_complete = true;
        }
        monitor.consume_captures();
        monitor.add_canonical_target();
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
        if terminal.index() >= self.names.token_sorts.len() {
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
        for index in 0..self.names.token_sorts[terminal.index()].len() {
            let token = &self.names.token_sorts[terminal.index()][index];
            let kind = token.kind;
            let sort = self.names.sorts[&token.sort].id;
            if let Some(value) = self.lexeme_value(kind, lexeme) {
                self.current_lexeme_values.push((sort, value));
            }
            if let Some(source) = self.lexeme_source(kind, lexeme) {
                self.current_lexeme_sources
                    .push(TypedExact { sort, source });
            }
        }
        self.flush_prefix_delta()?;
        self.reset_current_prefix_proof();
        let mut saturation_rounds = DEFAULT_PREFIX_SATURATION_ROUND_LIMIT;
        self.finish_prefix_phase(&mut saturation_rounds)?;
        if self.empty
            && self.disjoint_relation.is_some()
            && !self.complete_disjoint_target
            && self.parser.is_live()
        {
            // A finite concrete root snapshot serves both as local rewrite
            // focus and as the explicit universal negative proof. Reachable
            // zipper cycles fail this phase immediately and leave Unknown.
            self.realizability.begin_update();
            self.enumerate_current_outputs_for_disjointness()?;
            self.finish_prefix_phase(&mut saturation_rounds)?;
        } else if self.empty && self.names.saturation_initialized && self.parser.is_live() {
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
        let commands = self
            .egraph
            .parser
            .get_program_from_string(None, update)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        let declared_functions = collect_declared_functions(&commands);
        if source_mentions_identifier_prefix(update, &self.private_prefix) {
            return Err(LiveMonitorError::ReservedNamespace(
                self.private_prefix.clone(),
            ));
        }
        reject_nonmonotone_commands(&commands)?;
        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.realizability.begin_update();
        let update_result = self.egraph.run_program(commands);
        let context_result = self.sync_context_functions(declared_functions);
        if let Err(error) = update_result {
            let mut original = error.to_string();
            if let Err(context) = context_result {
                original.push_str(&format!(
                    "; additionally failed to install context projection: {context}"
                ));
            }
            // egglog command batches are not transactional: commands before
            // the failing one may already have added rows or equalities. Keep
            // the cached realizability state synchronized before reporting
            // that error.
            if let Err(sync) = self.finish_egraph_delta_with_round_limit(round_limit) {
                return Err(LiveMonitorError::Egglog(format!(
                    "{original}; additionally failed to synchronize the partial update: {sync}"
                )));
            }
            return Err(LiveMonitorError::Egglog(original));
        }
        if let Err(error) = context_result {
            if let Err(sync) = self.finish_egraph_delta_with_round_limit(round_limit) {
                return Err(LiveMonitorError::Egglog(format!(
                    "{error}; additionally failed to synchronize the update: {sync}"
                )));
            }
            return Err(error);
        }
        self.egraph_updates = self.egraph_updates.saturating_add(1);
        self.finish_egraph_delta_with_round_limit(round_limit)
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
        if source_mentions_identifier_prefix(rewrites, &self.private_prefix) {
            return Err(LiveMonitorError::ReservedNamespace(
                self.private_prefix.clone(),
            ));
        }
        let commands = self
            .egraph
            .parser
            .get_program_from_string(None, rewrites)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        reject_nonmonotone_commands(&commands)?;
        // Typecheck the whole user batch before installing any private reach
        // relation or rule. Egglog command batches are not transactional; this
        // preflight keeps malformed rewrites from leaving a partially
        // installed private plan behind.
        self.egraph
            .desugar_program(None, rewrites)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;

        self.last_basin_rule_matches = 0;
        self.last_delta_rule_matches = 0;
        self.realizability.begin_update();
        self.install_managed_commands(commands)?;
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

    fn install_managed_commands(&mut self, commands: Vec<Command>) -> Result<(), LiveMonitorError> {
        let plan = build_managed_rewrite_plan(
            &mut self.egraph,
            &self.names,
            &self.private_prefix,
            commands,
        )?;
        self.egraph
            .run_program(plan.commands)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        self.names.saturation_reach = plan.saturation_reach;
        self.names.saturation_initialized = plan.saturation_initialized;
        self.names.projected_functions = plan.projected_functions;
        self.names.installed_rewrite_directions = plan.installed_rewrite_directions;
        self.managed_rewrite_declarations = self
            .managed_rewrite_declarations
            .saturating_add(plan.rewrite_count);
        if plan.rewrite_count != 0 {
            self.local_saturation_complete = false;
        }
        Ok(())
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
        let saturation = self.saturate_matcher(round_limit)?;
        self.local_saturation_complete = saturation.complete;
        self.record_saturation(saturation);
        self.consume_captures();
        self.add_canonical_target();
        let local_matches = self.realizability.finish_update();
        self.record_realizability_matches(local_matches);
        self.refresh_answer();
        if saturation.complete {
            Ok(self.empty)
        } else {
            Err(LiveMonitorError::ManagedSaturationRoundLimit {
                rounds: round_limit,
            })
        }
    }

    fn sync_context_functions(
        &mut self,
        declared_functions: BTreeSet<String>,
    ) -> Result<(), LiveMonitorError> {
        let mut known_functions = self.names.known_functions.clone();
        known_functions.extend(
            declared_functions
                .into_iter()
                .filter(|name| self.egraph.get_function(name).is_some()),
        );
        if known_functions == self.names.known_functions {
            return Ok(());
        }
        if !self.names.saturation_initialized {
            self.names.known_functions = known_functions;
            return Ok(());
        }

        let mut saturation_reach = self.names.saturation_reach.clone();
        let mut projected_functions = self.names.projected_functions.clone();
        let mut declarations = Vec::new();
        append_saturation_projections(
            &self.egraph,
            &self.names.saturation_ruleset,
            &self.private_prefix,
            known_functions.iter().cloned(),
            &mut saturation_reach,
            &mut projected_functions,
            &mut declarations,
        );
        self.egraph
            .run_program(declarations)
            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        self.names.known_functions = known_functions;
        self.names.saturation_reach = saturation_reach;
        self.names.projected_functions = projected_functions;
        Ok(())
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
        if self.focused_egraph_enabled() {
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
        if self.focused_egraph_enabled()
            && !self.local_saturation_complete
            && *remaining_saturation_rounds != 0
        {
            let saturation = self.saturate_matcher(*remaining_saturation_rounds)?;
            *remaining_saturation_rounds =
                remaining_saturation_rounds.saturating_sub(saturation.rounds);
            self.local_saturation_complete = saturation.complete;
            self.record_saturation(saturation);
            self.consume_captures();
            self.add_canonical_target();
        } else if !self.focused_egraph_enabled() {
            self.local_saturation_complete = true;
        }
        let matches = self.realizability.finish_update();
        self.record_realizability_matches(matches);
        self.refresh_answer();
        Ok(())
    }

    fn propagate_current_prefix_focus(&mut self) -> Result<(), LiveMonitorError> {
        if !self.names.saturation_initialized {
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
        if self.disjoint_relation.is_none() || self.complete_disjoint_target {
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

    fn focused_egraph_enabled(&self) -> bool {
        self.disjoint_relation.is_some()
            || self.names.free_ruleset.is_some()
            || self.names.saturation_initialized
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

    fn materialize_fixed_trees(&mut self) -> Result<(), LiveMonitorError> {
        let prefix = self.private_prefix.clone();
        let constructor_names = &self.constructor_names;
        let egraph = &mut self.egraph;
        let mut bindings_to_mark = Vec::new();
        let mut inserted_enode = false;
        self.fixed_trees.drain_pending_batches(|requests| {
            let mut constructor_sizes = HashMap::new();
            let mut actions = Vec::with_capacity(requests.len());
            for request in requests {
                if let BindingRhs::Constructor { constructor, .. } = &request.rhs {
                    let constructor = &constructor_names[*constructor];
                    constructor_sizes
                        .entry(constructor.clone())
                        .or_insert_with(|| egraph.get_size(constructor));
                }
                actions.push(Command::Action(EggAction::Let(
                    egglog::span!(),
                    request.egglog_name(&prefix),
                    fixed_binding_expression(request, constructor_names, &prefix),
                )));
            }
            egraph
                .run_program(actions)
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
            inserted_enode |= constructor_sizes
                .iter()
                .any(|(constructor, size)| egraph.get_size(constructor) > *size);

            requests
                .iter()
                .map(|request| {
                    bindings_to_mark.push((request.sort, request.binding));
                    let name = request.egglog_name(&prefix);
                    egraph
                        .eval_expr(&Expr::Var(egglog::span!(), name))
                        .map(|(_, value)| value)
                        .map_err(|error| LiveMonitorError::Egglog(error.to_string()))
                })
                .collect::<Result<Vec<_>, _>>()
        })?;

        self.fixed_trees
            .drain_materialized(&mut self.materialized_buffer);
        for candidate in self.materialized_buffer.drain(..) {
            self.prefix_outputs
                .notify_focus_candidate(candidate.space, candidate.binding);
            bindings_to_mark.push((candidate.sort, candidate.binding));
        }
        if bindings_to_mark.is_empty() {
            return Ok(());
        }
        let mut relevance_actions = Vec::new();
        let mut relevance_sizes = HashMap::new();
        for (sort, binding) in bindings_to_mark {
            let Some((sort_name, egglog_sort)) = self.sort_metadata.get(sort) else {
                continue;
            };
            let Some(value) = self.fixed_trees.binding_value(binding) else {
                continue;
            };
            let value = self.egraph.get_canonical_value(value, egglog_sort);
            if !self.relevance_marked_values.insert((sort, value)) {
                continue;
            }
            let binding = Expr::Var(egglog::span!(), binding.egglog_name(&self.private_prefix));
            if let Some(reach) = self.names.saturation_reach.get(sort_name) {
                relevance_sizes
                    .entry(reach.clone())
                    .or_insert_with(|| self.egraph.get_size(reach));
                relevance_actions.push(call_command(reach, vec![binding.clone()]));
            }
            if let Some(reach) = self.names.free_reach.get(sort_name) {
                relevance_sizes
                    .entry(reach.clone())
                    .or_insert_with(|| self.egraph.get_size(reach));
                relevance_actions.push(call_command(reach, vec![binding]));
            }
        }
        if !relevance_actions.is_empty() {
            self.egraph
                .run_program(relevance_actions)
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
        }
        let added_relevance = relevance_sizes
            .iter()
            .any(|(relation, size)| self.egraph.get_size(relation) > *size);
        if inserted_enode || added_relevance {
            self.local_saturation_complete = false;
        }
        Ok(())
    }

    fn saturate_matcher(&mut self, round_limit: usize) -> Result<SaturationRun, LiveMonitorError> {
        let mut projection_matches = 0usize;
        let mut basin_matches = 0usize;
        if !self.names.saturation_initialized {
            let mut rounds = 0usize;
            let complete = loop {
                if rounds == round_limit {
                    break false;
                }
                rounds = rounds.saturating_add(1);
                let free = match &self.names.free_ruleset {
                    Some(ruleset) => Some(
                        self.egraph
                            .step_rules(ruleset)
                            .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?,
                    ),
                    None => None,
                };
                let projection = self
                    .egraph
                    .step_rules(&self.names.ruleset)
                    .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
                projection_matches = projection_matches.saturating_add(
                    free.as_ref()
                        .map(|report| report.num_matches_per_rule.values().copied().sum::<usize>())
                        .unwrap_or(0),
                );
                projection_matches = projection_matches.saturating_add(
                    projection
                        .num_matches_per_rule
                        .values()
                        .copied()
                        .sum::<usize>(),
                );
                if !projection.updated && !free.is_some_and(|report| report.updated) {
                    break true;
                }
            };
            return Ok(SaturationRun {
                complete,
                rounds,
                projection_matches,
                basin_matches: 0,
            });
        }
        let mut rounds = 0usize;
        let complete = loop {
            if rounds == round_limit {
                break false;
            }
            rounds = rounds.saturating_add(1);
            let relevant = self
                .egraph
                .step_rules(&self.names.relevant_ruleset)
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
            let saturation = self
                .egraph
                .step_rules(&self.names.saturation_ruleset)
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
            let free = match &self.names.free_ruleset {
                Some(ruleset) => Some(
                    self.egraph
                        .step_rules(ruleset)
                        .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?,
                ),
                None => None,
            };
            let projection = self
                .egraph
                .step_rules(&self.names.ruleset)
                .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
            basin_matches = basin_matches.saturating_add(
                relevant
                    .num_matches_per_rule
                    .values()
                    .copied()
                    .sum::<usize>(),
            );
            projection_matches = projection_matches.saturating_add(
                saturation
                    .num_matches_per_rule
                    .values()
                    .copied()
                    .sum::<usize>(),
            );
            projection_matches = projection_matches.saturating_add(
                free.as_ref()
                    .map(|report| report.num_matches_per_rule.values().copied().sum::<usize>())
                    .unwrap_or(0),
            );
            projection_matches = projection_matches.saturating_add(
                projection
                    .num_matches_per_rule
                    .values()
                    .copied()
                    .sum::<usize>(),
            );
            if !relevant.updated
                && !saturation.updated
                && !free.is_some_and(|report| report.updated)
                && !projection.updated
            {
                break true;
            }
        };
        Ok(SaturationRun {
            complete,
            rounds,
            projection_matches,
            basin_matches,
        })
    }

    fn consume_captures(&mut self) {
        let facts = std::mem::take(&mut *self.captures.lock().unwrap());
        for fact in facts {
            match fact {
                CapturedFact::Enode {
                    constructor,
                    output,
                    children,
                } => {
                    let is_target_constructor =
                        self.names.constructors[&self.constructor_names[constructor]].output
                            == self.names.target_sort;
                    if is_target_constructor
                        && self.complete_disjoint_candidate
                        && self.complete_free_constructor_ids.contains(&constructor)
                        && self.egraph.get_canonical_value(output, &self.target_sort)
                            == self
                                .egraph
                                .get_canonical_value(self.target_value, &self.target_sort)
                    {
                        self.complete_disjoint_target = true;
                    }
                    self.realizability.add_enode(constructor, output, children);
                }
                CapturedFact::Domain {
                    sort,
                    value,
                    lexical_form,
                    integer,
                } => self
                    .realizability
                    .add_domain(sort, value, lexical_form, integer),
                CapturedFact::Disjoint { left, right } => {
                    let left = self.egraph.get_canonical_value(left, &self.target_sort);
                    let right = self.egraph.get_canonical_value(right, &self.target_sort);
                    self.disjoint_pairs.insert((left, right));
                }
            }
        }
    }

    fn add_canonical_target(&mut self) {
        let target = self
            .egraph
            .get_canonical_value(self.target_value, &self.target_sort);
        self.realizability.add_target(self.target_sort_id, target);
    }

    fn lexeme_value(&self, kind: PrimitiveKind, lexeme: &str) -> Option<Value> {
        match kind {
            PrimitiveKind::String => Some(self.egraph.base_to_value::<S>(lexeme.to_owned().into())),
            PrimitiveKind::I64 => Some(self.egraph.base_to_value::<i64>(lexeme.parse().ok()?)),
        }
    }

    fn lexeme_source(&self, kind: PrimitiveKind, lexeme: &str) -> Option<ExactSource> {
        match kind {
            PrimitiveKind::String => Some(ExactSource::String(Arc::from(lexeme))),
            PrimitiveKind::I64 => Some(ExactSource::I64(lexeme.parse().ok()?)),
        }
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
            || (self.local_saturation_complete && self.complete_disjoint_target)
        {
            Some(false)
        } else {
            None
        };
    }

    fn refresh_explicit_disjoint_proof(&mut self) {
        self.explicit_disjoint_prefix = false;
        if self.disjoint_relation.is_none()
            || !self.empty
            || !self.current_outputs_complete
            || self.current_output_roots.is_empty()
        {
            return;
        }
        let target = self
            .egraph
            .get_canonical_value(self.target_value, &self.target_sort);
        self.explicit_disjoint_prefix = self.current_output_roots.iter().all(|&binding| {
            if self.fixed_trees.binding_sort(binding) != self.target_sort_id {
                return false;
            }
            let Some(value) = self.fixed_trees.binding_value(binding) else {
                return false;
            };
            let value = self.egraph.get_canonical_value(value, &self.target_sort);
            self.disjoint_pairs.contains(&(value, target))
        });
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SaturationRun {
    complete: bool,
    rounds: usize,
    projection_matches: usize,
    basin_matches: usize,
}

struct ManagedRewritePlan {
    commands: Vec<Command>,
    saturation_reach: BTreeMap<String, String>,
    saturation_initialized: bool,
    projected_functions: BTreeSet<String>,
    installed_rewrite_directions: BTreeSet<String>,
    rewrite_count: usize,
}

fn build_managed_rewrite_plan(
    egraph: &mut EGraph,
    names: &MatcherNames,
    private_prefix: &str,
    commands: Vec<Command>,
) -> Result<ManagedRewritePlan, LiveMonitorError> {
    let mut rewrites = Vec::<Rewrite>::new();
    let mut installed_rewrite_directions = names.installed_rewrite_directions.clone();
    let mut function_names = BTreeSet::new();
    let mut rewrite_count = 0usize;
    for command in commands {
        match command {
            Command::Rewrite(_, rewrite, false) => {
                if register_managed_direction(
                    rewrite,
                    &mut installed_rewrite_directions,
                    &mut function_names,
                    &mut rewrites,
                ) {
                    rewrite_count = rewrite_count.saturating_add(1);
                }
            }
            Command::BiRewrite(_, rewrite) => {
                let reverse = Rewrite {
                    span: rewrite.span.clone(),
                    lhs: rewrite.rhs.clone(),
                    rhs: rewrite.lhs.clone(),
                    conditions: rewrite.conditions.clone(),
                };
                let forward_added = register_managed_direction(
                    rewrite,
                    &mut installed_rewrite_directions,
                    &mut function_names,
                    &mut rewrites,
                );
                let reverse_added = register_managed_direction(
                    reverse,
                    &mut installed_rewrite_directions,
                    &mut function_names,
                    &mut rewrites,
                );
                if forward_added || reverse_added {
                    rewrite_count = rewrite_count.saturating_add(1);
                }
            }
            Command::Rewrite(_, _, true) => {
                return Err(LiveMonitorError::NonMonotoneUpdate(":subsume".to_owned()));
            }
            other => {
                return Err(LiveMonitorError::UnsupportedManagedSaturationCommand(
                    command_kind(&other).to_owned(),
                ));
            }
        }
    }

    let mut saturation_reach = names.saturation_reach.clone();
    let mut projected_functions = names.projected_functions.clone();
    let mut declarations = Vec::new();
    let saturation_initialized = names.saturation_initialized || !rewrites.is_empty();
    if !names.saturation_initialized && !rewrites.is_empty() {
        for sort in names.sorts.values() {
            let (Some(target_reach), Some(saturation_reach)) =
                (&sort.reach, names.saturation_reach.get(&sort.name))
            else {
                continue;
            };
            declarations.push(reach_bridge_rule(
                &names.saturation_ruleset,
                target_reach,
                saturation_reach,
            ));
        }
    }
    if saturation_initialized {
        function_names.extend(names.known_functions.iter().cloned());
        append_saturation_projections(
            egraph,
            &names.saturation_ruleset,
            private_prefix,
            function_names,
            &mut saturation_reach,
            &mut projected_functions,
            &mut declarations,
        );
    }
    for rewrite in &rewrites {
        append_guarded_direction(egraph, &saturation_reach, names, rewrite, &mut declarations)?;
    }
    Ok(ManagedRewritePlan {
        commands: declarations,
        saturation_reach,
        saturation_initialized,
        projected_functions,
        installed_rewrite_directions,
        rewrite_count,
    })
}

fn register_managed_direction(
    rewrite: Rewrite,
    installed_rewrite_directions: &mut BTreeSet<String>,
    function_names: &mut BTreeSet<String>,
    rewrites: &mut Vec<Rewrite>,
) -> bool {
    if !installed_rewrite_directions.insert(rewrite_direction_key(&rewrite)) {
        return false;
    }
    collect_rewrite_functions(&rewrite, function_names);
    rewrites.push(rewrite);
    true
}

fn append_saturation_projections(
    egraph: &EGraph,
    ruleset: &str,
    private_prefix: &str,
    function_names: impl IntoIterator<Item = String>,
    reaches: &mut BTreeMap<String, String>,
    projected_functions: &mut BTreeSet<String>,
    declarations: &mut Vec<Command>,
) {
    for function_name in function_names {
        if projected_functions.contains(&function_name) {
            continue;
        }
        let Some(function) = egraph.get_function(&function_name) else {
            // Primitive calls have no e-graph table whose children could be
            // congruence-relevant.
            continue;
        };
        let schema = function.schema();
        let output_is_equality = schema.output.is_eq_sort();
        let output_sort = schema.output.name().to_owned();
        let input_sorts = schema.input.clone();
        let ordinal = projected_functions.len();
        projected_functions.insert(function_name.clone());
        if !output_is_equality {
            continue;
        }
        let output_reach =
            ensure_reach_relation(reaches, private_prefix, &output_sort, declarations);
        let mut equality_children = Vec::new();
        for (argument, sort) in input_sorts.iter().enumerate() {
            if sort.is_eq_sort() {
                let reach =
                    ensure_reach_relation(reaches, private_prefix, sort.name(), declarations);
                equality_children.push((argument, reach));
            }
        }
        if !equality_children.is_empty() {
            declarations.push(projection_rule(
                ruleset,
                private_prefix,
                ordinal,
                &function_name,
                input_sorts.len(),
                &output_reach,
                &equality_children,
            ));
        }
    }
}

fn rewrite_direction_key(rewrite: &Rewrite) -> String {
    Command::Rewrite(String::new(), rewrite.clone(), false).to_string()
}

fn ensure_reach_relation(
    reaches: &mut BTreeMap<String, String>,
    private_prefix: &str,
    sort: &str,
    declarations: &mut Vec<Command>,
) -> String {
    if let Some(reach) = reaches.get(sort) {
        return reach.clone();
    }
    let reach = format!("{private_prefix}_aux_reach_{}", reaches.len());
    declarations.push(Command::Relation {
        span: egglog::span!(),
        name: reach.clone(),
        inputs: vec![sort.to_owned()],
    });
    reaches.insert(sort.to_owned(), reach.clone());
    reach
}

fn reach_bridge_rule(ruleset: &str, source: &str, destination: &str) -> Command {
    let value = Expr::Var(egglog::span!(), "saturation_value".to_owned());
    Command::Rule {
        rule: Rule {
            span: egglog::span!(),
            head: GenericActions(vec![EggAction::Expr(
                egglog::span!(),
                Expr::Call(egglog::span!(), destination.to_owned(), vec![value.clone()]),
            )]),
            body: vec![Fact::Fact(Expr::Call(
                egglog::span!(),
                source.to_owned(),
                vec![value],
            ))],
            name: format!("{destination}_bridge"),
            ruleset: ruleset.to_owned(),
        },
    }
}

fn projection_rule(
    ruleset: &str,
    private_prefix: &str,
    ordinal: usize,
    function: &str,
    arity: usize,
    output_reach: &str,
    equality_children: &[(usize, String)],
) -> Command {
    let output = Expr::Var(egglog::span!(), "relevant_output".to_owned());
    let children = (0..arity)
        .map(|argument| Expr::Var(egglog::span!(), format!("relevant_child_{argument}")))
        .collect::<Vec<_>>();
    let body = vec![
        Fact::Fact(Expr::Call(
            egglog::span!(),
            output_reach.to_owned(),
            vec![output.clone()],
        )),
        Fact::Eq(
            egglog::span!(),
            output,
            Expr::Call(egglog::span!(), function.to_owned(), children.clone()),
        ),
    ];
    let head = equality_children
        .iter()
        .map(|(argument, reach)| {
            EggAction::Expr(
                egglog::span!(),
                Expr::Call(
                    egglog::span!(),
                    reach.clone(),
                    vec![children[*argument].clone()],
                ),
            )
        })
        .collect();
    Command::Rule {
        rule: Rule {
            span: egglog::span!(),
            head: GenericActions(head),
            body,
            name: format!("{private_prefix}_dynamic_projection_{ordinal}"),
            ruleset: ruleset.to_owned(),
        },
    }
}

fn append_guarded_direction(
    egraph: &mut EGraph,
    reaches: &BTreeMap<String, String>,
    names: &MatcherNames,
    rewrite: &Rewrite,
    output: &mut Vec<Command>,
) -> Result<(), LiveMonitorError> {
    let sort = expression_sort(egraph, &rewrite.lhs)
        .or_else(|| expression_sort(egraph, &rewrite.rhs))
        .ok_or(LiveMonitorError::UnsupportedManagedRewrite)?;
    let reach = reaches
        .get(&sort)
        .ok_or(LiveMonitorError::UnsupportedManagedRewrite)?;
    // Every managed direction is forward-only and fires only when its LHS is
    // already in the target-rooted saturation basin. A birewrite reaches this
    // helper twice, once for each direction.
    output.push(guarded_rewrite(
        &names.relevant_ruleset,
        rewrite,
        reach,
        &rewrite.lhs,
    ));
    Ok(())
}

fn guarded_rewrite(ruleset: &str, rewrite: &Rewrite, reach: &str, guard: &Expr) -> Command {
    let mut guarded = rewrite.clone();
    guarded.conditions.push(Fact::Fact(Expr::Call(
        egglog::span!(),
        reach.to_owned(),
        vec![guard.clone()],
    )));
    Command::Rewrite(ruleset.to_owned(), guarded, false)
}

fn expression_sort(egraph: &mut EGraph, expression: &Expr) -> Option<String> {
    match expression {
        Expr::Call(_, function, _) => egraph
            .get_function(function)
            .map(|function| function.schema().output.name().to_owned()),
        Expr::Var(_, variable) if variable.starts_with('$') => egraph
            .eval_expr(expression)
            .ok()
            .map(|(sort, _)| sort.name().to_owned()),
        Expr::Var(..) | Expr::Lit(..) => None,
    }
}

fn collect_rewrite_functions(rewrite: &Rewrite, functions: &mut BTreeSet<String>) {
    collect_expr_functions(&rewrite.lhs, functions);
    collect_expr_functions(&rewrite.rhs, functions);
    for condition in &rewrite.conditions {
        match condition {
            Fact::Eq(_, left, right) => {
                collect_expr_functions(left, functions);
                collect_expr_functions(right, functions);
            }
            Fact::Fact(expression) => collect_expr_functions(expression, functions),
        }
    }
}

fn collect_expr_functions(expression: &Expr, functions: &mut BTreeSet<String>) {
    if let Expr::Call(_, function, children) = expression {
        functions.insert(function.clone());
        for child in children {
            collect_expr_functions(child, functions);
        }
    }
}

fn command_kind(command: &Command) -> &'static str {
    match command {
        Command::Sort(..) => "sort",
        Command::Function { .. } => "function",
        Command::Constructor { .. } => "constructor",
        Command::Relation { .. } => "relation",
        Command::Datatype { .. } => "datatype",
        Command::Datatypes { .. } => "datatypes",
        Command::AddRuleset(..) => "ruleset",
        Command::UnstableCombinedRuleset(..) => "combined-ruleset",
        Command::Rule { .. } => "rule",
        Command::Rewrite(..) => "rewrite",
        Command::BiRewrite(..) => "birewrite",
        Command::Action(..) => "action",
        Command::Extract(..) => "extract",
        Command::RunSchedule(..) => "run-schedule",
        Command::PrintOverallStatistics(..) => "print-stats",
        Command::Check(..) => "check",
        Command::Push(..) => "push",
        Command::Pop(..) => "pop",
        Command::PrintFunction(..) => "print-function",
        Command::PrintSize(..) => "print-size",
        Command::Input { .. } => "input",
        Command::Output { .. } => "output",
        Command::Fail(..) => "fail",
        Command::Include(..) => "include",
        Command::UserDefined(..) => "user-defined",
    }
}

fn normalize_binding(binding: &str) -> Result<String, LiveMonitorError> {
    let binding = binding.trim();
    if binding.is_empty() || binding.chars().any(char::is_whitespace) {
        return Err(LiveMonitorError::InvalidBinding {
            binding: binding.to_owned(),
            reason: "expected one nonempty global name".to_owned(),
        });
    }
    Ok(if binding.starts_with('$') {
        binding.to_owned()
    } else {
        format!("${binding}")
    })
}

fn choose_prefix(egraph: &EGraph, initial_program: &str) -> String {
    for index in 0usize.. {
        let prefix = format!("__prefixspace_live_{index}");
        if !initial_program.contains(&prefix)
            && egraph.get_function(&format!("{prefix}_targets")).is_none()
            && egraph.get_function(&format!("{prefix}_reach_0")).is_none()
        {
            return prefix;
        }
    }
    unreachable!()
}

/// Egglog identifiers are unquoted atoms. Ignore comments and escaped string
/// contents before looking for a private-name prefix, so ordinary user data
/// cannot collide with the monitor's capability boundary.
fn source_mentions_identifier_prefix(source: &str, prefix: &str) -> bool {
    let mut visible = String::with_capacity(source.len());
    let mut characters = source.chars();
    let mut in_string = false;
    let mut in_comment = false;
    while let Some(character) = characters.next() {
        if in_comment {
            if character == '\n' {
                in_comment = false;
                visible.push('\n');
            }
            continue;
        }
        if in_string {
            if character == '\\' {
                let _ = characters.next();
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        match character {
            ';' => in_comment = true,
            '"' => in_string = true,
            _ => visible.push(character),
        }
    }
    visible.contains(prefix)
}

fn build_specs(
    grammar: &Grammar,
    egraph: &EGraph,
    input: &RuntimeInput,
    prefix: &str,
    target_sort: &str,
    declared_constructors: &BTreeSet<String>,
    known_functions: BTreeSet<String>,
) -> Result<MatcherNames, LiveMonitorError> {
    let mut constructors = HashMap::<String, ConstructorSpec>::new();
    let mut sorts = BTreeMap::<String, ArcSort>::new();
    let target = egraph
        .get_sort_by_name(target_sort)
        .expect("target sort was returned by egglog")
        .clone();
    sorts.insert(target_sort.to_owned(), target);
    let mut token_usages = BTreeSet::<(usize, String)>::new();
    // A terminal's egglog sort is not necessarily visible at the production
    // which selects it.  Unit productions such as `id: ID { $1 }` pass that
    // value through, and the required sort can be imposed by a constructor
    // arbitrarily far up the chain (or by the distinguished start value).
    // Track those equality constraints for every grammar symbol, then close
    // the Project edges below before installing the lexical matcher rules.
    let nonterminal_count = grammar.nonterminal_count();
    let mut symbol_sorts =
        vec![BTreeSet::<String>::new(); nonterminal_count + grammar.terminal_count()];
    symbol_sorts[grammar.start().index()].insert(target_sort.to_owned());

    let symbol_index = |symbol: Symbol| match symbol {
        Symbol::Nonterminal(nonterminal) => nonterminal.index(),
        Symbol::Terminal(terminal) => nonterminal_count + terminal.index(),
    };

    for production in grammar.productions() {
        let Action::Construct {
            constructor,
            arguments,
        } = &production.action
        else {
            continue;
        };
        let function = egraph
            .get_function(constructor)
            .ok_or_else(|| LiveMonitorError::MissingConstructor(constructor.clone()))?;
        if !declared_constructors.contains(constructor) {
            return Err(LiveMonitorError::NonConstructorAction(constructor.clone()));
        }
        let schema = function.schema();
        if schema.input.len() != arguments.len() {
            return Err(LiveMonitorError::ConstructorArity {
                constructor: constructor.clone(),
                expected: arguments.len(),
                actual: schema.input.len(),
            });
        }
        sorts.insert(schema.output.name().to_owned(), schema.output.clone());
        for sort in &schema.input {
            sorts.insert(sort.name().to_owned(), sort.clone());
        }
        symbol_sorts[production.lhs.index()].insert(schema.output.name().to_owned());
        let constructor_index = constructors.len();
        constructors
            .entry(constructor.clone())
            .or_insert_with(|| ConstructorSpec {
                id: constructor_index,
                name: constructor.clone(),
                capture: format!("{prefix}_capture_constructor_{constructor_index}"),
                inputs: schema
                    .input
                    .iter()
                    .map(|sort| sort.name().to_owned())
                    .collect(),
                output: schema.output.name().to_owned(),
            });
        for (argument, sort) in arguments.iter().zip(&schema.input) {
            let selected = production.rhs[*argument - 1];
            symbol_sorts[symbol_index(selected)].insert(sort.name().to_owned());
        }
    }

    // Project actions are semantic equalities.  Propagate in both directions:
    // a parent constructor can determine the projected child's sort, while a
    // constructed child can determine the projecting nonterminal's sort.
    loop {
        let mut changed = false;
        for production in grammar.productions() {
            let Action::Project { position } = &production.action else {
                continue;
            };
            let lhs = production.lhs.index();
            let rhs = symbol_index(production.rhs[*position - 1]);
            let union = symbol_sorts[lhs]
                .union(&symbol_sorts[rhs])
                .cloned()
                .collect::<Vec<_>>();
            let lhs_len = symbol_sorts[lhs].len();
            let rhs_len = symbol_sorts[rhs].len();
            symbol_sorts[lhs].extend(union.iter().cloned());
            symbol_sorts[rhs].extend(union);
            changed |= symbol_sorts[lhs].len() != lhs_len || symbol_sorts[rhs].len() != rhs_len;
        }
        if !changed {
            break;
        }
    }

    for terminal_index in 0..grammar.terminal_count() {
        let terminal = TerminalId(terminal_index);
        for sort_name in &symbol_sorts[nonterminal_count + terminal_index] {
            let sort = &sorts[sort_name];
            if !input.has_lexer() {
                return Err(LiveMonitorError::SelectedTerminalWithoutLexer(
                    grammar.terminal_name(terminal).to_owned(),
                ));
            }
            if PrimitiveKind::from_sort(sort).is_none() {
                return Err(LiveMonitorError::UnsupportedLexicalSort {
                    terminal: grammar.terminal_name(terminal).to_owned(),
                    sort: sort_name.clone(),
                });
            }
            token_usages.insert((terminal_index, sort_name.clone()));
        }
    }

    let sort_specs = sorts
        .into_iter()
        .enumerate()
        .map(|(index, (name, sort))| {
            let primitive = PrimitiveKind::from_sort(&sort);
            if !sort.is_eq_sort() && primitive.is_none() {
                return Err(LiveMonitorError::UnsupportedSemanticSort(name));
            }
            let spec = SortSpec {
                id: index,
                name: name.clone(),
                reach: sort.is_eq_sort().then(|| format!("{prefix}_reach_{index}")),
                domain: primitive.map(|_| format!("{prefix}_domain_{index}")),
                capture_domain: primitive.map(|_| format!("{prefix}_capture_domain_{index}")),
                primitive,
            };
            Ok((name, spec))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let mut token_sorts = vec![Vec::new(); grammar.terminal_count()];
    for (terminal, sort) in token_usages {
        let kind = sort_specs[&sort].primitive.unwrap();
        token_sorts[terminal].push(TokenSortSpec { sort, kind });
    }
    let saturation_reach = sort_specs
        .iter()
        .filter_map(|(sort, spec)| {
            spec.reach.as_ref().map(|_| {
                (
                    sort.clone(),
                    format!("{prefix}_saturation_reach_{}", spec.id),
                )
            })
        })
        .collect();
    // Source-side saturation rules are installed lazily with the first
    // managed rewrite so monitors that only consume external egglog updates
    // retain the original target-projection cost.
    let projected_functions = BTreeSet::new();
    Ok(MatcherNames {
        target_sort: target_sort.to_owned(),
        ruleset: format!("{prefix}_rules"),
        saturation_ruleset: format!("{prefix}_saturation_rules"),
        relevant_ruleset: format!("{prefix}_relevant_rules"),
        free_ruleset: None,
        free_reach: BTreeMap::new(),
        disjoint_relation: None,
        capture_disjoint: None,
        targets: format!("{prefix}_targets"),
        sorts: sort_specs,
        saturation_reach,
        saturation_initialized: false,
        projected_functions,
        known_functions,
        installed_rewrite_directions: BTreeSet::new(),
        constructors,
        token_sorts,
    })
}

fn register_capture_primitives(egraph: &mut EGraph, names: &MatcherNames, buffer: CaptureBuffer) {
    for constructor in names.constructors.values() {
        let mut sorts = Vec::with_capacity(constructor.inputs.len() + 1);
        sorts.push(
            egraph
                .get_sort_by_name(&constructor.output)
                .expect("constructor output sort was checked")
                .clone(),
        );
        sorts.extend(constructor.inputs.iter().map(|name| {
            egraph
                .get_sort_by_name(name)
                .expect("constructor input sort was checked")
                .clone()
        }));
        egraph.add_primitive(CaptureEnode {
            name: constructor.capture.clone(),
            sorts,
            constructor: constructor.id,
            buffer: buffer.clone(),
        });
    }
    for sort in names.sorts.values() {
        let (Some(kind), Some(capture)) = (sort.primitive, &sort.capture_domain) else {
            continue;
        };
        egraph.add_primitive(CaptureDomain {
            name: capture.clone(),
            sort: egraph
                .get_sort_by_name(&sort.name)
                .expect("primitive sort was checked")
                .clone(),
            sort_id: sort.id,
            kind,
            buffer: buffer.clone(),
        });
    }
    if let Some(capture) = &names.capture_disjoint {
        egraph.add_primitive(CaptureDisjoint {
            name: capture.clone(),
            sort: egraph
                .get_sort_by_name(&names.target_sort)
                .expect("target sort was checked")
                .clone(),
            buffer,
        });
    }
}

fn build_realizability_engine(
    grammar: &Grammar,
    input: &RuntimeInput,
    names: &MatcherNames,
) -> RealizabilityEngine {
    let mut terminal_sorts = vec![Vec::new(); grammar.terminal_count()];
    for (terminal, sorts) in names.token_sorts.iter().enumerate() {
        terminal_sorts[terminal].extend(sorts.iter().map(|sort| names.sorts[&sort.sort].id));
    }
    RealizabilityEngine::new(
        input.clone(),
        grammar.terminal_count(),
        names.sorts.len(),
        constructor_schemas(names),
        terminal_sorts,
    )
}

fn constructor_schemas(names: &MatcherNames) -> Vec<ConstructorSchema> {
    let mut constructors = vec![None; names.constructors.len()];
    for constructor in names.constructors.values() {
        constructors[constructor.id] = Some(ConstructorSchema {
            inputs: constructor
                .inputs
                .iter()
                .map(|sort| names.sorts[sort].id)
                .collect(),
            output: names.sorts[&constructor.output].id,
        });
    }
    constructors
        .into_iter()
        .map(|constructor| constructor.expect("constructor IDs are contiguous"))
        .collect()
}

fn build_matcher_program(names: &MatcherNames, target_sort: &str) -> String {
    fn call(name: &str, arguments: &[String]) -> String {
        if arguments.is_empty() {
            format!("({name})")
        } else {
            format!("({name} {})", arguments.join(" "))
        }
    }

    fn demand(sort: &SortSpec) -> &str {
        sort.reach
            .as_deref()
            .or(sort.domain.as_deref())
            .expect("checked semantic sort has a reachability relation")
    }

    let mut source = format!(
        "(ruleset {})\n(ruleset {})\n(ruleset {})\n(relation {} ({}))\n",
        names.ruleset, names.saturation_ruleset, names.relevant_ruleset, names.targets, target_sort
    );
    for sort in names.sorts.values() {
        if let Some(reach) = &sort.reach {
            source.push_str(&format!("(relation {reach} ({}))\n", sort.name));
        }
        if let Some(domain) = &sort.domain {
            source.push_str(&format!("(relation {domain} ({}))\n", sort.name));
        }
    }
    for (sort, reach) in &names.saturation_reach {
        source.push_str(&format!("(relation {reach} ({sort}))\n"));
    }

    let root_reach = names.sorts[target_sort]
        .reach
        .as_ref()
        .expect("target is an equality sort");
    source.push_str(&format!(
        "(rule (({} value)) (({} value)) :ruleset {})\n",
        names.targets, root_reach, names.ruleset
    ));

    if let (Some(relation), Some(capture)) = (&names.disjoint_relation, &names.capture_disjoint) {
        let same = format!("{}_disjoint_same", names.targets);
        let candidate = format!("{}_disjoint_candidate", names.targets);
        let target = format!("{}_disjoint_target", names.targets);
        source.push_str(&format!(
            "(rule (({relation} {same} {same})) ((panic \"disjointness relation `{relation}` contains an equal pair\")) :ruleset {})\n",
            names.ruleset
        ));
        source.push_str(&format!(
            "(rule (({root_reach} {target}) ({relation} {candidate} {target})) (({capture} {candidate} {target})) :ruleset {})\n",
            names.ruleset
        ));
        source.push_str(&format!(
            "(rule (({root_reach} {target}) ({relation} {target} {candidate})) (({capture} {candidate} {target})) :ruleset {})\n",
            names.ruleset
        ));
    }

    for constructor in names.constructors.values() {
        let child_values = (0..constructor.inputs.len())
            .map(|index| format!("value{index}"))
            .collect::<Vec<_>>();
        let mut actions = constructor
            .inputs
            .iter()
            .enumerate()
            .map(|(index, sort)| format!("({} value{index})", demand(&names.sorts[sort])))
            .collect::<Vec<_>>();
        let mut capture_arguments = vec!["output".to_owned()];
        capture_arguments.extend(child_values.iter().cloned());
        actions.push(call(&constructor.capture, &capture_arguments));
        source.push_str(&format!(
            "(rule (({} output) (= output {})) ({}) :ruleset {})\n",
            demand(&names.sorts[&constructor.output]),
            call(&constructor.name, &child_values),
            actions.join(" "),
            names.ruleset
        ));
    }

    for sort in names.sorts.values() {
        if let (Some(domain), Some(capture)) = (&sort.domain, &sort.capture_domain) {
            source.push_str(&format!(
                "(rule (({domain} value)) (({capture} value)) :ruleset {})\n",
                names.ruleset
            ));
        }
    }
    source
}

fn insert_target(
    egraph: &mut EGraph,
    relation: &str,
    binding: Expr,
) -> Result<(), LiveMonitorError> {
    egraph
        .run_program(vec![call_command(relation, vec![binding])])
        .map_err(|error| LiveMonitorError::Egglog(error.to_string()))?;
    Ok(())
}

fn call_command(name: &str, arguments: Vec<Expr>) -> Command {
    Command::Action(EggAction::Expr(
        egglog::span!(),
        Expr::Call(egglog::span!(), name.to_owned(), arguments),
    ))
}

fn fixed_binding_expression(
    request: &PendingBinding,
    constructor_names: &[String],
    private_prefix: &str,
) -> Expr {
    match &request.rhs {
        BindingRhs::Exact(ExactSource::String(value)) => {
            Expr::Lit(egglog::span!(), Literal::String(value.to_string()))
        }
        BindingRhs::Exact(ExactSource::I64(value)) => {
            Expr::Lit(egglog::span!(), Literal::Int(*value))
        }
        BindingRhs::Constructor {
            constructor,
            children,
        } => Expr::Call(
            egglog::span!(),
            constructor_names[*constructor].clone(),
            children
                .iter()
                .map(|child| Expr::Var(egglog::span!(), child.egglog_name(private_prefix)))
                .collect(),
        ),
    }
}

fn validate_disjoint_relation(
    egraph: &EGraph,
    relation: &str,
    target_sort: &str,
) -> Result<(), LiveMonitorError> {
    let function = egraph
        .get_function(relation)
        .ok_or_else(|| LiveMonitorError::UnknownDisjointRelation(relation.to_owned()))?;
    let schema = function.schema();
    let valid = schema.input.len() == 2
        && schema.input.iter().all(|sort| sort.name() == target_sort)
        && schema.output.name() == "Unit";
    if !valid {
        return Err(LiveMonitorError::InvalidDisjointRelation {
            relation: relation.to_owned(),
            sort: target_sort.to_owned(),
        });
    }
    Ok(())
}

fn collect_declared_constructors(commands: &[Command]) -> BTreeSet<String> {
    let mut constructors = BTreeSet::new();
    for command in commands {
        match command {
            Command::Constructor { name, .. } => {
                constructors.insert(name.clone());
            }
            Command::Datatype { variants, .. } => {
                constructors.extend(variants.iter().map(|variant| variant.name.clone()));
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, _, definition) in datatypes {
                    if let Subdatatypes::Variants(variants) = definition {
                        constructors.extend(variants.iter().map(|variant| variant.name.clone()));
                    }
                }
            }
            _ => {}
        }
    }
    constructors
}

fn collect_declared_functions(commands: &[Command]) -> BTreeSet<String> {
    let mut functions = collect_declared_constructors(commands);
    for command in commands {
        if let Command::Function { name, .. } = command {
            functions.insert(name.clone());
        }
    }
    functions
}

fn reject_nonmonotone_commands(commands: &[Command]) -> Result<(), LiveMonitorError> {
    fn reject(name: &str) -> Result<(), LiveMonitorError> {
        Err(LiveMonitorError::NonMonotoneUpdate(name.to_owned()))
    }

    fn reject_operational(name: &str) -> Result<(), LiveMonitorError> {
        Err(LiveMonitorError::UnsupportedUpdateCommand(name.to_owned()))
    }

    fn check_action(action: &EggAction) -> Result<(), LiveMonitorError> {
        match action {
            EggAction::Set(..) => reject("set"),
            EggAction::Change(_, Change::Delete, ..) => reject("delete"),
            EggAction::Change(_, Change::Subsume, ..) => reject("subsume"),
            EggAction::Panic(..) => reject_operational("panic"),
            EggAction::Let(..) | EggAction::Union(..) | EggAction::Expr(..) => Ok(()),
        }
    }

    for command in commands {
        match command {
            Command::Action(action) => check_action(action)?,
            Command::Rule { rule } => {
                for action in &rule.head.0 {
                    check_action(action)?;
                }
            }
            Command::Rewrite(_, _, true) => return reject(":subsume"),
            Command::Push(_) => return reject("push"),
            Command::Pop(..) => return reject("pop"),
            Command::Include(..) => return reject("include"),
            Command::Input { .. } => return reject("input"),
            Command::UserDefined(..) => return reject("user-defined command"),
            Command::Fail(..) => return reject_operational("fail"),
            Command::Extract(..) => return reject_operational("extract"),
            Command::Check(..) => return reject_operational("check"),
            Command::PrintOverallStatistics(..) => return reject_operational("print-stats"),
            Command::PrintFunction(..) => return reject_operational("print-function"),
            Command::PrintSize(..) => return reject_operational("print-size"),
            Command::Output { .. } => return reject_operational("output"),
            Command::Sort(..)
            | Command::Function { .. }
            | Command::Constructor { .. }
            | Command::Relation { .. }
            | Command::Datatype { .. }
            | Command::Datatypes { .. }
            | Command::AddRuleset(..)
            | Command::UnstableCombinedRuleset(..)
            | Command::Rewrite(_, _, false)
            | Command::BiRewrite(..)
            | Command::RunSchedule(..) => {}
        }
    }
    Ok(())
}
