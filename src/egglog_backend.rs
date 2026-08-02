use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::{Arc, RwLock},
};

use egglog::{
    ArcSort, EGraph, RawValues, Read, Value, Write,
    ast::{Action as EggAction, Change, Command, Expr, ResolvedCommand},
    scheduler::{Matches, Scheduler, SchedulerId},
    sort::S,
    util::FreshGen,
};

use crate::{
    error::MonitorError,
    grammar::{Action, Grammar, RuntimeInput, Symbol, TerminalId},
    realizability::{
        Application as CoreApplication, ConstructorId, ConstructorSchema, EGraphChange, SortId,
        TypedClass,
    },
};

/// An Egglog value is meaningful only together with the sort recorded by
/// `TypedClass`. Keeping the raw value opaque prevents the parser side from
/// depending on Egglog's representation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ValueId(Value);

impl ValueId {
    fn raw(self) -> Value {
        self.0
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BackendSchema {
    pub(crate) constructors: Arc<[ConstructorSchema]>,
    constructor_ids: HashMap<String, ConstructorId>,
}

impl BackendSchema {
    pub(crate) fn constructor_id(&self, name: &str) -> ConstructorId {
        self.constructor_ids[name]
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ExactToken {
    pub(crate) sort: SortId,
    pub(crate) value: ValueId,
}

#[derive(Clone, Debug)]
pub(crate) struct BackendDelta {
    pub(crate) changes: Vec<EGraphChange>,
}

pub(crate) struct BackendInit {
    pub(crate) backend: EgglogBackend,
    pub(crate) schema: BackendSchema,
}

pub(crate) enum MutationResult {
    Applied,
    PartiallyApplied(MonitorError),
}

#[derive(Clone, Copy)]
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
    name: String,
    sort: ArcSort,
    primitive: Option<PrimitiveKind>,
}

#[derive(Clone)]
struct ConstructorSpec {
    name: String,
}

struct ValidatedConstructor {
    name: String,
    schema: ConstructorSchema,
}

#[derive(Clone, Copy)]
struct TokenSortSpec {
    sort: SortId,
    kind: PrimitiveKind,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FocusValue {
    sort: String,
    value: Value,
}

#[derive(Default)]
struct ScheduleState {
    focus: HashSet<FocusValue>,
    roots: HashMap<String, MatchRoot>,
    anchors: HashMap<String, Vec<String>>,
    active: HashSet<String>,
}

#[derive(Clone)]
struct MatchRoot {
    variable: String,
    sort: String,
}

/// Egglog computes the matches. This scheduler only decides which already
/// computed matches belong to the part of the e-graph exposed by the current
/// zippers. Matches rejected now remain in Egglog's scheduler worklist and can
/// be selected after a later derivative grows `focus`.
#[derive(Clone)]
struct FocusScheduler {
    state: Arc<RwLock<ScheduleState>>,
}

impl Scheduler for FocusScheduler {
    fn filter_matches(&mut self, rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
        let state = self.state.read().unwrap();
        if let Some(root) = state.roots.get(rule) {
            if state.active.contains(rule) {
                matches.choose_all();
                return true;
            }
            for index in 0..matches.match_size() {
                let value = matches.get_match(index).get_value(&root.variable);
                if state.focus.contains(&FocusValue {
                    sort: root.sort.clone(),
                    value,
                }) {
                    matches.choose(index);
                }
            }
            return true;
        }
        // Egglog's public Scheduler API does not expose the final variables
        // introduced while compiling an ordinary rule. Global execution is
        // therefore the sound fallback for non-rewrite rules.
        matches.choose_all();
        true
    }
}

struct TargetValue {
    expression: Expr,
    sort: ArcSort,
    sort_id: SortId,
    value: ValueId,
}

/// The only semantic database is `egraph`. The remaining fields are immutable
/// schema, scheduler metadata, parser-derived relevant class IDs, and pending
/// change notifications. Constructor rows and lexical domains are read
/// directly from Egglog and are never mirrored here.
pub(crate) struct EgglogBackend {
    egraph: EGraph,
    input: Arc<RuntimeInput>,
    sorts: Vec<SortSpec>,
    constructors: Vec<ConstructorSpec>,
    constructor_schemas: Arc<[ConstructorSchema]>,
    token_sorts: Vec<Vec<TokenSortSpec>>,
    target: TargetValue,
    schedule: Arc<RwLock<ScheduleState>>,
    scheduler: SchedulerId,
    rulesets: Vec<String>,
    rule_roots: HashMap<String, Vec<Option<String>>>,
    pending: Vec<EGraphChange>,
}

impl EgglogBackend {
    pub(crate) fn initialize(
        grammar: &Grammar,
        input: Arc<RuntimeInput>,
        program: &str,
        target_binding: &str,
    ) -> Result<BackendInit, MonitorError> {
        let mut egraph = EGraph::default();
        let commands = egraph.parse_program(None, program).map_err(egglog_error)?;
        reject_nonmonotone_commands(&commands)?;
        let commands = without_schedules(commands);
        let rules = run_commands(&mut egraph, commands)?;

        let target_expression = binding_expression(&mut egraph, target_binding)?;
        let (target_sort, target_value) =
            egraph
                .eval_expr(&target_expression)
                .map_err(|error| MonitorError::InvalidBinding {
                    binding: target_binding.to_owned(),
                    reason: error.to_string(),
                })?;
        if !target_sort.is_eq_sort() {
            return Err(MonitorError::NonEqualityTarget(
                target_sort.name().to_owned(),
            ));
        }

        let (sorts, constructors, constructor_ids, token_sorts) =
            build_schema(grammar, &input, &egraph, &target_sort)?;
        let target_sort_id = sorts
            .iter()
            .position(|sort| sort.name == target_sort.name())
            .expect("target sort is part of the monitored schema");
        let constructor_schemas: Arc<[ConstructorSchema]> = constructors
            .iter()
            .map(|constructor| constructor.schema.clone())
            .collect::<Vec<_>>()
            .into();
        let schema = BackendSchema {
            constructors: constructor_schemas.clone(),
            constructor_ids,
        };

        let schedule = Arc::new(RwLock::new(ScheduleState::default()));
        let scheduler = egraph.add_scheduler(Box::new(FocusScheduler {
            state: schedule.clone(),
        }));
        let mut backend = Self {
            egraph,
            input,
            sorts,
            constructors: constructors
                .into_iter()
                .map(|constructor| ConstructorSpec {
                    name: constructor.name,
                })
                .collect(),
            constructor_schemas,
            token_sorts,
            target: TargetValue {
                expression: target_expression,
                sort: target_sort,
                sort_id: target_sort_id,
                value: ValueId(target_value),
            },
            schedule,
            scheduler,
            rulesets: Vec::new(),
            rule_roots: HashMap::new(),
            pending: Vec::new(),
        };
        backend.install_rules(rules);
        backend.begin_focus();
        Ok(BackendInit { backend, schema })
    }

    pub(crate) fn exact_tokens(
        &self,
        terminal: TerminalId,
        lexeme: &str,
        output: &mut Vec<ExactToken>,
    ) -> Result<(), MonitorError> {
        let Some(sorts) = self.token_sorts.get(terminal.index()) else {
            return Err(MonitorError::InvalidTerminalId(terminal.index()));
        };
        output.clear();
        for token in sorts {
            let value = match token.kind {
                PrimitiveKind::String => self.egraph.base_to_value::<S>(lexeme.to_owned().into()),
                PrimitiveKind::I64 => {
                    let Ok(value) = lexeme.parse::<i64>() else {
                        continue;
                    };
                    self.egraph.base_to_value(value)
                }
            };
            output.push(ExactToken {
                sort: token.sort,
                value: ValueId(value),
            });
        }
        Ok(())
    }

    pub(crate) fn terminal_count(&self) -> usize {
        self.token_sorts.len()
    }

    pub(crate) fn target(&self) -> TypedClass<ValueId> {
        TypedClass {
            sort: self.target.sort_id,
            class: self.target.value,
        }
    }

    /// Visits the current Egglog rows for one grammar constructor. No row is
    /// retained after this call.
    pub(crate) fn for_each_application(
        &self,
        constructor: ConstructorId,
        mut visit: impl FnMut(CoreApplication<ValueId>),
    ) {
        let spec = &self.constructors[constructor];
        let schema = &self.constructor_schemas[constructor];
        self.egraph
            .constructor_enodes(&spec.name, |enode| {
                if enode.subsumed {
                    return;
                }
                let output_sort = &self.sorts[schema.output].sort;
                let output = ValueId(self.canonical(output_sort, enode.eclass));
                let children = enode
                    .children
                    .iter()
                    .zip(&schema.inputs)
                    .map(|(&value, &sort)| ValueId(self.canonical(&self.sorts[sort].sort, value)))
                    .collect();
                visit(CoreApplication { output, children });
            })
            .expect("grammar actions were validated as constructors");
    }

    /// Visits the primitive values which occur in current grammar-constructor
    /// rows and are complete lexemes of `terminal`.
    pub(crate) fn for_each_terminal_value(
        &self,
        terminal: u32,
        mut visit: impl FnMut(TypedClass<ValueId>),
    ) {
        let Some(token_sorts) = self.token_sorts.get(terminal as usize) else {
            return;
        };
        let terminal_id = TerminalId(terminal as usize);
        let mut seen = HashSet::new();
        for (constructor, schema) in self.constructors.iter().zip(&*self.constructor_schemas) {
            self.egraph
                .constructor_enodes(&constructor.name, |enode| {
                    if enode.subsumed {
                        return;
                    }
                    for (&value, &child_sort) in enode.children.iter().zip(&schema.inputs) {
                        for token_sort in token_sorts {
                            if token_sort.sort != child_sort {
                                continue;
                            }
                            let matches = match token_sort.kind {
                                PrimitiveKind::String => {
                                    let string = self.egraph.value_to_base::<S>(value);
                                    self.input.lexeme_matches(terminal_id, string.as_str())
                                }
                                PrimitiveKind::I64 => self.input.i64_lexeme_matches(
                                    terminal_id,
                                    self.egraph.value_to_base::<i64>(value),
                                ),
                            };
                            let value = TypedClass {
                                sort: child_sort,
                                class: ValueId(value),
                            };
                            if matches && seen.insert(value) {
                                visit(value);
                            }
                        }
                    }
                })
                .expect("grammar actions were validated as constructors");
        }
    }

    pub(crate) fn equivalent(&self, left: TypedClass<ValueId>, right: TypedClass<ValueId>) -> bool {
        left.sort == right.sort
            && self.canonical(&self.sorts[left.sort].sort, left.class.raw())
                == self.canonical(&self.sorts[right.sort].sort, right.class.raw())
    }

    pub(crate) fn add_application(
        &mut self,
        constructor: ConstructorId,
        children: &[TypedClass<ValueId>],
    ) -> Result<TypedClass<ValueId>, MonitorError> {
        let schema = &self.constructor_schemas[constructor];
        let output_sort_id = schema.output;
        debug_assert_eq!(children.len(), schema.inputs.len());
        let name = self.constructors[constructor].name.clone();
        let raw = children
            .iter()
            .map(|child| child.class.raw())
            .collect::<Vec<_>>();
        if let Some(value) = self
            .egraph
            .read(|state| state.eclass_of(&name, RawValues(raw.clone())))
            .map_err(egglog_error)?
        {
            return Ok(TypedClass {
                sort: output_sort_id,
                class: ValueId(self.canonical(&self.sorts[output_sort_id].sort, value)),
            });
        }
        let value = self
            .egraph
            .update(|mut state| state.add(&name, RawValues(raw)))
            .map_err(egglog_error)?;
        self.mark_constructor(constructor);
        for terminal in 0..self.token_sorts.len() {
            self.mark(EGraphChange::Terminal(terminal as u32));
        }
        Ok(TypedClass {
            sort: output_sort_id,
            class: ValueId(self.canonical(&self.sorts[output_sort_id].sort, value)),
        })
    }

    /// Starts a synchronization with only the target class in focus.
    pub(crate) fn begin_focus(&mut self) {
        let sort = &self.sorts[self.target.sort_id];
        let target = FocusValue {
            sort: sort.name.clone(),
            value: self.canonical(&sort.sort, self.target.value.raw()),
        };
        let mut schedule = self.schedule.write().unwrap();
        schedule.focus.clear();
        schedule.focus.insert(target);
        drop(schedule);
        self.close_focus_downward();
    }

    /// Adds parser-derived classes to the current focus and closes them
    /// downward through grammar constructors. It never writes to Egglog.
    pub(crate) fn saturate_near(
        &mut self,
        values: &[TypedClass<ValueId>],
    ) -> Result<bool, MonitorError> {
        let mut changed = false;
        {
            let mut schedule = self.schedule.write().unwrap();
            for value in values {
                let sort = &self.sorts[value.sort];
                changed |= schedule.focus.insert(FocusValue {
                    sort: sort.name.clone(),
                    value: self.canonical(&sort.sort, value.class.raw()),
                });
            }
        }
        changed |= self.close_focus_downward();
        Ok(changed)
    }

    /// Runs the current focused worklist to local quiescence. Skipped matches
    /// remain in Egglog's scheduler and are reconsidered when `saturate_near`
    /// adds another class.
    pub(crate) fn saturate_local(&mut self) -> Result<BackendDelta, MonitorError> {
        self.run_focused_rules()?;
        self.flush_changes()
    }

    /// Drains structural changes which have already happened. This never runs
    /// a user rule; the monitor uses it to close the existing intersection
    /// before deciding whether more equality saturation is necessary.
    pub(crate) fn flush_changes(&mut self) -> Result<BackendDelta, MonitorError> {
        let (_, target) = self
            .egraph
            .eval_expr(&self.target.expression)
            .map_err(egglog_error)?;
        self.target.value = ValueId(self.canonical(&self.target.sort, target));
        Ok(BackendDelta {
            changes: std::mem::take(&mut self.pending),
        })
    }

    pub(crate) fn apply_monotone_update(
        &mut self,
        update: &str,
    ) -> Result<MutationResult, MonitorError> {
        let commands = self
            .egraph
            .parse_program(None, update)
            .map_err(egglog_error)?;
        reject_nonmonotone_commands(&commands)?;
        let commands = without_schedules(commands);
        match run_commands(&mut self.egraph, commands) {
            Ok(rules) => {
                self.install_rules(rules);
                self.recanonicalize_focus();
                self.mark_all();
                Ok(MutationResult::Applied)
            }
            Err(error) => {
                // Egglog executes a batch in order, so earlier actions may have
                // landed. Conservatively notify every monitored projection.
                self.recanonicalize_focus();
                self.mark_all();
                Ok(MutationResult::PartiallyApplied(error))
            }
        }
    }

    fn run_focused_rules(&mut self) -> Result<bool, MonitorError> {
        if self.rulesets.is_empty() {
            return Ok(false);
        }
        let mut any_update = false;
        loop {
            self.close_focus_downward();
            let mut updated = false;
            for ruleset in self.rulesets.clone() {
                let ruleset_updated = if self.ruleset_is_fully_focused(&ruleset) {
                    let mut changed = false;
                    loop {
                        let report = self.egraph.step_rules(&ruleset).map_err(egglog_error)?;
                        if !report.updated {
                            break;
                        }
                        changed = true;
                    }
                    changed
                } else {
                    self.refresh_active_rules();
                    let report = self
                        .egraph
                        .step_rules_with_scheduler(self.scheduler, &ruleset)
                        .map_err(egglog_error)?;
                    report.updated
                };
                updated |= ruleset_updated;
            }
            if !updated {
                break;
            }
            any_update = true;
            self.mark_all();
            self.recanonicalize_focus();
        }
        Ok(any_update)
    }

    fn install_rules(&mut self, rules: Vec<ResolvedRulePlan>) {
        if rules.is_empty() {
            return;
        }
        let mut schedule = self.schedule.write().unwrap();
        for rule in rules {
            self.rule_roots
                .entry(rule.ruleset.clone())
                .or_default()
                .push(rule.lhs_anchor.clone());
            if let Some(root) = rule.root {
                schedule.roots.insert(rule.name.clone(), root);
            }
            if !rule.anchors.is_empty() {
                schedule.anchors.insert(rule.name.clone(), rule.anchors);
            }
            if !self.rulesets.contains(&rule.ruleset) {
                self.rulesets.push(rule.ruleset);
            }
        }
    }

    fn ruleset_is_fully_focused(&self, ruleset: &str) -> bool {
        let Some(roots) = self.rule_roots.get(ruleset) else {
            return false;
        };
        !roots.is_empty()
            && roots.iter().all(|root| {
                root.as_deref()
                    .is_some_and(|root| self.anchor_is_fully_focused(root))
            })
    }

    fn anchor_is_fully_focused(&self, anchor: &str) -> bool {
        let Some(function) = self.egraph.get_function(anchor) else {
            return false;
        };
        let sort = function.schema().output.clone();
        let sort_name = sort.name().to_owned();
        let focus = &self.schedule.read().unwrap().focus;
        let mut all = true;
        if self
            .egraph
            .constructor_enodes_while(anchor, |enode| {
                all = focus.contains(&FocusValue {
                    sort: sort_name.clone(),
                    value: self.canonical(&sort, enode.eclass),
                });
                all
            })
            .is_err()
        {
            let _ = self.egraph.function_entries_while(anchor, |entry| {
                all = focus.contains(&FocusValue {
                    sort: sort_name.clone(),
                    value: self.canonical(&sort, entry.output),
                });
                all
            });
        }
        all
    }

    fn refresh_active_rules(&self) {
        let (anchors, focus) = {
            let schedule = self.schedule.read().unwrap();
            (schedule.anchors.clone(), schedule.focus.clone())
        };
        let mut active = HashSet::new();
        for (rule, anchors) in anchors {
            if anchors
                .iter()
                .any(|anchor| self.anchor_touches_focus(anchor, &focus))
            {
                active.insert(rule);
            }
        }
        self.schedule.write().unwrap().active = active;
    }

    fn anchor_touches_focus(&self, anchor: &str, focus: &HashSet<FocusValue>) -> bool {
        let Some(function) = self.egraph.get_function(anchor) else {
            return false;
        };
        let sort = function.schema().output.clone();
        let sort_name = sort.name().to_owned();
        let mut found = false;
        if self
            .egraph
            .constructor_enodes_while(anchor, |enode| {
                found = focus.contains(&FocusValue {
                    sort: sort_name.clone(),
                    value: self.canonical(&sort, enode.eclass),
                });
                !found
            })
            .is_err()
        {
            let _ = self.egraph.function_entries_while(anchor, |entry| {
                found = focus.contains(&FocusValue {
                    sort: sort_name.clone(),
                    value: self.canonical(&sort, entry.output),
                });
                !found
            });
        }
        found
    }

    fn close_focus_downward(&self) -> bool {
        // Read each Egglog row once, then traverse the reachable children in
        // memory. Repeated whole-table scans would make an n-deep target cost
        // O(n²) even though its e-node graph has only n edges.
        let mut children = HashMap::<FocusValue, Vec<FocusValue>>::new();
        for (constructor, schema) in self.constructors.iter().zip(&*self.constructor_schemas) {
            let output_sort = &self.sorts[schema.output];
            self.egraph
                .constructor_enodes(&constructor.name, |enode| {
                    let output = FocusValue {
                        sort: output_sort.name.clone(),
                        value: self.canonical(&output_sort.sort, enode.eclass),
                    };
                    let row = children.entry(output).or_default();
                    for (&child, &sort_id) in enode.children.iter().zip(&schema.inputs) {
                        let sort = &self.sorts[sort_id];
                        row.push(FocusValue {
                            sort: sort.name.clone(),
                            value: self.canonical(&sort.sort, child),
                        });
                    }
                })
                .expect("grammar actions were validated as constructors");
        }

        let mut schedule = self.schedule.write().unwrap();
        let mut agenda = schedule.focus.iter().cloned().collect::<Vec<_>>();
        let mut changed = false;
        while let Some(value) = agenda.pop() {
            let Some(row) = children.get(&value) else {
                continue;
            };
            for child in row {
                if schedule.focus.insert(child.clone()) {
                    changed = true;
                    agenda.push(child.clone());
                }
            }
        }
        changed
    }

    fn recanonicalize_focus(&self) {
        let old = std::mem::take(&mut self.schedule.write().unwrap().focus);
        let mut new = HashSet::with_capacity(old.len());
        for value in old {
            if let Some(sort) = self.egraph.get_sort_by_name(&value.sort) {
                new.insert(FocusValue {
                    sort: value.sort,
                    value: self.canonical(sort, value.value),
                });
            }
        }
        self.schedule.write().unwrap().focus = new;
    }

    fn canonical(&self, sort: &ArcSort, value: Value) -> Value {
        if !sort.is_eq_sort() {
            return value;
        }
        let class = self.egraph.value_to_class_id(sort, value);
        self.egraph.class_id_to_value(&class)
    }

    fn mark_all(&mut self) {
        self.mark(EGraphChange::Target);
        for constructor in 0..self.constructors.len() {
            self.mark_constructor(constructor);
        }
        for terminal in 0..self.token_sorts.len() {
            self.mark(EGraphChange::Terminal(terminal as u32));
        }
    }

    fn mark_constructor(&mut self, constructor: ConstructorId) {
        self.mark(EGraphChange::Constructor(constructor));
    }

    fn mark(&mut self, change: EGraphChange) {
        if !self.pending.contains(&change) {
            self.pending.push(change);
        }
    }
}

struct ResolvedRulePlan {
    name: String,
    ruleset: String,
    lhs_anchor: Option<String>,
    root: Option<MatchRoot>,
    anchors: Vec<String>,
}

fn run_commands(
    egraph: &mut EGraph,
    commands: Vec<Command>,
) -> Result<Vec<ResolvedRulePlan>, MonitorError> {
    let mut plans = Vec::new();
    for command in commands.into_iter().flat_map(directed_rewrites) {
        if !command_defines_rule(&command) {
            egraph.run_program(vec![command]).map_err(egglog_error)?;
            continue;
        }
        // Resolve with Egglog itself, then register exactly that desugaring.
        // The clone prevents the preview's type/name bookkeeping from being
        // applied twice to the real e-graph.
        let mut preview = egraph.clone();
        let resolved = preview
            .resolve_program(None, &command.to_string())
            .map_err(egglog_error)?;
        plans.extend(resolved_rule_plans(
            &resolved,
            &mut preview.parser.symbol_gen,
        ));
        // Register the user's command itself. The resolved copy above is only
        // scheduler metadata; it never replaces user logic.
        egraph.run_program(vec![command]).map_err(egglog_error)?;
    }
    Ok(plans)
}

fn directed_rewrites(command: Command) -> Vec<Command> {
    let Command::BiRewrite(ruleset, rewrite) = command else {
        return vec![command];
    };
    let base = if rewrite.name.is_empty() {
        egglog::ast::desugar::rule_name(&Command::BiRewrite(ruleset.clone(), rewrite.clone()))
    } else {
        rewrite.name.clone()
    };
    let mut forward = rewrite.clone();
    forward.name = format!("{base}=>");
    let reverse = egglog::ast::Rewrite {
        span: rewrite.span,
        lhs: rewrite.rhs,
        rhs: rewrite.lhs,
        conditions: rewrite.conditions,
        name: format!("{base}<="),
    };
    vec![
        Command::Rewrite(ruleset.clone(), forward, false),
        Command::Rewrite(ruleset, reverse, false),
    ]
}

fn resolved_rule_plans(
    resolved: &[ResolvedCommand],
    symbol_gen: &mut egglog::util::SymbolGen,
) -> Vec<ResolvedRulePlan> {
    resolved
        .iter()
        .cloned()
        .into_iter()
        .filter_map(|command| match command {
            ResolvedCommand::Rule { rule } => {
                let lhs = rewrite_lhs(&rule.body);
                let root = lhs.map(|call| {
                    let variable = symbol_gen.fresh(call);
                    MatchRoot {
                        variable: variable.name,
                        sort: variable.sort.name().to_owned(),
                    }
                });
                let lhs_anchor = lhs.map(|call| call.name().to_owned());
                let anchors = rewrite_anchors(lhs, &rule.head.0);
                let plan = ResolvedRulePlan {
                    name: rule.name,
                    ruleset: rule.ruleset,
                    lhs_anchor,
                    root,
                    anchors,
                };
                Some(plan)
            }
            _ => None,
        })
        .collect()
}

fn rewrite_anchors(
    lhs: Option<&egglog::ResolvedCall>,
    actions: &[egglog::ast::GenericAction<egglog::ResolvedCall, egglog::ast::ResolvedVar>],
) -> Vec<String> {
    let Some(lhs) = lhs else {
        return Vec::new();
    };
    let mut anchors = Vec::new();
    for action in actions {
        let egglog::ast::GenericAction::Union(_, _, rhs) = action else {
            continue;
        };
        if let egglog::ast::GenericExpr::Call(_, call, _) = rhs {
            let name = call.name().to_owned();
            if name != lhs.name() && !anchors.contains(&name) {
                anchors.push(name);
            }
        }
    }
    anchors
}

fn rewrite_lhs(facts: &[egglog::ast::ResolvedFact]) -> Option<&egglog::ResolvedCall> {
    facts.iter().find_map(|fact| {
        let egglog::ast::GenericFact::Eq(_, left, right) = fact else {
            return None;
        };
        match (left, right) {
            (
                egglog::ast::GenericExpr::Var(_, variable),
                egglog::ast::GenericExpr::Call(_, call, _),
            )
            | (
                egglog::ast::GenericExpr::Call(_, call, _),
                egglog::ast::GenericExpr::Var(_, variable),
            ) if variable.name.contains("rewrite_var__") => Some(call),
            _ => None,
        }
    })
}

fn command_defines_rule(command: &Command) -> bool {
    matches!(
        command,
        Command::Rule { .. } | Command::Rewrite(..) | Command::BiRewrite(..)
    )
}

fn without_schedules(commands: Vec<Command>) -> Vec<Command> {
    commands
        .into_iter()
        .filter(|command| !matches!(command, Command::RunSchedule(..)))
        .collect()
}

fn binding_expression(egraph: &mut EGraph, binding: &str) -> Result<Expr, MonitorError> {
    let trimmed = binding.trim();
    if trimmed.is_empty() || trimmed.chars().any(char::is_whitespace) {
        return Err(MonitorError::InvalidBinding {
            binding: binding.to_owned(),
            reason: "expected one nonempty global name".to_owned(),
        });
    }
    let source = if trimmed.starts_with('$') {
        trimmed.to_owned()
    } else {
        format!("${trimmed}")
    };
    let expression = egraph
        .parser
        .get_expr_from_string(None, &source)
        .map_err(|error| MonitorError::InvalidBinding {
            binding: binding.to_owned(),
            reason: error.to_string(),
        })?;
    if !matches!(expression, Expr::Var(..)) {
        return Err(MonitorError::InvalidBinding {
            binding: binding.to_owned(),
            reason: "expected one global name".to_owned(),
        });
    }
    Ok(expression)
}

fn build_schema(
    grammar: &Grammar,
    input: &RuntimeInput,
    egraph: &EGraph,
    target_sort: &ArcSort,
) -> Result<
    (
        Vec<SortSpec>,
        Vec<ValidatedConstructor>,
        HashMap<String, ConstructorId>,
        Vec<Vec<TokenSortSpec>>,
    ),
    MonitorError,
> {
    let mut sort_map = BTreeMap::<String, ArcSort>::new();
    sort_map.insert(target_sort.name().to_owned(), target_sort.clone());
    let mut constructor_names = Vec::<String>::new();
    let mut constructor_ids = HashMap::<String, ConstructorId>::new();
    let nonterminals = grammar.nonterminal_count();
    let mut symbol_sorts = vec![BTreeSet::<String>::new(); nonterminals + grammar.terminal_count()];
    symbol_sorts[grammar.start().index()].insert(target_sort.name().to_owned());
    let symbol_index = |symbol: Symbol| match symbol {
        Symbol::Nonterminal(nonterminal) => nonterminal.index(),
        Symbol::Terminal(terminal) => nonterminals + terminal.index(),
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
            .ok_or_else(|| MonitorError::MissingConstructor(constructor.clone()))?;
        if egraph.constructor_enodes(constructor, |_| {}).is_err() {
            return Err(MonitorError::NonConstructorAction(constructor.clone()));
        }
        let schema = function.schema();
        if schema.input.len() != arguments.len() {
            return Err(MonitorError::ConstructorArity {
                constructor: constructor.clone(),
                expected: arguments.len(),
                actual: schema.input.len(),
            });
        }
        if !constructor_ids.contains_key(constructor) {
            let id = constructor_names.len();
            constructor_ids.insert(constructor.clone(), id);
            constructor_names.push(constructor.clone());
        }
        sort_map.insert(schema.output.name().to_owned(), schema.output.clone());
        symbol_sorts[production.lhs.index()].insert(schema.output.name().to_owned());
        for (position, child_sort) in arguments.iter().zip(&schema.input) {
            sort_map.insert(child_sort.name().to_owned(), child_sort.clone());
            symbol_sorts[symbol_index(production.rhs[*position - 1])]
                .insert(child_sort.name().to_owned());
        }
    }

    loop {
        let mut changed = false;
        for production in grammar.productions() {
            let Action::Project { position } = production.action else {
                continue;
            };
            let left = production.lhs.index();
            let right = symbol_index(production.rhs[position - 1]);
            let union = symbol_sorts[left]
                .union(&symbol_sorts[right])
                .cloned()
                .collect::<Vec<_>>();
            let before = symbol_sorts[left].len() + symbol_sorts[right].len();
            symbol_sorts[left].extend(union.iter().cloned());
            symbol_sorts[right].extend(union);
            changed |= before != symbol_sorts[left].len() + symbol_sorts[right].len();
        }
        if !changed {
            break;
        }
    }

    let sorts = sort_map
        .into_iter()
        .map(|(name, sort)| {
            let primitive = PrimitiveKind::from_sort(&sort);
            if !sort.is_eq_sort() && primitive.is_none() {
                return Err(MonitorError::UnsupportedSemanticSort(name));
            }
            Ok(SortSpec {
                name,
                sort,
                primitive,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let sort_ids = sorts
        .iter()
        .enumerate()
        .map(|(id, sort)| (sort.name.clone(), id))
        .collect::<HashMap<_, _>>();

    let constructors = constructor_names
        .iter()
        .map(|name| {
            let schema = egraph.get_function(name).unwrap().schema();
            ValidatedConstructor {
                name: name.clone(),
                schema: ConstructorSchema {
                    inputs: schema
                        .input
                        .iter()
                        .map(|sort| sort_ids[sort.name()])
                        .collect(),
                    output: sort_ids[schema.output.name()],
                },
            }
        })
        .collect::<Vec<_>>();

    let mut token_sorts = vec![Vec::new(); grammar.terminal_count()];
    for terminal in 0..grammar.terminal_count() {
        for sort_name in &symbol_sorts[nonterminals + terminal] {
            if !input.has_lexer() {
                return Err(MonitorError::SelectedTerminalWithoutLexer(
                    grammar.terminal_name(TerminalId(terminal)).to_owned(),
                ));
            }
            let id = sort_ids[sort_name];
            let Some(kind) = sorts[id].primitive else {
                return Err(MonitorError::UnsupportedLexicalSort {
                    terminal: grammar.terminal_name(TerminalId(terminal)).to_owned(),
                    sort: sort_name.clone(),
                });
            };
            token_sorts[terminal].push(TokenSortSpec { sort: id, kind });
        }
    }
    Ok((sorts, constructors, constructor_ids, token_sorts))
}

fn reject_nonmonotone_commands(commands: &[Command]) -> Result<(), MonitorError> {
    fn reject(name: &str) -> Result<(), MonitorError> {
        Err(MonitorError::NonMonotoneUpdate(name.to_owned()))
    }
    fn reject_operational(name: &str) -> Result<(), MonitorError> {
        Err(MonitorError::UnsupportedUpdateCommand(name.to_owned()))
    }
    fn check_action(action: &EggAction) -> Result<(), MonitorError> {
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
            Command::Prove(..) | Command::ProveExists(..) => return reject_operational("prove"),
            Command::PrintOverallStatistics(..) => return reject_operational("print-stats"),
            Command::PrintFunction(..) => return reject_operational("print-function"),
            Command::PrintSize(..) => return reject_operational("print-size"),
            Command::Output { .. } => return reject_operational("output"),
            _ => {}
        }
    }
    Ok(())
}

fn egglog_error(error: impl ToString) -> MonitorError {
    MonitorError::Egglog(error.to_string())
}
