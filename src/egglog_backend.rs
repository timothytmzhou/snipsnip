use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::{Arc, RwLock},
};

use egglog::{
    ArcSort, EGraph, RawValues, Read, Value, Write,
    ast::{
        Action as EggAction, Change, Command, Expr, GenericActions, GenericExpr, GenericFact,
        ResolvedCommand, ResolvedVar, Rule as EggRule, RuleEvalMode,
    },
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
pub(crate) struct BackendDelta {
    pub(crate) changes: Vec<EGraphChange>,
    /// More focused rule work may become useful before the local fixpoint.
    pub(crate) updated: bool,
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
    rules: HashMap<String, ScheduledRule>,
    selected: HashMap<(u32, Option<FocusValue>), u16>,
    deferred: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct MatchRoot {
    variable: String,
    sort: String,
}

#[derive(Clone)]
enum RuleSelector {
    Lhs(MatchRoot),
    Rhs(MatchRoot),
    Global,
}

#[derive(Clone)]
struct ScheduledRule {
    id: u32,
    selector: RuleSelector,
    /// Top-level function whose outputs can satisfy this selector. `None`
    /// means the rule cannot be cheaply ruled out before Egglog queries it.
    anchor: Option<String>,
}

const MAX_MATCHES_PER_RULE_AND_CLASS: u16 = 4_096;
const MATCH_BATCH: usize = 64;

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
        let mut state = self.state.write().unwrap();
        let Some(rule) = state.rules.get(rule).cloned() else {
            return false;
        };

        let mut selected = 0;
        let mut deferred = false;
        for index in 0..matches.match_size() {
            let matched = matches.get_match(index);
            let value = |variable: &MatchRoot| FocusValue {
                sort: variable.sort.clone(),
                value: matched.get_value(&variable.variable),
            };
            let relevant_class = match &rule.selector {
                RuleSelector::Lhs(lhs) => {
                    let lhs = value(lhs);
                    state.focus.contains(&lhs).then_some(Some(lhs))
                }
                RuleSelector::Rhs(rhs) => {
                    let rhs = value(rhs);
                    state.focus.contains(&rhs).then_some(Some(rhs))
                }
                RuleSelector::Global => Some(None),
            };
            let Some(relevant_class) = relevant_class else {
                continue;
            };
            let key = (rule.id, relevant_class);
            if state.selected.get(&key).copied().unwrap_or(0) == MAX_MATCHES_PER_RULE_AND_CLASS {
                continue;
            }
            if selected == MATCH_BATCH {
                deferred = true;
                continue;
            }
            matches.choose(index);
            *state.selected.entry(key).or_default() += 1;
            selected += 1;
        }
        state.deferred |= deferred;
        true
    }
}

struct TargetValue {
    expression: Expr,
    sort_id: SortId,
    value: ValueId,
}

struct ValidatedSchema {
    sorts: Vec<SortSpec>,
    constructors: Vec<ValidatedConstructor>,
    constructor_ids: HashMap<String, ConstructorId>,
    token_sorts: Vec<Vec<TokenSortSpec>>,
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
    target_focus: HashSet<FocusValue>,
    schedule: Arc<RwLock<ScheduleState>>,
    scheduler: SchedulerId,
    intersection_stale: bool,
    pending: Vec<EGraphChange>,
    disjoint_relation: bool,
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
        let run = run_commands(&mut egraph, commands, None);
        if let Some(error) = run.error {
            return Err(error);
        }
        let disjoint_relation = run.disjoint_relation_added;
        let rules = run.rules;

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

        let ValidatedSchema {
            sorts,
            constructors,
            constructor_ids,
            token_sorts,
        } = build_schema(grammar, &input, &egraph, &target_sort)?;
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
                sort_id: target_sort_id,
                value: ValueId(target_value),
            },
            target_focus: HashSet::new(),
            schedule,
            scheduler,
            intersection_stale: false,
            pending: Vec::new(),
            disjoint_relation,
        };
        backend.install_rules(rules);
        backend.rebuild_target_focus();
        backend.begin_focus();
        backend.validate_disjoint()?;
        Ok(BackendInit { backend, schema })
    }

    pub(crate) fn exact_tokens(
        &self,
        terminal: TerminalId,
        lexeme: &str,
        output: &mut crate::realizability::TokenValues,
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
            output.push(TypedClass {
                sort: token.sort,
                class: ValueId(value),
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

    pub(crate) fn canonical_class(&self, value: TypedClass<ValueId>) -> TypedClass<ValueId> {
        TypedClass {
            sort: value.sort,
            class: ValueId(self.canonical(&self.sorts[value.sort].sort, value.class.raw())),
        }
    }

    pub(crate) fn has_disjoint_facts(&self) -> bool {
        self.disjoint_relation
            && self
                .egraph
                .read(|state| state.table_size("Disjoint"))
                .unwrap_or(0)
                != 0
    }

    pub(crate) fn disjoint(&self, left: TypedClass<ValueId>, right: TypedClass<ValueId>) -> bool {
        if !self.disjoint_relation {
            return false;
        }
        if left.sort != self.target.sort_id || right.sort != self.target.sort_id {
            return false;
        }
        let sort = &self.sorts[self.target.sort_id].sort;
        let left = self.canonical(sort, left.class.raw());
        let right = self.canonical(sort, right.class.raw());
        let contains = |first, second| {
            self.egraph
                .read(|state| state.contains("Disjoint", RawValues(vec![first, second])))
                .unwrap_or(false)
        };
        contains(left, right) || contains(right, left)
    }

    pub(crate) fn existing_application(
        &self,
        constructor: ConstructorId,
        children: &[TypedClass<ValueId>],
    ) -> Option<TypedClass<ValueId>> {
        let schema = &self.constructor_schemas[constructor];
        if children.len() != schema.inputs.len()
            || children
                .iter()
                .zip(&schema.inputs)
                .any(|(child, sort)| child.sort != *sort)
        {
            return None;
        }
        let raw = children
            .iter()
            .zip(&schema.inputs)
            .map(|(child, sort)| self.canonical(&self.sorts[*sort].sort, child.class.raw()))
            .collect::<Vec<_>>();
        let value = self
            .egraph
            .read(|state| state.eclass_of(&self.constructors[constructor].name, RawValues(raw)))
            .expect("grammar actions were validated as constructors")?;
        Some(TypedClass {
            sort: schema.output,
            class: ValueId(self.canonical(&self.sorts[schema.output].sort, value)),
        })
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
            .zip(&schema.inputs)
            .map(|(child, sort)| self.canonical(&self.sorts[*sort].sort, child.class.raw()))
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

    /// Starts a new current-prefix focus. Egglog equalities remain monotone,
    /// but classes reachable only from dead parser branches are not scheduled
    /// after the next derivative.
    pub(crate) fn begin_focus(&mut self) {
        let mut schedule = self.schedule.write().unwrap();
        schedule.focus.clone_from(&self.target_focus);
        schedule.deferred = false;
    }

    /// Adds parser-derived classes to the current focus and closes them
    /// downward through grammar constructors. It never writes to Egglog.
    pub(crate) fn saturate_near(
        &mut self,
        values: &[TypedClass<ValueId>],
    ) -> Result<bool, MonitorError> {
        let mut changed = false;
        for value in values {
            let sort = &self.sorts[value.sort];
            changed |= self.add_focus(FocusValue {
                sort: sort.name.clone(),
                value: self.canonical(&sort.sort, value.class.raw()),
            });
        }
        if changed {
            changed |= self.close_focus_downward();
        }
        Ok(changed)
    }

    fn add_focus(&mut self, value: FocusValue) -> bool {
        let mut schedule = self.schedule.write().unwrap();
        schedule.focus.insert(value)
    }

    /// Runs one small batch of relevant user-rule matches. The monitor checks
    /// the current intersection between batches, so a useful equality stops a
    /// productive rule without waiting for global saturation.
    pub(crate) fn saturate_local(&mut self) -> Result<BackendDelta, MonitorError> {
        let (updated, deferred) = self.step_focused_rules()?;
        if updated {
            self.validate_disjoint()?;
            self.intersection_stale = true;
            if self.recanonicalize_focus() {
                self.mark_all();
                self.intersection_stale = false;
            }
            self.close_focus_downward();
        }
        if updated || deferred {
            let mut delta = self.flush_changes()?;
            delta.updated = true;
            return Ok(delta);
        }

        if self.intersection_stale {
            self.mark_all();
            self.intersection_stale = false;
        }
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
        let target_sort = &self.sorts[self.target.sort_id].sort;
        let target = ValueId(self.canonical(target_sort, target));
        if target != self.target.value {
            self.target.value = target;
            self.mark(EGraphChange::Target);
        }
        if !self.pending.is_empty() {
            self.validate_disjoint()?;
        }
        Ok(BackendDelta {
            changes: std::mem::take(&mut self.pending),
            updated: false,
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
        let focus = self.schedule.read().unwrap().focus.clone();
        let run = run_commands(&mut self.egraph, commands, Some(&focus));
        self.disjoint_relation |= run.disjoint_relation_added;
        let relevant_union = run.relevant_union;
        self.install_rules(run.rules);
        let focus_changed = self.recanonicalize_focus();
        if focus_changed || relevant_union {
            self.rebuild_target_focus();
            self.mark_all();
        }
        self.validate_disjoint()?;
        Ok(match run.error {
            None => MutationResult::Applied,
            Some(error) => MutationResult::PartiallyApplied(error),
        })
    }

    fn step_focused_rules(&mut self) -> Result<(bool, bool), MonitorError> {
        let (focus, rules) = {
            let schedule = self.schedule.read().unwrap();
            (
                schedule.focus.clone(),
                schedule
                    .rules
                    .iter()
                    .map(|(name, rule)| (name.clone(), rule.anchor.clone()))
                    .collect::<Vec<_>>(),
            )
        };
        if rules.is_empty() {
            return Ok((false, false));
        }

        let mut updated = false;
        let mut deferred = false;
        for (ruleset, anchor) in rules {
            if anchor
                .as_deref()
                .is_some_and(|anchor| !self.function_output_touches_focus(anchor, &focus))
            {
                continue;
            }
            self.schedule.write().unwrap().deferred = false;
            let report = self
                .egraph
                .step_rules_with_scheduler(self.scheduler, &ruleset)
                .map_err(egglog_error)?;
            updated |= report.updated;
            deferred |= self.schedule.read().unwrap().deferred;
        }
        Ok((updated, deferred))
    }

    fn install_rules(&mut self, rules: Vec<ResolvedRulePlan>) {
        let mut schedule = self.schedule.write().unwrap();
        for rule in rules {
            let id = u32::try_from(schedule.rules.len()).expect("too many Egglog rules");
            schedule.rules.insert(
                rule.name,
                ScheduledRule {
                    id,
                    selector: rule.selector,
                    anchor: rule.anchor,
                },
            );
        }
    }

    fn function_output_touches_focus(
        &self,
        function_name: &str,
        focus: &HashSet<FocusValue>,
    ) -> bool {
        let Some(function) = self.egraph.get_function(function_name) else {
            return false;
        };
        let sort = function.schema().output.clone();
        let sort_name = sort.name().to_owned();
        let mut found = false;
        if self
            .egraph
            .constructor_enodes_while(function_name, |enode| {
                found = focus.contains(&FocusValue {
                    sort: sort_name.clone(),
                    value: self.canonical(&sort, enode.eclass),
                });
                !found
            })
            .is_err()
        {
            let _ = self.egraph.function_entries_while(function_name, |entry| {
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
        let constructors = self
            .egraph
            .functions_iter()
            .filter(|(_, function)| {
                !function.is_hidden()
                    && !function.is_let_binding()
                    && function.schema().output.is_eq_sort()
            })
            .map(|(name, function)| {
                (
                    name.clone(),
                    function.schema().input.clone(),
                    function.schema().output.clone(),
                )
            })
            .collect::<Vec<_>>();
        for (constructor, input_sorts, output_sort) in constructors {
            let _ = self.egraph.constructor_enodes(&constructor, |enode| {
                if enode.subsumed {
                    return;
                }
                let output = FocusValue {
                    sort: output_sort.name().to_owned(),
                    value: self.canonical(&output_sort, enode.eclass),
                };
                let row = children.entry(output).or_default();
                for (&child, sort) in enode.children.iter().zip(&input_sorts) {
                    row.push(FocusValue {
                        sort: sort.name().to_owned(),
                        value: self.canonical(sort, child),
                    });
                }
            });
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

    fn rebuild_target_focus(&mut self) {
        let sort = &self.sorts[self.target.sort_id];
        let target = FocusValue {
            sort: sort.name.clone(),
            value: self.canonical(&sort.sort, self.target.value.raw()),
        };
        self.schedule.write().unwrap().focus = HashSet::from([target]);
        self.close_focus_downward();
        self.target_focus = self.schedule.read().unwrap().focus.clone();
    }

    fn recanonicalize_focus(&mut self) -> bool {
        let old = std::mem::take(&mut self.schedule.write().unwrap().focus);
        let mut new = HashSet::with_capacity(old.len());
        for value in &old {
            if let Some(sort) = self.egraph.get_sort_by_name(&value.sort) {
                new.insert(FocusValue {
                    sort: value.sort.clone(),
                    value: self.canonical(sort, value.value),
                });
            }
        }
        let changed = old != new;
        self.schedule.write().unwrap().focus = new;

        let old_target = std::mem::take(&mut self.target_focus);
        self.target_focus = old_target
            .into_iter()
            .filter_map(|value| {
                self.egraph
                    .get_sort_by_name(&value.sort)
                    .map(|sort| FocusValue {
                        sort: value.sort,
                        value: self.canonical(sort, value.value),
                    })
            })
            .collect();
        changed
    }

    fn canonical(&self, sort: &ArcSort, value: Value) -> Value {
        if !sort.is_eq_sort() {
            return value;
        }
        let class = self.egraph.value_to_class_id(sort, value);
        self.egraph.class_id_to_value(&class)
    }

    fn validate_disjoint(&self) -> Result<(), MonitorError> {
        let Some(function) = self.egraph.get_function("Disjoint") else {
            return Ok(());
        };
        let schema = function.schema();
        let target_sort = &self.sorts[self.target.sort_id].sort;
        if !self.disjoint_relation
            || !valid_disjoint_inputs(schema, target_sort)
            || self
                .egraph
                .constructor_enodes_while("Disjoint", |_| false)
                .is_err()
        {
            return Err(MonitorError::InvalidDisjointRelation {
                relation: "Disjoint".to_owned(),
                sort: target_sort.name().to_owned(),
            });
        }
        let mut reflexive = false;
        self.egraph
            .constructor_enodes_while("Disjoint", |row| {
                if row.children.len() == 2 {
                    reflexive = self.canonical(target_sort, row.children[0])
                        == self.canonical(target_sort, row.children[1]);
                }
                !reflexive
            })
            .map_err(egglog_error)?;
        if reflexive {
            Err(MonitorError::ReflexiveDisjoint)
        } else {
            Ok(())
        }
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

fn valid_disjoint_inputs(schema: &egglog::ResolvedSchema, target_sort: &ArcSort) -> bool {
    schema.input.len() == 2
        && schema
            .input
            .iter()
            .all(|sort| sort.name() == target_sort.name())
}

#[derive(Clone)]
struct ResolvedRulePlan {
    name: String,
    selector: RuleSelector,
    anchor: Option<String>,
}

struct CommandRun {
    rules: Vec<ResolvedRulePlan>,
    relevant_union: bool,
    disjoint_relation_added: bool,
    error: Option<MonitorError>,
}

fn run_commands(
    egraph: &mut EGraph,
    commands: Vec<Command>,
    focus: Option<&HashSet<FocusValue>>,
) -> CommandRun {
    let mut plans = Vec::new();
    let mut relevant_union = false;
    let mut disjoint_relation_added = false;
    for command in commands.into_iter().flat_map(directed_rewrites) {
        relevant_union |= focus.is_some_and(|focus| union_touches_focus(egraph, &command, focus));
        let scheduled = match command {
            Command::Rewrite(_, rewrite, false) => compile_rewrite(egraph, rewrite),
            Command::Rule { .. } => vec![(command, SelectorSpec::Global, None)],
            _ => {
                let is_disjoint_relation = matches!(
                    &command,
                    Command::Relation { name, .. } if name == "Disjoint"
                );
                if let Err(error) = egraph.run_program(vec![command]).map_err(egglog_error) {
                    return CommandRun {
                        rules: plans,
                        relevant_union,
                        disjoint_relation_added,
                        error: Some(error),
                    };
                }
                disjoint_relation_added |= is_disjoint_relation;
                continue;
            }
        };
        for (mut command, selector, anchor) in scheduled {
            let result = (|| -> Result<ResolvedRulePlan, MonitorError> {
                let name = isolate_rule(egraph, &mut command)?;
                let selector = resolve_selector(egraph, &command, selector)?;
                egraph.run_program(vec![command]).map_err(egglog_error)?;
                Ok(ResolvedRulePlan {
                    name,
                    selector,
                    anchor,
                })
            })();
            match result {
                Ok(plan) => plans.push(plan),
                Err(error) => {
                    return CommandRun {
                        rules: plans,
                        relevant_union,
                        disjoint_relation_added,
                        error: Some(error),
                    };
                }
            }
        }
    }
    CommandRun {
        rules: plans,
        relevant_union,
        disjoint_relation_added,
        error: None,
    }
}

#[derive(Clone)]
enum SelectorSpec {
    Lhs(String),
    Rhs(String),
    Global,
}

fn compile_rewrite(
    egraph: &mut EGraph,
    rewrite: egglog::ast::Rewrite,
) -> Vec<(Command, SelectorSpec, Option<String>)> {
    let span = rewrite.span.clone();
    let mut bound = HashSet::new();
    expression_variable_names(&rewrite.lhs, &mut bound);
    for condition in &rewrite.conditions {
        fact_variable_names(condition, &mut bound);
    }
    let mut rhs_variables = HashSet::new();
    expression_variable_names(&rewrite.rhs, &mut rhs_variables);
    let mut used = bound.union(&rhs_variables).cloned().collect::<HashSet<_>>();
    let lhs_name = fresh_rule_variable(egraph, "prefixspace_lhs", &mut used);
    let lhs = Expr::Var(span.clone(), lhs_name.clone());
    let mut body = vec![GenericFact::Eq(
        span.clone(),
        lhs.clone(),
        rewrite.lhs.clone(),
    )];
    body.extend(rewrite.conditions.clone());
    let forward = Command::Rule {
        rule: EggRule {
            span: span.clone(),
            head: GenericActions(vec![EggAction::Union(
                span.clone(),
                lhs.clone(),
                rewrite.rhs.clone(),
            )]),
            body: body.clone(),
            name: String::new(),
            ruleset: String::new(),
            eval_mode: RuleEvalMode::default(),
            no_decomp: true,
            include_subsumed: false,
        },
    };
    let lhs_anchor = expression_head(&rewrite.lhs);
    let rhs_anchor = expression_head(&rewrite.rhs);
    let mut output = vec![(forward, SelectorSpec::Lhs(lhs_name.clone()), lhs_anchor)];

    let rhs_name = fresh_rule_variable(egraph, "prefixspace_rhs", &mut used);
    let rhs = Expr::Var(span.clone(), rhs_name.clone());
    body.push(GenericFact::Eq(span.clone(), rhs.clone(), rewrite.rhs));
    output.push((
        Command::Rule {
            rule: EggRule {
                span: span.clone(),
                head: GenericActions(vec![EggAction::Union(span, lhs, rhs)]),
                body,
                name: String::new(),
                ruleset: String::new(),
                eval_mode: RuleEvalMode::default(),
                no_decomp: true,
                include_subsumed: false,
            },
        },
        SelectorSpec::Rhs(rhs_name),
        rhs_anchor,
    ));
    output
}

fn expression_head(expression: &Expr) -> Option<String> {
    match expression {
        GenericExpr::Call(_, name, _) => Some(name.clone()),
        GenericExpr::Var(..) | GenericExpr::Lit(..) => None,
    }
}

fn fresh_rule_variable(egraph: &mut EGraph, hint: &str, used: &mut HashSet<String>) -> String {
    loop {
        let internal = egraph.parser.symbol_gen.fresh(hint);
        let visible = internal.trim_start_matches('@').to_owned();
        if used.insert(visible.clone()) {
            return visible;
        }
    }
}

fn expression_variable_names(expression: &Expr, output: &mut HashSet<String>) {
    match expression {
        GenericExpr::Var(_, variable) => {
            output.insert(variable.clone());
        }
        GenericExpr::Call(_, _, arguments) => {
            for argument in arguments {
                expression_variable_names(argument, output);
            }
        }
        GenericExpr::Lit(..) => {}
    }
}

fn fact_variable_names(fact: &egglog::ast::Fact, output: &mut HashSet<String>) {
    match fact {
        GenericFact::Eq(_, left, right) => {
            expression_variable_names(left, output);
            expression_variable_names(right, output);
        }
        GenericFact::Fact(expression) => expression_variable_names(expression, output),
    }
}

fn resolve_selector(
    egraph: &EGraph,
    command: &Command,
    selector: SelectorSpec,
) -> Result<RuleSelector, MonitorError> {
    let SelectorSpec::Global = selector else {
        let mut preview = egraph.clone();
        preview.parser.ensure_no_reserved_symbols = false;
        let resolved = preview
            .resolve_program(None, &command.to_string())
            .map_err(egglog_error)?;
        let rule = resolved.iter().find_map(|command| match command {
            ResolvedCommand::Rule { rule } => Some(rule),
            _ => None,
        });
        let Some(rule) = rule else {
            return Err(MonitorError::Egglog(
                "internal rewrite did not resolve to a rule".to_owned(),
            ));
        };
        let roots = predict_resolved_roots(rule, &mut preview.parser.symbol_gen);
        let root = |name: &str| -> Result<MatchRoot, MonitorError> {
            roots.get(name).cloned().ok_or_else(|| {
                MonitorError::Egglog(format!("internal variable {name} was not resolved"))
            })
        };
        return match selector {
            SelectorSpec::Lhs(lhs) => Ok(RuleSelector::Lhs(root(&lhs)?)),
            SelectorSpec::Rhs(rhs) => Ok(RuleSelector::Rhs(root(&rhs)?)),
            SelectorSpec::Global => unreachable!(),
        };
    };
    Ok(RuleSelector::Global)
}

fn predict_resolved_roots(
    rule: &egglog::ast::GenericRule<egglog::ResolvedCall, ResolvedVar>,
    symbol_gen: &mut egglog::util::SymbolGen,
) -> HashMap<String, MatchRoot> {
    fn expression_root(
        expression: &GenericExpr<egglog::ResolvedCall, ResolvedVar>,
        symbol_gen: &mut egglog::util::SymbolGen,
    ) -> Option<ResolvedVar> {
        match expression {
            GenericExpr::Var(_, variable) => Some(variable.clone()),
            GenericExpr::Lit(..) => None,
            GenericExpr::Call(_, function, arguments) => {
                let root = symbol_gen.fresh(function);
                for argument in arguments {
                    expression_root(argument, symbol_gen);
                }
                Some(root)
            }
        }
    }

    let mut roots = HashMap::new();
    for fact in &rule.body {
        match fact {
            GenericFact::Eq(_, left, right) => {
                let left_root = expression_root(left, symbol_gen);
                let right_root = expression_root(right, symbol_gen);
                if let (GenericExpr::Var(_, marker), Some(root)) = (left, right_root.as_ref()) {
                    roots.insert(
                        marker.name.clone(),
                        MatchRoot {
                            variable: root.name.clone(),
                            sort: root.sort.name().to_owned(),
                        },
                    );
                }
                if let (GenericExpr::Var(_, marker), Some(root)) = (right, left_root.as_ref()) {
                    roots.insert(
                        marker.name.clone(),
                        MatchRoot {
                            variable: root.name.clone(),
                            sort: root.sort.name().to_owned(),
                        },
                    );
                }
            }
            GenericFact::Fact(expression) => {
                expression_root(expression, symbol_gen);
            }
        }
    }
    roots
}

fn union_touches_focus(
    egraph: &mut EGraph,
    command: &Command,
    focus: &HashSet<FocusValue>,
) -> bool {
    let Command::Action(EggAction::Union(_, left, right)) = command else {
        return false;
    };
    let Ok((left_sort, left)) = egraph.eval_expr(left) else {
        return false;
    };
    let Ok((right_sort, right)) = egraph.eval_expr(right) else {
        return false;
    };
    if left_sort.name() != right_sort.name() {
        return false;
    }
    let canonical = |value| {
        if left_sort.is_eq_sort() {
            let class = egraph.value_to_class_id(&left_sort, value);
            egraph.class_id_to_value(&class)
        } else {
            value
        }
    };
    let left = canonical(left);
    let right = canonical(right);
    left != right
        && [left, right].into_iter().any(|value| {
            focus.contains(&FocusValue {
                sort: left_sort.name().to_owned(),
                value,
            })
        })
}

fn isolate_rule(egraph: &mut EGraph, command: &mut Command) -> Result<String, MonitorError> {
    let Command::Rule { rule } = command else {
        return Err(MonitorError::Egglog(
            "internal scheduler expected a rule".to_owned(),
        ));
    };
    let name = egraph.parser.symbol_gen.fresh("prefixspace_rule");
    egraph
        .run_program(vec![Command::AddRuleset(rule.span.clone(), name.clone())])
        .map_err(egglog_error)?;
    rule.ruleset = name.clone();
    rule.name = name.clone();
    Ok(name)
}

fn directed_rewrites(command: Command) -> Vec<Command> {
    let Command::BiRewrite(ruleset, rewrite) = command else {
        return vec![command];
    };
    let mut reverse = rewrite.clone();
    reverse.lhs = rewrite.rhs.clone();
    reverse.rhs = rewrite.lhs.clone();
    vec![
        Command::Rewrite(ruleset.clone(), rewrite, false),
        Command::Rewrite(ruleset, reverse, false),
    ]
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
) -> Result<ValidatedSchema, MonitorError> {
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
    Ok(ValidatedSchema {
        sorts,
        constructors,
        constructor_ids,
        token_sorts,
    })
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
