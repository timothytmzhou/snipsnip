use std::sync::Arc;

use egglog::Value;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;

use crate::{
    dataflow::DeltaEngine,
    forest::{ContextId, MemoId, SpaceId},
    grammar::{RuntimeInput, TerminalId},
};

pub(crate) type SortId = usize;
pub(crate) type ConstructorId = usize;
type ContinuationOutputIndex = HashMap<(Value, Option<usize>), Vec<usize>>;
type ContinuationChildIndex = HashMap<(Value, Option<usize>), Vec<usize>>;
type ValueSet = SmallVec<[Value; 4]>;

const NO_VALUE: Value = Value::new_const(u32::MAX);
const WIDE_ROW_THRESHOLD: usize = 8;

#[derive(Clone, Copy, Debug)]
struct ValueCell {
    first: Value,
    rest: u32,
}

impl Default for ValueCell {
    fn default() -> Self {
        Self {
            first: NO_VALUE,
            rest: NO_EDGE,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ValueEdge {
    value: Value,
    next: u32,
}

/// A dense relation whose overwhelmingly common row contains zero or one
/// e-value. Keeping that row to eight bytes avoids paying a `SmallVec` header
/// for every historical PwZ space, memo, and context. Ambiguous rows spill to
/// one shared linked arena and remain unbounded.
#[derive(Clone, Debug, Default)]
struct CompactValueRelation {
    cells: Vec<ValueCell>,
    edges: Vec<ValueEdge>,
    /// Membership acceleration for the exceptional high-cardinality rows.
    /// Common zero/one-value rows still cost only one eight-byte `ValueCell`.
    wide_rows: HashMap<usize, HashSet<Value>>,
    pairs: usize,
}

impl CompactValueRelation {
    fn insert(&mut self, index: usize, value: Value) -> bool {
        if self.cells.len() <= index {
            self.cells.resize(index + 1, ValueCell::default());
        }
        let cell = self.cells[index];
        if cell.first == NO_VALUE {
            self.cells[index].first = value;
            self.pairs = self.pairs.saturating_add(1);
            return true;
        }
        if cell.first == value {
            return false;
        }
        if let Some(values) = self.wide_rows.get_mut(&index) {
            if !values.insert(value) {
                return false;
            }
            self.push_edge(index, value, cell.rest);
            return true;
        }
        let mut edge = cell.rest;
        let mut row_len = 1;
        while edge != NO_EDGE {
            let row = self.edges[edge as usize];
            if row.value == value {
                return false;
            }
            row_len += 1;
            edge = row.next;
        }
        if row_len >= WIDE_ROW_THRESHOLD {
            let mut values = HashSet::default();
            values.reserve(row_len + 1);
            values.insert(cell.first);
            let mut edge = cell.rest;
            while edge != NO_EDGE {
                let row = self.edges[edge as usize];
                values.insert(row.value);
                edge = row.next;
            }
            values.insert(value);
            self.wide_rows.insert(index, values);
        }
        self.push_edge(index, value, cell.rest);
        true
    }

    fn push_edge(&mut self, index: usize, value: Value, next: u32) {
        let edge =
            u32::try_from(self.edges.len()).expect("realizability relation capacity exceeded");
        self.edges.push(ValueEdge { value, next });
        self.cells[index].rest = edge;
        self.pairs = self.pairs.saturating_add(1);
    }

    fn contains(&self, index: usize, value: Value) -> bool {
        let Some(cell) = self.cells.get(index).copied() else {
            return false;
        };
        if cell.first == value {
            return true;
        }
        if let Some(values) = self.wide_rows.get(&index) {
            return values.contains(&value);
        }
        let mut edge = cell.rest;
        while edge != NO_EDGE {
            let row = self.edges[edge as usize];
            if row.value == value {
                return true;
            }
            edge = row.next;
        }
        false
    }

    fn values(&self, index: usize) -> ValueSet {
        let Some(cell) = self.cells.get(index).copied() else {
            return ValueSet::new();
        };
        if cell.first == NO_VALUE {
            return ValueSet::new();
        }
        let mut values = ValueSet::new();
        values.push(cell.first);
        let mut edge = cell.rest;
        while edge != NO_EDGE {
            let row = self.edges[edge as usize];
            values.push(row.value);
            edge = row.next;
        }
        values
    }

    fn pair_count(&self) -> usize {
        self.pairs
    }
}

fn insert_flag(flags: &mut Vec<bool>, index: usize) -> bool {
    if flags.len() <= index {
        flags.resize(index + 1, false);
    }
    let is_new = !flags[index];
    flags[index] = true;
    is_new
}

fn has_flag(flags: &[bool], index: u32) -> bool {
    flags.get(index as usize).copied().unwrap_or(false)
}

const NO_EDGE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
struct AdjacencyEdge<T> {
    value: T,
    next: u32,
}

#[derive(Clone, Debug)]
struct DenseAdjacency<T> {
    heads: Vec<u32>,
    edges: Vec<AdjacencyEdge<T>>,
}

impl<T> Default for DenseAdjacency<T> {
    fn default() -> Self {
        Self {
            heads: Vec::new(),
            edges: Vec::new(),
        }
    }
}

impl<T: Copy> DenseAdjacency<T> {
    fn push(&mut self, key: usize, value: T) {
        if self.heads.len() <= key {
            self.heads.resize(key + 1, NO_EDGE);
        }
        let edge =
            u32::try_from(self.edges.len()).expect("realizability adjacency capacity exceeded");
        self.edges.push(AdjacencyEdge {
            value,
            next: self.heads[key],
        });
        self.heads[key] = edge;
    }

    fn values(&self, key: usize) -> SmallVec<[T; 4]> {
        let mut values = SmallVec::new();
        let mut edge = self.heads.get(key).copied().unwrap_or(NO_EDGE);
        while edge != NO_EDGE {
            let row = self.edges[edge as usize];
            values.push(row.value);
            edge = row.next;
        }
        values
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ConstructorSchema {
    pub(crate) inputs: Vec<SortId>,
    pub(crate) output: SortId,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Enode {
    output: Value,
    children: Arc<[Value]>,
}

#[derive(Clone, Debug)]
struct DomainValue {
    lexical_form: String,
    integer: Option<i64>,
}

#[derive(Clone, Copy, Debug)]
struct SpaceApplication {
    constructor: u32,
    output: SpaceId,
    children_start: u32,
    children_len: u32,
}

impl SpaceApplication {
    fn constructor(self) -> ConstructorId {
        self.constructor as usize
    }
}

#[derive(Clone, Debug)]
struct ProjectFixed {
    context: u32,
    memo: u32,
    child: SpaceId,
}

const NO_HOLE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
struct Continuation {
    constructor: u32,
    context: u32,
    memo: u32,
    hole: u32,
    fixed_start: u32,
    fixed_len: u32,
}

impl Continuation {
    fn constructor(self) -> ConstructorId {
        self.constructor as usize
    }

    fn context(self) -> u32 {
        self.context
    }

    fn memo(self) -> u32 {
        self.memo
    }

    fn hole(self) -> Option<usize> {
        (self.hole != NO_HOLE).then_some(self.hole as usize)
    }

    fn fixed_argument(self, offset: usize) -> usize {
        match self.hole() {
            Some(hole) if offset >= hole => offset + 1,
            _ => offset,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Event {
    Produces {
        sort: SortId,
        space: SpaceId,
        value: Value,
    },
    RealizableForMemo {
        sort: SortId,
        memo: u32,
        value: Value,
    },
    RealizableForContext {
        sort: SortId,
        context: u32,
        value: Value,
    },
    RealizableMemo(u32),
    RealizableContext(u32),
}

/// Insertion-only incremental realizability engine for PwZ and e-graph facts.
///
/// The e-graph contributes only target-reachable constructor rows and lexical
/// domain values. Everything indexed by a PwZ space, memo, or context lives in
/// this worklist, so its history never enters egglog's rebuild path.
pub(crate) struct RealizabilityEngine {
    input: RuntimeInput,
    sort_count: usize,
    constructors: Vec<ConstructorSchema>,
    terminal_sorts: Vec<Vec<SortId>>,
    sort_terminals: Vec<Vec<TerminalId>>,

    enodes: Vec<Vec<Enode>>,
    enode_seen: Vec<HashSet<Enode>>,
    enodes_by_output: Vec<HashMap<Value, Vec<usize>>>,
    enodes_by_child: Vec<Vec<HashMap<Value, Vec<usize>>>>,
    domains: Vec<HashMap<Value, DomainValue>>,

    produces: Vec<CompactValueRelation>,
    aliases_by_child: DenseAdjacency<SpaceId>,
    space_applications: Vec<SpaceApplication>,
    space_application_children: Vec<SpaceId>,
    space_apps_by_constructor: Vec<Vec<usize>>,
    space_uses: Vec<DenseAdjacency<(usize, usize)>>,
    space_apps_by_child: Vec<Vec<HashMap<Value, Vec<usize>>>>,

    token_any: Vec<Vec<SpaceId>>,
    exact_tokens: Vec<HashMap<Value, Vec<SpaceId>>>,

    realizable_for_memos: Vec<CompactValueRelation>,
    realizable_for_contexts: Vec<CompactValueRelation>,
    realizable_memos: Vec<bool>,
    realizable_contexts: Vec<bool>,
    parents_by_context: DenseAdjacency<u32>,
    alternatives_by_memo: DenseAdjacency<u32>,
    project_holes_by_memo: DenseAdjacency<u32>,
    project_fixed: Vec<ProjectFixed>,
    project_fixed_by_memo: DenseAdjacency<usize>,
    project_fixed_by_space: DenseAdjacency<usize>,
    continuations: Vec<Continuation>,
    continuation_fixed_spaces: Vec<SpaceId>,
    continuations_by_memo: DenseAdjacency<usize>,
    continuation_uses: Vec<DenseAdjacency<(usize, usize)>>,
    continuations_by_output: Vec<ContinuationOutputIndex>,
    continuations_by_child: Vec<Vec<ContinuationChildIndex>>,

    targets: Vec<HashSet<Value>>,
    delta: DeltaEngine<Event>,
    last_join_probes: usize,
    total_join_probes: usize,
}

impl RealizabilityEngine {
    pub(crate) fn new(
        input: RuntimeInput,
        terminal_count: usize,
        sort_count: usize,
        constructors: Vec<ConstructorSchema>,
        terminal_sorts: Vec<Vec<SortId>>,
    ) -> Self {
        let constructor_count = constructors.len();
        let constructor_arities = constructors
            .iter()
            .map(|constructor| constructor.inputs.len())
            .collect::<Vec<_>>();
        let mut sort_terminals = vec![Vec::new(); sort_count];
        for (terminal, terminal_sort_ids) in terminal_sorts.iter().enumerate() {
            for &sort in terminal_sort_ids {
                sort_terminals[sort].push(TerminalId(terminal));
            }
        }
        Self {
            input,
            sort_count,
            constructors,
            terminal_sorts,
            sort_terminals,
            enodes: vec![Vec::new(); constructor_count],
            enode_seen: vec![HashSet::default(); constructor_count],
            enodes_by_output: vec![HashMap::default(); constructor_count],
            enodes_by_child: constructor_arities
                .iter()
                .map(|arity| vec![HashMap::default(); *arity])
                .collect(),
            domains: vec![HashMap::default(); sort_count],
            produces: vec![CompactValueRelation::default(); sort_count],
            aliases_by_child: DenseAdjacency::default(),
            space_applications: Vec::new(),
            space_application_children: Vec::new(),
            space_apps_by_constructor: vec![Vec::new(); constructor_count],
            space_uses: (0..sort_count).map(|_| DenseAdjacency::default()).collect(),
            space_apps_by_child: constructor_arities
                .iter()
                .map(|arity| vec![HashMap::default(); *arity])
                .collect(),
            token_any: vec![Vec::new(); terminal_count],
            exact_tokens: vec![HashMap::default(); sort_count],
            realizable_for_memos: vec![CompactValueRelation::default(); sort_count],
            realizable_for_contexts: vec![CompactValueRelation::default(); sort_count],
            realizable_memos: Vec::new(),
            realizable_contexts: Vec::new(),
            parents_by_context: DenseAdjacency::default(),
            alternatives_by_memo: DenseAdjacency::default(),
            project_holes_by_memo: DenseAdjacency::default(),
            project_fixed: Vec::new(),
            project_fixed_by_memo: DenseAdjacency::default(),
            project_fixed_by_space: DenseAdjacency::default(),
            continuations: Vec::new(),
            continuation_fixed_spaces: Vec::new(),
            continuations_by_memo: DenseAdjacency::default(),
            continuation_uses: (0..sort_count).map(|_| DenseAdjacency::default()).collect(),
            continuations_by_output: vec![HashMap::default(); constructor_count],
            continuations_by_child: constructor_arities
                .iter()
                .map(|arity| vec![HashMap::default(); *arity])
                .collect(),
            targets: vec![HashSet::default(); sort_count],
            delta: DeltaEngine::default(),
            last_join_probes: 0,
            total_join_probes: 0,
        }
    }

    pub(crate) fn begin_update(&mut self) {
        self.delta.begin_update();
        self.last_join_probes = 0;
    }

    pub(crate) fn finish_update(&mut self) -> usize {
        self.drain();
        self.delta.last_derived()
    }

    pub(crate) fn fact_count(&self) -> usize {
        self.produces
            .iter()
            .map(CompactValueRelation::pair_count)
            .sum::<usize>()
            + self
                .realizable_for_memos
                .iter()
                .map(CompactValueRelation::pair_count)
                .sum::<usize>()
            + self
                .realizable_for_contexts
                .iter()
                .map(CompactValueRelation::pair_count)
                .sum::<usize>()
            + self.realizable_memos.iter().filter(|value| **value).count()
            + self
                .realizable_contexts
                .iter()
                .filter(|value| **value)
                .count()
    }

    pub(crate) fn last_join_probes(&self) -> usize {
        self.last_join_probes
    }

    pub(crate) fn total_join_probes(&self) -> usize {
        self.total_join_probes
    }

    pub(crate) fn add_target(&mut self, sort: SortId, value: Value) {
        if self.targets[sort].insert(value) {
            self.insert_realizable_for_context(sort, 0, value);
        }
    }

    pub(crate) fn initial_viable(&self, sort: SortId, root: SpaceId) -> bool {
        self.targets[sort]
            .iter()
            .any(|value| self.produces(sort, root, *value))
    }

    pub(crate) fn frontier_viable(
        &self,
        lexeme_values: &[(SortId, Value)],
        memos: impl Iterator<Item = MemoId>,
    ) -> bool {
        memos.into_iter().any(|memo| {
            let memo = memo.as_u32();
            has_flag(&self.realizable_memos, memo)
                || lexeme_values.iter().any(|(sort, value)| {
                    self.realizable_for_memos[*sort].contains(memo as usize, *value)
                })
        })
    }

    pub(crate) fn add_enode(
        &mut self,
        constructor: ConstructorId,
        output: Value,
        children: Vec<Value>,
    ) {
        debug_assert_eq!(children.len(), self.constructors[constructor].inputs.len());
        let enode = Enode {
            output,
            children: children.into(),
        };
        if !self.enode_seen[constructor].insert(enode.clone()) {
            return;
        }
        let id = self.enodes[constructor].len();
        self.enodes[constructor].push(enode.clone());
        self.enodes_by_output[constructor]
            .entry(enode.output)
            .or_default()
            .push(id);
        for (argument, child) in enode.children.iter().copied().enumerate() {
            self.enodes_by_child[constructor][argument]
                .entry(child)
                .or_default()
                .push(id);
        }
        self.match_new_enode_against_spaces(constructor, id);
        self.match_new_enode_against_continuations(constructor, id);
    }

    pub(crate) fn add_domain(
        &mut self,
        sort: SortId,
        value: Value,
        lexical_form: String,
        integer: Option<i64>,
    ) {
        if self.domains[sort]
            .insert(
                value,
                DomainValue {
                    lexical_form: lexical_form.clone(),
                    integer,
                },
            )
            .is_some()
        {
            return;
        }
        if let Some(spaces) = self.exact_tokens[sort].get(&value).cloned() {
            for space in spaces {
                self.insert_produces(sort, space, value);
            }
        }
        for terminal in self.sort_terminals[sort].clone() {
            let matches = integer
                .is_some_and(|integer| self.input.i64_lexeme_matches(terminal, integer))
                || (integer.is_none() && self.input.lexeme_matches(terminal, &lexical_form));
            if matches {
                for space in self.token_any[terminal.index()].clone() {
                    self.insert_produces(sort, space, value);
                }
            }
        }
    }

    pub(crate) fn add_alias(&mut self, parent: SpaceId, child: SpaceId) {
        self.aliases_by_child.push(child.index(), parent);
        for sort in 0..self.sort_count {
            for value in self.produced_values(sort, child) {
                self.insert_produces(sort, parent, value);
            }
        }
    }

    pub(crate) fn add_space_constructor(
        &mut self,
        constructor: ConstructorId,
        output: SpaceId,
        children: SmallVec<[SpaceId; 4]>,
    ) {
        let id = self.space_applications.len();
        let children_start = u32::try_from(self.space_application_children.len())
            .expect("space-application child capacity exceeded");
        let children_len =
            u32::try_from(children.len()).expect("space-application child capacity exceeded");
        self.space_application_children
            .extend(children.iter().copied());
        self.space_applications.push(SpaceApplication {
            constructor: u32::try_from(constructor).expect("constructor capacity exceeded"),
            output,
            children_start,
            children_len,
        });
        self.space_apps_by_constructor[constructor].push(id);
        for (argument, child) in children.into_iter().enumerate() {
            let sort = self.constructors[constructor].inputs[argument];
            self.space_uses[sort].push(child.index(), (id, argument));
            for value in self.produced_values(sort, child) {
                self.space_apps_by_child[constructor][argument]
                    .entry(value)
                    .or_default()
                    .push(id);
            }
        }
        self.match_space_application_against_existing_enodes(id);
    }

    pub(crate) fn add_token_any(&mut self, output: SpaceId, terminal: TerminalId) {
        self.token_any[terminal.index()].push(output);
        for sort in self.terminal_sorts[terminal.index()].clone() {
            let domains = self.domains[sort]
                .iter()
                .map(|(value, domain)| (*value, domain.clone()))
                .collect::<Vec<_>>();
            for (value, domain) in domains {
                let matches = domain
                    .integer
                    .is_some_and(|integer| self.input.i64_lexeme_matches(terminal, integer))
                    || (domain.integer.is_none()
                        && self.input.lexeme_matches(terminal, &domain.lexical_form));
                if matches {
                    self.insert_produces(sort, output, value);
                }
            }
        }
    }

    pub(crate) fn add_token_exact(&mut self, sort: SortId, output: SpaceId, value: Value) {
        self.exact_tokens[sort]
            .entry(value)
            .or_default()
            .push(output);
        if self.domains[sort].contains_key(&value) {
            self.insert_produces(sort, output, value);
        }
    }

    pub(crate) fn add_parent(&mut self, memo: MemoId, context: ContextId) {
        let memo = memo.as_u32();
        let context = context.as_u32();
        self.parents_by_context.push(context as usize, memo);
        for sort in 0..self.sort_count {
            for value in self.realizable_for_context_values(sort, context) {
                self.insert_realizable_for_memo(sort, memo, value);
            }
        }
        if has_flag(&self.realizable_contexts, context) {
            self.insert_realizable_memo(memo);
        }
    }

    pub(crate) fn add_alternative(&mut self, context: ContextId, memo: MemoId) {
        let context = context.as_u32();
        let memo = memo.as_u32();
        self.alternatives_by_memo.push(memo as usize, context);
        for sort in 0..self.sort_count {
            for value in self.realizable_for_memo_values(sort, memo) {
                self.insert_realizable_for_context(sort, context, value);
            }
        }
        if has_flag(&self.realizable_memos, memo) {
            self.insert_realizable_context(context);
        }
    }

    pub(crate) fn add_project_hole(&mut self, context: ContextId, memo: MemoId) {
        let context = context.as_u32();
        let memo = memo.as_u32();
        self.project_holes_by_memo.push(memo as usize, context);
        for sort in 0..self.sort_count {
            for value in self.realizable_for_memo_values(sort, memo) {
                self.insert_realizable_for_context(sort, context, value);
            }
        }
        if has_flag(&self.realizable_memos, memo) {
            self.insert_realizable_context(context);
        }
    }

    pub(crate) fn add_project_fixed(&mut self, context: ContextId, memo: MemoId, child: SpaceId) {
        let id = self.project_fixed.len();
        let memo_raw = memo.as_u32();
        self.project_fixed.push(ProjectFixed {
            context: context.as_u32(),
            memo: memo_raw,
            child,
        });
        self.project_fixed_by_memo.push(memo_raw as usize, id);
        self.project_fixed_by_space.push(child.index(), id);
        self.recompute_project_fixed(id);
        if has_flag(&self.realizable_memos, memo_raw) {
            self.insert_realizable_context(context.as_u32());
        }
    }

    pub(crate) fn add_construct_hole(
        &mut self,
        constructor: ConstructorId,
        context: ContextId,
        memo: MemoId,
        hole: usize,
        fixed_children: SmallVec<[SpaceId; 4]>,
    ) {
        self.add_continuation(constructor, context, memo, Some(hole), fixed_children);
    }

    pub(crate) fn add_construct_ignored(
        &mut self,
        constructor: ConstructorId,
        context: ContextId,
        memo: MemoId,
        children: SmallVec<[SpaceId; 4]>,
    ) {
        self.add_continuation(constructor, context, memo, None, children);
    }

    fn add_continuation(
        &mut self,
        constructor: ConstructorId,
        context: ContextId,
        memo: MemoId,
        hole: Option<usize>,
        fixed_spaces: SmallVec<[SpaceId; 4]>,
    ) {
        let id = self.continuations.len();
        let fixed_start = u32::try_from(self.continuation_fixed_spaces.len())
            .expect("continuation fixed-space capacity exceeded");
        let fixed_len =
            u32::try_from(fixed_spaces.len()).expect("continuation fixed-space capacity exceeded");
        self.continuation_fixed_spaces.extend(fixed_spaces);
        let continuation = Continuation {
            constructor: u32::try_from(constructor).expect("constructor capacity exceeded"),
            context: context.as_u32(),
            memo: memo.as_u32(),
            hole: hole
                .map(|hole| u32::try_from(hole).expect("constructor arity exceeded"))
                .unwrap_or(NO_HOLE),
            fixed_start,
            fixed_len,
        };
        self.continuations.push(continuation);
        for offset in 0..continuation.fixed_len as usize {
            let argument = continuation.fixed_argument(offset);
            let space = self.continuation_fixed_spaces[continuation.fixed_start as usize + offset];
            let sort = self.constructors[constructor].inputs[argument];
            self.continuation_uses[sort].push(space.index(), (id, argument));
            for value in self.produced_values(sort, space) {
                self.continuations_by_child[constructor][argument]
                    .entry((value, continuation.hole()))
                    .or_default()
                    .push(id);
            }
        }
        let output_sort = self.constructors[constructor].output;
        for value in self.realizable_for_memo_values(output_sort, continuation.memo()) {
            self.continuations_by_output[constructor]
                .entry((value, continuation.hole()))
                .or_default()
                .push(id);
        }
        self.continuations_by_memo
            .push(continuation.memo as usize, id);
        self.match_continuation_against_existing_enodes(id);
        if has_flag(&self.realizable_memos, continuation.memo()) {
            self.insert_realizable_context(continuation.context());
        }
    }

    fn drain(&mut self) {
        DeltaEngine::close_program(
            self,
            |realizability| &mut realizability.delta,
            Self::apply_event,
        );
    }

    fn apply_event(&mut self, event: Event) {
        match event {
            Event::Produces { sort, space, value } => {
                for parent in self.aliases_by_child.values(space.index()) {
                    self.insert_produces(sort, parent, value);
                }
                for (application, argument) in self.space_uses[sort].values(space.index()) {
                    let constructor = self.space_applications[application].constructor();
                    self.space_apps_by_child[constructor][argument]
                        .entry(value)
                        .or_default()
                        .push(application);
                    let enodes = self.enodes_by_child[constructor][argument]
                        .get(&value)
                        .cloned()
                        .unwrap_or_default();
                    for enode in enodes {
                        self.try_space_match(application, enode);
                    }
                }
                for project in self.project_fixed_by_space.values(space.index()) {
                    let project = self.project_fixed[project].clone();
                    if self.realizable_for_memos[sort].contains(project.memo as usize, value) {
                        self.insert_realizable_context(project.context);
                    }
                }
                for (continuation, argument) in self.continuation_uses[sort].values(space.index()) {
                    let constructor = self.continuations[continuation].constructor();
                    self.continuations_by_child[constructor][argument]
                        .entry((value, self.continuations[continuation].hole()))
                        .or_default()
                        .push(continuation);
                    let enodes = self.enodes_by_child[constructor][argument]
                        .get(&value)
                        .cloned()
                        .unwrap_or_default();
                    for enode in enodes {
                        self.try_continuation_match(continuation, enode);
                    }
                }
            }
            Event::RealizableForMemo { sort, memo, value } => {
                for context in self.alternatives_by_memo.values(memo as usize) {
                    self.insert_realizable_for_context(sort, context, value);
                }
                for context in self.project_holes_by_memo.values(memo as usize) {
                    self.insert_realizable_for_context(sort, context, value);
                }
                for project in self.project_fixed_by_memo.values(memo as usize) {
                    let project = self.project_fixed[project].clone();
                    if self.produces(sort, project.child, value) {
                        self.insert_realizable_context(project.context);
                    }
                }
                for continuation in self.continuations_by_memo.values(memo as usize) {
                    let constructor = self.continuations[continuation].constructor();
                    if self.constructors[constructor].output != sort {
                        continue;
                    }
                    self.continuations_by_output[constructor]
                        .entry((value, self.continuations[continuation].hole()))
                        .or_default()
                        .push(continuation);
                    let enodes = self.enodes_by_output[constructor]
                        .get(&value)
                        .cloned()
                        .unwrap_or_default();
                    for enode in enodes {
                        self.try_continuation_match(continuation, enode);
                    }
                }
            }
            Event::RealizableForContext {
                sort,
                context,
                value,
            } => {
                for memo in self.parents_by_context.values(context as usize) {
                    self.insert_realizable_for_memo(sort, memo, value);
                }
            }
            Event::RealizableMemo(memo) => {
                for context in self.alternatives_by_memo.values(memo as usize) {
                    self.insert_realizable_context(context);
                }
                for context in self.project_holes_by_memo.values(memo as usize) {
                    self.insert_realizable_context(context);
                }
                for project in self.project_fixed_by_memo.values(memo as usize) {
                    self.insert_realizable_context(self.project_fixed[project].context);
                }
                for continuation in self.continuations_by_memo.values(memo as usize) {
                    self.insert_realizable_context(self.continuations[continuation].context());
                }
            }
            Event::RealizableContext(context) => {
                for memo in self.parents_by_context.values(context as usize) {
                    self.insert_realizable_memo(memo);
                }
            }
        }
    }

    fn match_new_enode_against_spaces(&mut self, constructor: ConstructorId, enode: usize) {
        let row = self.enodes[constructor][enode].clone();
        let candidates = if row.children.is_empty() {
            self.space_apps_by_constructor[constructor].clone()
        } else {
            let mut best = None::<(usize, usize)>;
            for (argument, child) in row.children.iter().copied().enumerate() {
                let Some(candidates) = self.space_apps_by_child[constructor][argument].get(&child)
                else {
                    return;
                };
                if best
                    .as_ref()
                    .is_none_or(|(_, current_len)| candidates.len() < *current_len)
                {
                    best = Some((argument, candidates.len()));
                }
            }
            let (argument, _) = best.expect("nonempty constructor has a child posting");
            self.space_apps_by_child[constructor][argument][&row.children[argument]].clone()
        };
        for application in candidates {
            self.try_space_match(application, enode);
        }
    }

    fn match_space_application_against_existing_enodes(&mut self, application: usize) {
        let row = self.space_applications[application];
        let constructor = row.constructor();
        let candidates = if row.children_len == 0 {
            (0..self.enodes[constructor].len()).collect()
        } else {
            let mut best = None::<(usize, usize)>;
            for argument in 0..row.children_len as usize {
                let sort = self.constructors[constructor].inputs[argument];
                let space = self.space_application_children[row.children_start as usize + argument];
                let values = self.produced_values(sort, space);
                if values.is_empty() {
                    return;
                }
                let candidate_len = values
                    .iter()
                    .filter_map(|value| {
                        self.enodes_by_child[constructor][argument]
                            .get(value)
                            .map(Vec::len)
                    })
                    .fold(0usize, usize::saturating_add);
                if candidate_len == 0 {
                    return;
                }
                if best
                    .as_ref()
                    .is_none_or(|(_, current_len)| candidate_len < *current_len)
                {
                    best = Some((argument, candidate_len));
                }
            }
            let (argument, candidate_len) = best.expect("application has a child posting");
            let sort = self.constructors[constructor].inputs[argument];
            let space = self.space_application_children[row.children_start as usize + argument];
            let mut candidates = Vec::with_capacity(candidate_len);
            for value in self.produced_values(sort, space) {
                if let Some(enodes) = self.enodes_by_child[constructor][argument].get(&value) {
                    candidates.extend(enodes.iter().copied());
                }
            }
            candidates
        };
        for enode in candidates {
            self.try_space_match(application, enode);
        }
    }

    fn try_space_match(&mut self, application: usize, enode: usize) {
        self.note_join_probe();
        let application = self.space_applications[application];
        let constructor = application.constructor();
        let (matches, output_sort, output_value) = {
            let row = &self.enodes[constructor][enode];
            let schema = &self.constructors[constructor];
            let matches = (0..application.children_len as usize).all(|argument| {
                let space =
                    self.space_application_children[application.children_start as usize + argument];
                self.produces(schema.inputs[argument], space, row.children[argument])
            });
            (matches, schema.output, row.output)
        };
        if matches {
            self.insert_produces(output_sort, application.output, output_value);
        }
    }

    fn recompute_project_fixed(&mut self, id: usize) {
        let project = self.project_fixed[id].clone();
        let realizable = (0..self.sort_count).any(|sort| {
            self.realizable_for_memos[sort]
                .values(project.memo as usize)
                .iter()
                .any(|value| self.produces(sort, project.child, *value))
        });
        if realizable {
            self.insert_realizable_context(project.context);
        }
    }

    fn match_new_enode_against_continuations(&mut self, constructor: ConstructorId, enode: usize) {
        let row = self.enodes[constructor][enode].clone();
        let arity = row.children.len();
        for hole in std::iter::once(None).chain((0..arity).map(Some)) {
            let Some(output_candidates) =
                self.continuations_by_output[constructor].get(&(row.output, hole))
            else {
                continue;
            };
            let mut best = (None, output_candidates.len());
            for (argument, child) in row.children.iter().copied().enumerate() {
                if hole == Some(argument) {
                    continue;
                }
                let Some(candidates) =
                    self.continuations_by_child[constructor][argument].get(&(child, hole))
                else {
                    best.1 = 0;
                    break;
                };
                if candidates.len() < best.1 {
                    best = (Some(argument), candidates.len());
                }
            }
            if best.1 == 0 {
                continue;
            }
            let candidates = match best.0 {
                Some(argument) => self.continuations_by_child[constructor][argument]
                    [&(row.children[argument], hole)]
                    .clone(),
                None => output_candidates.clone(),
            };
            for continuation in candidates {
                self.try_continuation_match(continuation, enode);
            }
        }
    }

    fn match_continuation_against_existing_enodes(&mut self, continuation: usize) {
        let continuation_fact = self.continuations[continuation];
        let constructor = continuation_fact.constructor();
        let schema = &self.constructors[constructor];
        let output_values =
            self.realizable_for_memo_values(schema.output, continuation_fact.memo());
        if output_values.is_empty() {
            return;
        }
        let output_len = output_values
            .iter()
            .filter_map(|value| self.enodes_by_output[constructor].get(value).map(Vec::len))
            .fold(0usize, usize::saturating_add);
        if output_len == 0 {
            return;
        }
        // `None` selects the output posting; `Some(offset)` selects one fixed
        // child posting. Only the winning posting is materialized.
        let mut best = (None, output_len);
        for offset in 0..continuation_fact.fixed_len as usize {
            let argument = continuation_fact.fixed_argument(offset);
            let space =
                self.continuation_fixed_spaces[continuation_fact.fixed_start as usize + offset];
            let sort = self.constructors[constructor].inputs[argument];
            let values = self.produced_values(sort, space);
            if values.is_empty() {
                return;
            }
            let candidate_len = values
                .iter()
                .filter_map(|value| {
                    self.enodes_by_child[constructor][argument]
                        .get(value)
                        .map(Vec::len)
                })
                .fold(0usize, usize::saturating_add);
            if candidate_len == 0 {
                return;
            }
            if candidate_len < best.1 {
                best = (Some(offset), candidate_len);
            }
        }
        let mut candidates = Vec::with_capacity(best.1);
        match best.0 {
            None => {
                for value in output_values {
                    if let Some(enodes) = self.enodes_by_output[constructor].get(&value) {
                        candidates.extend(enodes.iter().copied());
                    }
                }
            }
            Some(offset) => {
                let argument = continuation_fact.fixed_argument(offset);
                let space =
                    self.continuation_fixed_spaces[continuation_fact.fixed_start as usize + offset];
                let sort = self.constructors[constructor].inputs[argument];
                for value in self.produced_values(sort, space) {
                    if let Some(enodes) = self.enodes_by_child[constructor][argument].get(&value) {
                        candidates.extend(enodes.iter().copied());
                    }
                }
            }
        }
        for enode in candidates {
            self.try_continuation_match(continuation, enode);
        }
    }

    fn try_continuation_match(&mut self, continuation: usize, enode: usize) {
        self.note_join_probe();
        let continuation = self.continuations[continuation];
        let constructor = continuation.constructor();
        let conclusion = {
            let row = &self.enodes[constructor][enode];
            let schema = &self.constructors[constructor];
            if !self.realizable_for_memos[schema.output]
                .contains(continuation.memo as usize, row.output)
            {
                return;
            }
            for offset in 0..continuation.fixed_len as usize {
                let argument = continuation.fixed_argument(offset);
                let space =
                    self.continuation_fixed_spaces[continuation.fixed_start as usize + offset];
                if !self.produces(schema.inputs[argument], space, row.children[argument]) {
                    return;
                }
            }
            continuation
                .hole()
                .map(|hole| (schema.inputs[hole], row.children[hole]))
        };
        match conclusion {
            Some((sort, value)) => {
                self.insert_realizable_for_context(sort, continuation.context(), value)
            }
            None => self.insert_realizable_context(continuation.context()),
        }
    }

    fn insert_produces(&mut self, sort: SortId, space: SpaceId, value: Value) {
        if self.produces[sort].insert(space.index(), value) {
            self.delta
                .enqueue_new(Event::Produces { sort, space, value });
        }
    }

    fn insert_realizable_for_memo(&mut self, sort: SortId, memo: u32, value: Value) {
        if self.realizable_for_memos[sort].insert(memo as usize, value) {
            self.delta
                .enqueue_new(Event::RealizableForMemo { sort, memo, value });
        }
    }

    fn insert_realizable_for_context(&mut self, sort: SortId, context: u32, value: Value) {
        if self.realizable_for_contexts[sort].insert(context as usize, value) {
            self.delta.enqueue_new(Event::RealizableForContext {
                sort,
                context,
                value,
            });
        }
    }

    fn insert_realizable_context(&mut self, context: u32) {
        if insert_flag(&mut self.realizable_contexts, context as usize) {
            self.delta.enqueue_new(Event::RealizableContext(context));
        }
    }

    fn insert_realizable_memo(&mut self, memo: u32) {
        if insert_flag(&mut self.realizable_memos, memo as usize) {
            self.delta.enqueue_new(Event::RealizableMemo(memo));
        }
    }

    fn note_join_probe(&mut self) {
        self.last_join_probes = self.last_join_probes.saturating_add(1);
        self.total_join_probes = self.total_join_probes.saturating_add(1);
    }

    fn produces(&self, sort: SortId, space: SpaceId, value: Value) -> bool {
        self.produces[sort].contains(space.index(), value)
    }

    fn produced_values(&self, sort: SortId, space: SpaceId) -> ValueSet {
        self.produces[sort].values(space.index())
    }

    fn realizable_for_memo_values(&self, sort: SortId, memo: u32) -> ValueSet {
        self.realizable_for_memos[sort].values(memo as usize)
    }

    fn realizable_for_context_values(&self, sort: SortId, context: u32) -> ValueSet {
        self.realizable_for_contexts[sort].values(context as usize)
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use egglog::Value;

    use super::{CompactValueRelation, ValueCell, WIDE_ROW_THRESHOLD};

    #[test]
    fn compact_relation_keeps_small_rows_small_and_spills_without_a_limit() {
        assert_eq!(size_of::<ValueCell>(), 8);
        let mut relation = CompactValueRelation::default();
        for raw in 0..10 {
            assert!(relation.insert(7, Value::new_const(raw)));
            assert!(!relation.insert(7, Value::new_const(raw)));
        }
        assert_eq!(relation.pair_count(), 10);
        for raw in 0..10 {
            assert!(relation.contains(7, Value::new_const(raw)));
        }
        assert!(!relation.contains(6, Value::new_const(0)));
        assert!(!relation.contains(7, Value::new_const(11)));
        assert!(relation.wide_rows.contains_key(&7));
    }

    #[test]
    fn compact_relation_promotes_only_wide_rows_to_hash_membership() {
        let mut relation = CompactValueRelation::default();
        for raw in 0..WIDE_ROW_THRESHOLD as u32 {
            assert!(relation.insert(1, Value::new_const(raw)));
        }
        assert!(!relation.wide_rows.contains_key(&1));
        assert!(relation.insert(1, Value::new_const(WIDE_ROW_THRESHOLD as u32)));
        assert!(relation.wide_rows.contains_key(&1));

        assert!(relation.insert(2, Value::new_const(99)));
        assert!(!relation.wide_rows.contains_key(&2));
    }
}
