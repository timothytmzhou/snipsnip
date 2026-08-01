//! Incremental materialization of the finite, already-parsed part of PwZ
//! semantic spaces.
//!
//! The initial PwZ spaces denote whole nonterminal and terminal languages and
//! can be recursive or infinite. They are deliberately ignored here. Every
//! later exact-token/application/ambiguity space denotes concrete parsed
//! trees. This module incrementally turns those fixed trees into private
//! egglog bindings.
//!
//! Bindings form a DAG: a constructor request contains only the binding IDs of
//! its immediate children. Consequently the request size is proportional to
//! one constructor's arity, never to the depth of the AST being materialized.

use std::{collections::VecDeque, hash::Hash, sync::Arc};

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;

use crate::{
    forest::{SpaceFact, SpaceId},
    realizability::{ConstructorId, ConstructorSchema, SortId},
};

/// Numeric identity of a PwZ space as seen by this materializer.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct FixedSpaceId(u32);

impl FixedSpaceId {
    pub(crate) fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("fixed-space capacity exceeded"))
    }

    #[inline]
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub(crate) fn from_pwz(space: SpaceId) -> Self {
        Self::from_index(space.index())
    }
}

/// One private global egglog binding. IDs are stable, dense, and allocated in
/// dependency order, so every child named by a constructor has a lower ID.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct BindingId(u32);

impl BindingId {
    #[inline]
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }

    /// Returns the egglog global name for this binding.
    pub(crate) fn egglog_name(self, private_prefix: &str) -> String {
        format!(
            "${}_fixed_tree_{}",
            private_prefix.trim_start_matches('$'),
            self.0
        )
    }
}

/// A primitive exact-token term. Keeping this typed source, rather than only
/// its eventual egglog `Value`, lets the caller construct a normal `(let ...)`
/// command which later constructor bindings can reference.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExactSource {
    String(Arc<str>),
    I64(i64),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TypedExact {
    pub(crate) sort: SortId,
    pub(crate) source: ExactSource,
}

impl TypedExact {
    #[cfg(test)]
    pub(crate) fn string(sort: SortId, value: impl AsRef<str>) -> Self {
        Self {
            sort,
            source: ExactSource::String(Arc::from(value.as_ref())),
        }
    }

    #[cfg(test)]
    pub(crate) fn i64(sort: SortId, value: i64) -> Self {
        Self {
            sort,
            source: ExactSource::I64(value),
        }
    }
}

/// The constant-depth right-hand side of a pending private binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BindingRhs {
    Exact(ExactSource),
    Constructor {
        constructor: ConstructorId,
        children: SmallVec<[BindingId; 4]>,
    },
}

/// Work for the owning `live.rs`: insert this private binding, evaluate its
/// variable, and return the resulting value from the drain callback.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PendingBinding {
    pub(crate) binding: BindingId,
    pub(crate) sort: SortId,
    pub(crate) rhs: BindingRhs,
}

impl PendingBinding {
    pub(crate) fn egglog_name(&self, private_prefix: &str) -> String {
        self.binding.egglog_name(private_prefix)
    }
}

/// A newly established typed concrete candidate for a fixed space.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MaterializedCandidate<Value> {
    pub(crate) space: FixedSpaceId,
    pub(crate) sort: SortId,
    pub(crate) binding: BindingId,
    pub(crate) value: Value,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TermKey {
    Exact {
        sort: SortId,
        source: ExactSource,
    },
    Constructor {
        constructor: ConstructorId,
        children: SmallVec<[BindingId; 4]>,
    },
}

#[derive(Clone, Debug)]
struct Candidate<Value> {
    sort: SortId,
    term: TermKey,
    value: Option<Value>,
    destinations: SmallVec<[FixedSpaceId; 2]>,
}

#[derive(Clone, Debug, Default)]
struct SpaceCandidates {
    /// One representative binding per distinct returned value and sort.
    by_sort: HashMap<SortId, Vec<BindingId>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ApplicationKey {
    constructor: ConstructorId,
    output: FixedSpaceId,
    children: SmallVec<[FixedSpaceId; 4]>,
}

#[derive(Clone, Debug)]
struct Application {
    constructor: ConstructorId,
    output: FixedSpaceId,
    children: SmallVec<[FixedSpaceId; 4]>,
}

#[derive(Clone, Copy, Debug)]
struct ApplicationUse {
    application: u32,
    argument: u32,
}

#[derive(Clone, Copy, Debug)]
struct SpaceValue<Value> {
    space: FixedSpaceId,
    sort: SortId,
    binding: BindingId,
    value: Value,
}

/// Incrementally materializes only dynamic, concrete PwZ spaces.
///
/// `Value` is normally `egglog::Value`; tests and other clients may use any
/// cheap hashable value. Values returned by the evaluator are used to suppress
/// equivalent candidates before computing constructor cross-products.
pub(crate) struct FixedTreeMaterializer<Value>
where
    Value: Copy + Eq + Hash,
{
    static_space_count: usize,
    sort_count: usize,
    constructors: Vec<ConstructorSchema>,

    spaces: Vec<SpaceCandidates>,
    seen_space_values: HashSet<(FixedSpaceId, SortId, Value)>,
    aliases_by_child: Vec<Vec<FixedSpaceId>>,
    seen_aliases: HashSet<(FixedSpaceId, FixedSpaceId)>,

    applications: Vec<Application>,
    uses_by_space: Vec<Vec<ApplicationUse>>,
    seen_applications: HashSet<ApplicationKey>,

    candidates: Vec<Candidate<Value>>,
    terms: HashMap<TermKey, BindingId>,
    attachments: HashSet<(BindingId, FixedSpaceId)>,
    pending: VecDeque<BindingId>,
    space_agenda: Vec<SpaceValue<Value>>,
    materialized: Vec<MaterializedCandidate<Value>>,
}

impl<Value> FixedTreeMaterializer<Value>
where
    Value: Copy + Eq + Hash,
{
    pub(crate) fn new(
        static_space_count: usize,
        sort_count: usize,
        constructors: Vec<ConstructorSchema>,
    ) -> Self {
        let mut materializer = Self {
            static_space_count,
            sort_count,
            constructors,
            spaces: Vec::new(),
            seen_space_values: HashSet::default(),
            aliases_by_child: Vec::new(),
            seen_aliases: HashSet::default(),
            applications: Vec::new(),
            uses_by_space: Vec::new(),
            seen_applications: HashSet::default(),
            candidates: Vec::new(),
            terms: HashMap::default(),
            attachments: HashSet::default(),
            pending: VecDeque::new(),
            space_agenda: Vec::new(),
            materialized: Vec::new(),
        };
        if static_space_count != 0 {
            materializer.ensure_space(FixedSpaceId::from_index(static_space_count - 1));
        }
        materializer
    }

    /// Consumes one native PwZ space delta. `exact_values` is consulted only
    /// for `TokenExact` and must describe the lexeme whose parser step emitted
    /// that fact.
    pub(crate) fn add_space_fact(&mut self, fact: SpaceFact, exact_values: &[TypedExact]) {
        match fact {
            SpaceFact::Alias { output, child } => {
                self.add_alias(
                    FixedSpaceId::from_pwz(output),
                    FixedSpaceId::from_pwz(child),
                );
            }
            SpaceFact::Constructor {
                constructor,
                output,
                children,
            } => {
                self.add_constructor(
                    constructor as ConstructorId,
                    FixedSpaceId::from_pwz(output),
                    children.into_iter().map(FixedSpaceId::from_pwz).collect(),
                );
            }
            SpaceFact::TokenExact {
                output,
                terminal: _,
            } => {
                let output = FixedSpaceId::from_pwz(output);
                for exact in exact_values {
                    self.add_exact(output, exact.clone());
                }
            }
            // A TokenAny space denotes an open lexical language, never one
            // concrete already-consumed token.
            SpaceFact::TokenAny { .. } => {}
        }
    }

    /// Adds a concrete primitive leaf to a dynamic space. Returns false for a
    /// static/full space or an already-interned attachment.
    pub(crate) fn add_exact(&mut self, output: FixedSpaceId, exact: TypedExact) -> bool {
        if !self.is_dynamic(output) {
            return false;
        }
        assert!(exact.sort < self.sort_count, "unknown exact-value sort");
        self.ensure_space(output);
        let key = TermKey::Exact {
            sort: exact.sort,
            source: exact.source,
        };
        let binding = self.intern_term(key, exact.sort);
        let attached = self.attach(binding, output);
        self.close_space_agenda();
        attached
    }

    /// Adds a dynamic ambiguity/projection edge and catches it up with every
    /// candidate already known for the child.
    pub(crate) fn add_alias(&mut self, output: FixedSpaceId, child: FixedSpaceId) -> bool {
        if !self.is_dynamic(output) || !self.is_dynamic(child) {
            return false;
        }
        self.ensure_space(output);
        self.ensure_space(child);
        if !self.seen_aliases.insert((output, child)) {
            return false;
        }
        self.aliases_by_child[child.index()].push(output);

        let mut existing = Vec::new();
        for (&sort, bindings) in &self.spaces[child.index()].by_sort {
            for &binding in bindings {
                let value = self.candidates[binding.index()]
                    .value
                    .expect("space postings contain only evaluated candidates");
                existing.push((sort, binding, value));
            }
        }
        for (sort, binding, value) in existing {
            self.insert_space_value(output, sort, binding, value);
        }
        self.close_space_agenda();
        true
    }

    /// Adds a fixed constructor application. If children already have typed
    /// values, their full candidate cross-product is scheduled immediately;
    /// later child values extend it incrementally.
    pub(crate) fn add_constructor(
        &mut self,
        constructor: ConstructorId,
        output: FixedSpaceId,
        children: SmallVec<[FixedSpaceId; 4]>,
    ) -> bool {
        if !self.is_dynamic(output) || children.iter().any(|child| !self.is_dynamic(*child)) {
            return false;
        }
        let schema = self
            .constructors
            .get(constructor)
            .unwrap_or_else(|| panic!("unknown constructor {constructor}"));
        assert_eq!(
            schema.inputs.len(),
            children.len(),
            "fixed constructor arity mismatch"
        );
        self.ensure_space(output);
        for &child in &children {
            self.ensure_space(child);
        }

        let key = ApplicationKey {
            constructor,
            output,
            children: children.clone(),
        };
        if !self.seen_applications.insert(key) {
            return false;
        }
        let application = u32::try_from(self.applications.len())
            .expect("fixed constructor application capacity exceeded");
        self.applications.push(Application {
            constructor,
            output,
            children: children.clone(),
        });
        for (argument, child) in children.into_iter().enumerate() {
            self.uses_by_space[child.index()].push(ApplicationUse {
                application,
                argument: u32::try_from(argument).expect("constructor arity exceeded"),
            });
        }
        self.enumerate_application(application as usize, None);
        self.close_space_agenda();
        true
    }

    /// Repeatedly hands constant-depth binding requests to `evaluate` and
    /// records each returned value. Requests created by those values are
    /// drained in the same call.
    #[cfg(test)]
    pub(crate) fn drain_pending<Error>(
        &mut self,
        mut evaluate: impl FnMut(&PendingBinding) -> Result<Value, Error>,
    ) -> Result<usize, Error> {
        let mut count = 0usize;
        while let Some(binding) = self.pending.pop_front() {
            let request = self.pending_binding(binding);
            let value = match evaluate(&request) {
                Ok(value) => value,
                Err(error) => {
                    self.pending.push_front(binding);
                    return Err(error);
                }
            };
            self.resolve(binding, value);
            count = count.saturating_add(1);
        }
        Ok(count)
    }

    /// Like [`Self::drain_pending`], but evaluates every request that is ready
    /// at the start of a wave in one callback. Resolving that wave may unlock
    /// another wave of parent constructors.
    pub(crate) fn drain_pending_batches<Error>(
        &mut self,
        mut evaluate: impl FnMut(&[PendingBinding]) -> Result<Vec<Value>, Error>,
    ) -> Result<usize, Error> {
        let mut count = 0usize;
        while !self.pending.is_empty() {
            let wave_len = self.pending.len();
            let requests = (0..wave_len)
                .map(|_| {
                    let binding = self
                        .pending
                        .pop_front()
                        .expect("the wave length came from this queue");
                    self.pending_binding(binding)
                })
                .collect::<Vec<_>>();
            let values = match evaluate(&requests) {
                Ok(values) => values,
                Err(error) => {
                    for request in requests.into_iter().rev() {
                        self.pending.push_front(request.binding);
                    }
                    return Err(error);
                }
            };
            assert_eq!(
                values.len(),
                requests.len(),
                "batch evaluator returned the wrong number of values"
            );
            for (request, value) in requests.into_iter().zip(values) {
                self.resolve(request.binding, value);
                count = count.saturating_add(1);
            }
        }
        Ok(count)
    }

    #[cfg(test)]
    pub(crate) fn pending_count(&self) -> usize {
        self.pending.len()
    }

    pub(crate) fn binding_count(&self) -> usize {
        self.candidates.len()
    }

    /// Appends and clears candidate deltas accumulated since the previous
    /// drain. Alias propagation emits the same binding for the new space and
    /// never asks egglog to rebuild that term.
    pub(crate) fn drain_materialized(&mut self, output: &mut Vec<MaterializedCandidate<Value>>) {
        output.append(&mut self.materialized);
    }

    pub(crate) fn candidates(
        &self,
        space: FixedSpaceId,
        sort: SortId,
    ) -> impl Iterator<Item = (BindingId, Value)> + '_ {
        self.spaces
            .get(space.index())
            .and_then(|space| space.by_sort.get(&sort))
            .into_iter()
            .flatten()
            .map(|&binding| {
                (
                    binding,
                    self.candidates[binding.index()]
                        .value
                        .expect("space postings contain only evaluated candidates"),
                )
            })
    }

    /// Returns every evaluated binding attached to `space`, independent of
    /// its sort. This is used for a projection whose semantic action ignores
    /// the value currently in the zipper hole and selects a fixed child.
    pub(crate) fn all_candidate_bindings(
        &self,
        space: FixedSpaceId,
    ) -> impl Iterator<Item = (SortId, BindingId)> + '_ {
        self.spaces
            .get(space.index())
            .into_iter()
            .flat_map(|space| space.by_sort.iter())
            .flat_map(|(&sort, bindings)| {
                bindings.iter().copied().map(move |binding| (sort, binding))
            })
    }

    /// Interns one constructor node without attaching it to a PwZ space.
    ///
    /// Prefix-output reconstruction uses this for the shallow node created
    /// while a concrete value is passed through one zipper context. Children
    /// are existing bindings, so the pending egglog request remains constant
    /// depth regardless of the total AST depth.
    pub(crate) fn intern_detached_constructor(
        &mut self,
        constructor: ConstructorId,
        children: SmallVec<[BindingId; 4]>,
    ) -> BindingId {
        let schema = self
            .constructors
            .get(constructor)
            .unwrap_or_else(|| panic!("unknown constructor {constructor}"));
        assert_eq!(
            schema.inputs.len(),
            children.len(),
            "detached constructor arity mismatch"
        );
        for (argument, &child) in children.iter().enumerate() {
            let candidate = self
                .candidates
                .get(child.index())
                .unwrap_or_else(|| panic!("unknown fixed binding {}", child.index()));
            assert_eq!(
                candidate.sort, schema.inputs[argument],
                "detached constructor child sort mismatch"
            );
        }
        let output = schema.output;
        self.intern_term(
            TermKey::Constructor {
                constructor,
                children,
            },
            output,
        )
    }

    #[inline]
    pub(crate) fn binding_sort(&self, binding: BindingId) -> SortId {
        self.candidates
            .get(binding.index())
            .unwrap_or_else(|| panic!("unknown fixed binding {}", binding.index()))
            .sort
    }

    #[inline]
    pub(crate) fn binding_value(&self, binding: BindingId) -> Option<Value> {
        self.candidates
            .get(binding.index())
            .unwrap_or_else(|| panic!("unknown fixed binding {}", binding.index()))
            .value
    }

    #[inline]
    pub(crate) fn constructor_schema(&self, constructor: ConstructorId) -> &ConstructorSchema {
        self.constructors
            .get(constructor)
            .unwrap_or_else(|| panic!("unknown constructor {constructor}"))
    }

    fn is_dynamic(&self, space: FixedSpaceId) -> bool {
        space.index() >= self.static_space_count
    }

    fn ensure_space(&mut self, space: FixedSpaceId) {
        let len = space.index() + 1;
        if self.spaces.len() < len {
            self.spaces.resize_with(len, SpaceCandidates::default);
        }
        if self.aliases_by_child.len() < len {
            self.aliases_by_child.resize_with(len, Vec::new);
        }
        if self.uses_by_space.len() < len {
            self.uses_by_space.resize_with(len, Vec::new);
        }
    }

    fn intern_term(&mut self, term: TermKey, sort: SortId) -> BindingId {
        if let Some(&binding) = self.terms.get(&term) {
            debug_assert_eq!(self.candidates[binding.index()].sort, sort);
            return binding;
        }
        let raw = u32::try_from(self.candidates.len()).expect("fixed binding capacity exceeded");
        let binding = BindingId(raw);
        self.terms.insert(term.clone(), binding);
        self.candidates.push(Candidate {
            sort,
            term,
            value: None,
            destinations: SmallVec::new(),
        });
        self.pending.push_back(binding);
        binding
    }

    fn attach(&mut self, binding: BindingId, output: FixedSpaceId) -> bool {
        if !self.attachments.insert((binding, output)) {
            return false;
        }
        self.candidates[binding.index()].destinations.push(output);
        if let Some(value) = self.candidates[binding.index()].value {
            let sort = self.candidates[binding.index()].sort;
            self.insert_space_value(output, sort, binding, value);
        }
        true
    }

    fn pending_binding(&self, binding: BindingId) -> PendingBinding {
        let candidate = &self.candidates[binding.index()];
        debug_assert!(candidate.value.is_none());
        let rhs = match &candidate.term {
            TermKey::Exact { source, .. } => BindingRhs::Exact(source.clone()),
            TermKey::Constructor {
                constructor,
                children,
            } => BindingRhs::Constructor {
                constructor: *constructor,
                children: children.clone(),
            },
        };
        PendingBinding {
            binding,
            sort: candidate.sort,
            rhs,
        }
    }

    fn resolve(&mut self, binding: BindingId, value: Value) {
        let candidate = &mut self.candidates[binding.index()];
        assert!(
            candidate.value.replace(value).is_none(),
            "binding resolved twice"
        );
        let sort = candidate.sort;
        let destinations = candidate.destinations.clone();
        for output in destinations {
            self.insert_space_value(output, sort, binding, value);
        }
        self.close_space_agenda();
    }

    fn insert_space_value(
        &mut self,
        space: FixedSpaceId,
        sort: SortId,
        binding: BindingId,
        value: Value,
    ) {
        if !self.seen_space_values.insert((space, sort, value)) {
            return;
        }
        self.spaces[space.index()]
            .by_sort
            .entry(sort)
            .or_default()
            .push(binding);
        self.space_agenda.push(SpaceValue {
            space,
            sort,
            binding,
            value,
        });
    }

    fn close_space_agenda(&mut self) {
        while let Some(row) = self.space_agenda.pop() {
            self.materialized.push(MaterializedCandidate {
                space: row.space,
                sort: row.sort,
                binding: row.binding,
                value: row.value,
            });

            let alias_count = self.aliases_by_child[row.space.index()].len();
            for offset in 0..alias_count {
                let output = self.aliases_by_child[row.space.index()][offset];
                self.insert_space_value(output, row.sort, row.binding, row.value);
            }

            let use_count = self.uses_by_space[row.space.index()].len();
            for offset in 0..use_count {
                let usage = self.uses_by_space[row.space.index()][offset];
                let application = &self.applications[usage.application as usize];
                let expected_sort =
                    self.constructors[application.constructor].inputs[usage.argument as usize];
                if expected_sort == row.sort {
                    self.enumerate_application(
                        usage.application as usize,
                        Some((usage.argument as usize, row.binding)),
                    );
                }
            }
        }
    }

    /// Enumerates either a whole existing product (`fixed = None`) or exactly
    /// the new slice contributed by one child candidate. Term interning makes
    /// repeated-space/repeated-argument overlap harmless.
    fn enumerate_application(&mut self, application_id: usize, fixed: Option<(usize, BindingId)>) {
        let application = self.applications[application_id].clone();
        let arity = application.children.len();
        if arity == 0 {
            self.attach_constructor(&application, SmallVec::new());
            return;
        }

        let mut lengths = SmallVec::<[usize; 4]>::with_capacity(arity);
        for argument in 0..arity {
            if fixed.is_some_and(|(fixed_argument, _)| fixed_argument == argument) {
                lengths.push(1);
                continue;
            }
            let child = application.children[argument];
            let sort = self.constructors[application.constructor].inputs[argument];
            let length = self.spaces[child.index()]
                .by_sort
                .get(&sort)
                .map_or(0, Vec::len);
            if length == 0 {
                return;
            }
            lengths.push(length);
        }

        let mut positions = SmallVec::<[usize; 4]>::from_elem(0, arity);
        loop {
            let mut children = SmallVec::<[BindingId; 4]>::with_capacity(arity);
            for argument in 0..arity {
                if let Some((fixed_argument, binding)) = fixed
                    && fixed_argument == argument
                {
                    children.push(binding);
                    continue;
                }
                let child = application.children[argument];
                let sort = self.constructors[application.constructor].inputs[argument];
                children.push(self.spaces[child.index()].by_sort[&sort][positions[argument]]);
            }
            self.attach_constructor(&application, children);

            let mut cursor = arity;
            let advanced = loop {
                if cursor == 0 {
                    break false;
                }
                cursor -= 1;
                if fixed.is_some_and(|(fixed_argument, _)| fixed_argument == cursor) {
                    continue;
                }
                positions[cursor] += 1;
                if positions[cursor] < lengths[cursor] {
                    break true;
                }
                positions[cursor] = 0;
            };
            if !advanced {
                break;
            }
        }
    }

    fn attach_constructor(
        &mut self,
        application: &Application,
        children: SmallVec<[BindingId; 4]>,
    ) {
        debug_assert!(
            children
                .iter()
                .all(|child| child.index() < self.candidates.len())
        );
        let sort = self.constructors[application.constructor].output;
        let term = TermKey::Constructor {
            constructor: application.constructor,
            children,
        };
        let binding = self.intern_term(term, sort);
        self.attach(binding, application.output);
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use smallvec::smallvec;

    use super::{
        BindingRhs, ExactSource, FixedSpaceId, FixedTreeMaterializer, MaterializedCandidate,
        PendingBinding, TypedExact,
    };
    use crate::realizability::ConstructorSchema;

    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    struct FakeValue(u32);

    fn schema(inputs: &[usize], output: usize) -> ConstructorSchema {
        ConstructorSchema {
            inputs: inputs.to_vec(),
            output,
        }
    }

    fn dynamic(index: usize) -> FixedSpaceId {
        FixedSpaceId::from_index(index)
    }

    fn evaluate_all(
        materializer: &mut FixedTreeMaterializer<FakeValue>,
        requests: &mut Vec<PendingBinding>,
    ) -> usize {
        materializer
            .drain_pending(|request| {
                if let BindingRhs::Constructor { children, .. } = &request.rhs {
                    assert!(children.iter().all(|child| child.0 < request.binding.0));
                }
                let value = FakeValue(request.binding.0 + 1);
                requests.push(request.clone());
                Ok::<_, ()>(value)
            })
            .unwrap()
    }

    fn drain_output(
        materializer: &mut FixedTreeMaterializer<FakeValue>,
    ) -> Vec<MaterializedCandidate<FakeValue>> {
        let mut output = Vec::new();
        materializer.drain_materialized(&mut output);
        output
    }

    #[test]
    fn ignores_static_full_spaces_and_open_tokens() {
        let mut materializer = FixedTreeMaterializer::<FakeValue>::new(3, 2, vec![schema(&[0], 1)]);
        assert!(!materializer.add_exact(dynamic(1), TypedExact::string(0, "x")));
        assert!(!materializer.add_constructor(0, dynamic(0), smallvec![dynamic(3)]));
        assert!(!materializer.add_constructor(0, dynamic(3), smallvec![dynamic(1)]));
        assert_eq!(materializer.pending_count(), 0);
    }

    #[test]
    fn exact_string_and_i64_leaves_remain_typed() {
        let mut materializer = FixedTreeMaterializer::<FakeValue>::new(2, 2, vec![]);
        materializer.add_exact(dynamic(2), TypedExact::string(0, "hello"));
        materializer.add_exact(dynamic(3), TypedExact::i64(1, 42));

        let mut requests = Vec::new();
        assert_eq!(evaluate_all(&mut materializer, &mut requests), 2);
        assert!(requests.iter().any(|request| {
            request.sort == 0
                && request.rhs == BindingRhs::Exact(ExactSource::String(Arc::from("hello")))
        }));
        assert!(requests.iter().any(|request| {
            request.sort == 1 && request.rhs == BindingRhs::Exact(ExactSource::I64(42))
        }));
        assert_eq!(
            requests[0].egglog_name("__private"),
            "$__private_fixed_tree_0"
        );
    }

    #[test]
    fn aliases_propagate_existing_and_late_candidates_without_new_bindings() {
        let mut materializer = FixedTreeMaterializer::<FakeValue>::new(1, 1, vec![]);
        let leaf = dynamic(1);
        let middle = dynamic(2);
        let output = dynamic(3);
        materializer.add_exact(leaf, TypedExact::string(0, "x"));
        evaluate_all(&mut materializer, &mut Vec::new());
        drain_output(&mut materializer);

        assert!(materializer.add_alias(middle, leaf));
        assert!(materializer.add_alias(output, middle));
        assert!(materializer.add_alias(middle, output));
        assert!(!materializer.add_alias(middle, leaf));
        assert_eq!(materializer.binding_count(), 1);
        assert_eq!(materializer.candidates(output, 0).count(), 1);
        assert_eq!(
            drain_output(&mut materializer)
                .iter()
                .filter(|candidate| candidate.space == output)
                .count(),
            1
        );
    }

    #[test]
    fn constructor_cross_product_handles_ambiguity() {
        let mut materializer =
            FixedTreeMaterializer::<FakeValue>::new(1, 3, vec![schema(&[0, 1], 2)]);
        let left = dynamic(1);
        let right = dynamic(2);
        let output = dynamic(3);
        materializer.add_constructor(0, output, smallvec![left, right]);
        materializer.add_exact(left, TypedExact::string(0, "a"));
        materializer.add_exact(left, TypedExact::string(0, "b"));
        materializer.add_exact(right, TypedExact::i64(1, 1));
        materializer.add_exact(right, TypedExact::i64(1, 2));

        let mut requests = Vec::new();
        assert_eq!(evaluate_all(&mut materializer, &mut requests), 8);
        assert_eq!(
            requests
                .iter()
                .filter(|request| matches!(request.rhs, BindingRhs::Constructor { .. }))
                .count(),
            4
        );
        assert_eq!(materializer.candidates(output, 2).count(), 4);
    }

    #[test]
    fn late_constructor_and_late_children_both_catch_up() {
        let mut materializer =
            FixedTreeMaterializer::<FakeValue>::new(1, 2, vec![schema(&[0, 0], 1)]);
        let a = dynamic(1);
        let b = dynamic(2);
        let early_output = dynamic(3);
        let late_output = dynamic(4);
        materializer.add_constructor(0, early_output, smallvec![a, b]);

        materializer.add_exact(a, TypedExact::string(0, "a"));
        evaluate_all(&mut materializer, &mut Vec::new());
        assert_eq!(materializer.candidates(early_output, 1).count(), 0);
        materializer.add_exact(b, TypedExact::string(0, "b"));
        evaluate_all(&mut materializer, &mut Vec::new());
        assert_eq!(materializer.candidates(early_output, 1).count(), 1);

        materializer.add_constructor(0, late_output, smallvec![a, b]);
        evaluate_all(&mut materializer, &mut Vec::new());
        assert_eq!(materializer.candidates(late_output, 1).count(), 1);
    }

    #[test]
    fn equal_returned_values_are_suppressed_before_parent_products() {
        let mut materializer = FixedTreeMaterializer::<FakeValue>::new(1, 2, vec![schema(&[0], 1)]);
        let union = dynamic(1);
        let output = dynamic(2);
        materializer.add_constructor(0, output, smallvec![union]);
        materializer.add_exact(union, TypedExact::string(0, "left spelling"));
        materializer.add_exact(union, TypedExact::string(0, "right spelling"));

        let mut exact_count = 0;
        let mut constructor_count = 0;
        materializer
            .drain_pending(|request| {
                let value = match request.rhs {
                    BindingRhs::Exact(_) => {
                        exact_count += 1;
                        FakeValue(7)
                    }
                    BindingRhs::Constructor { .. } => {
                        constructor_count += 1;
                        FakeValue(8)
                    }
                };
                Ok::<_, ()>(value)
            })
            .unwrap();
        assert_eq!(exact_count, 2);
        assert_eq!(constructor_count, 1);
        assert_eq!(materializer.candidates(union, 0).count(), 1);
        assert_eq!(materializer.candidates(output, 1).count(), 1);
    }

    #[test]
    fn deep_trees_emit_one_level_bindings_instead_of_cloned_asts() {
        let mut materializer = FixedTreeMaterializer::<FakeValue>::new(1, 1, vec![schema(&[0], 0)]);
        let leaf = dynamic(1);
        let mut child = leaf;
        for index in 2..=102 {
            let output = dynamic(index);
            materializer.add_constructor(0, output, smallvec![child]);
            child = output;
        }
        materializer.add_exact(leaf, TypedExact::string(0, "leaf"));

        let mut requests = Vec::new();
        assert_eq!(evaluate_all(&mut materializer, &mut requests), 102);
        for request in &requests[1..] {
            let BindingRhs::Constructor { children, .. } = &request.rhs else {
                panic!("only the first request should be a primitive leaf");
            };
            assert_eq!(children.len(), 1);
        }
        assert_eq!(materializer.candidates(child, 0).count(), 1);
    }
}
