//! Bounded reconstruction of concrete AST roots from the current PwZ zipper.
//!
//! PwZ facts are immutable.  This module indexes them once, then passes the
//! concrete bindings for each current frontier space out through its zipper
//! contexts.  It never invents a value for an open/static space: such a value
//! is represented by `Any`, and `complete` is cleared if that unknown value is
//! semantically selected or reaches the root.

use std::{collections::VecDeque, hash::Hash};

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::{SmallVec, smallvec};

use crate::{
    fixed_tree::{BindingId, FixedSpaceId, FixedTreeMaterializer},
    forest::{Frontier, SpaceId, ZipperFact},
};

pub(crate) const DEFAULT_PREFIX_OUTPUT_WORK_BUDGET: usize = 2_048;
const TOP_CONTEXT: u32 = 0;

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContextAction {
    Alternative {
        memo: u32,
    },
    ConstructHole {
        constructor: usize,
        memo: u32,
        hole_argument: usize,
        fixed_children: SmallVec<[SpaceId; 4]>,
    },
    ConstructIgnored {
        constructor: usize,
        memo: u32,
        children: SmallVec<[SpaceId; 4]>,
    },
    ProjectHole {
        memo: u32,
    },
    ProjectFixed {
        memo: u32,
        child: SpaceId,
    },
}

impl ContextAction {
    fn memo(&self) -> u32 {
        match self {
            Self::Alternative { memo }
            | Self::ConstructHole { memo, .. }
            | Self::ConstructIgnored { memo, .. }
            | Self::ProjectHole { memo }
            | Self::ProjectFixed { memo, .. } => *memo,
        }
    }

    fn fixed_spaces(&self) -> &[SpaceId] {
        match self {
            Self::ConstructHole { fixed_children, .. } => fixed_children,
            Self::ConstructIgnored { children, .. } => children,
            Self::ProjectFixed { child, .. } => std::slice::from_ref(child),
            Self::Alternative { .. } | Self::ProjectHole { .. } => &[],
        }
    }

    fn is_input_independent(&self) -> bool {
        matches!(
            self,
            Self::ConstructIgnored { .. } | Self::ProjectFixed { .. }
        )
    }
}

/// Append-only index over the immutable zipper facts emitted by PwZ.
#[derive(Default)]
pub(crate) struct PrefixOutputBuilder {
    parents_by_memo: Vec<SmallVec<[u32; 2]>>,
    contexts: Vec<Option<ContextAction>>,
    parent_facts: HashSet<(u32, u32)>,

    // Persistent, monotone focus propagation.  This is deliberately separate
    // from `enumerate`: focus is existential/best-effort and may retain old
    // prefix states, while a disjointness proof needs a fresh universal
    // snapshot of exactly the current frontier.
    focus_seen: HashSet<State>,
    focus_agenda: VecDeque<State>,
    focus_memo_payloads: Vec<SmallVec<[Payload; 2]>>,
    focus_context_payloads: Vec<SmallVec<[Payload; 2]>>,
    focus_frontiers_by_space: Vec<SmallVec<[u32; 2]>>,
    focus_frontier_facts: HashSet<(FixedSpaceId, u32)>,
    focus_candidates_by_space: Vec<SmallVec<[BindingId; 2]>>,
    focus_candidate_facts: HashSet<(FixedSpaceId, BindingId)>,
    focus_contexts_by_space: Vec<SmallVec<[u32; 2]>>,
    focus_context_space_facts: HashSet<(FixedSpaceId, u32)>,
    /// Independent contexts need run only once until one of their fixed
    /// spaces gains a candidate.
    focus_independent_clean: HashSet<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PrefixOutput {
    pub(crate) roots: Vec<BindingId>,
    /// True only if every reachable semantic branch was concretely enumerated.
    pub(crate) complete: bool,
    pub(crate) work: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Payload {
    Concrete(BindingId),
    Any,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum State {
    Memo(u32, Payload),
    Context(u32, Payload),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum GraphNode {
    Memo(u32),
    Context(u32),
}

#[derive(Clone, Copy, Debug)]
struct Budget {
    limit: usize,
    used: usize,
}

impl Budget {
    fn spend(&mut self) -> bool {
        if self.used >= self.limit {
            false
        } else {
            self.used += 1;
            true
        }
    }
}

impl PrefixOutputBuilder {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn add_fact(&mut self, fact: &ZipperFact) {
        match fact {
            ZipperFact::Parent { memo, context } => {
                let memo = memo.as_u32();
                let context = context.as_u32();
                if self.parent_facts.insert((memo, context)) {
                    self.ensure_memo(memo);
                    self.parents_by_memo[memo as usize].push(context);
                    if context != TOP_CONTEXT {
                        let payloads = self
                            .focus_memo_payloads
                            .get(memo as usize)
                            .cloned()
                            .unwrap_or_default();
                        for payload in payloads {
                            self.insert_focus_state(State::Context(context, payload));
                        }
                    }
                }
            }
            ZipperFact::Alternative { context, memo } => self.install_context(
                context.as_u32(),
                ContextAction::Alternative {
                    memo: memo.as_u32(),
                },
            ),
            ZipperFact::ConstructHole {
                constructor,
                context,
                memo,
                hole_argument,
                fixed_children,
            } => self.install_context(
                context.as_u32(),
                ContextAction::ConstructHole {
                    constructor: *constructor as usize,
                    memo: memo.as_u32(),
                    hole_argument: *hole_argument,
                    fixed_children: fixed_children.clone(),
                },
            ),
            ZipperFact::ConstructIgnored {
                constructor,
                context,
                memo,
                children,
            } => self.install_context(
                context.as_u32(),
                ContextAction::ConstructIgnored {
                    constructor: *constructor as usize,
                    memo: memo.as_u32(),
                    children: children.clone(),
                },
            ),
            ZipperFact::ProjectHole { context, memo } => self.install_context(
                context.as_u32(),
                ContextAction::ProjectHole {
                    memo: memo.as_u32(),
                },
            ),
            ZipperFact::ProjectFixed {
                context,
                memo,
                child,
            } => self.install_context(
                context.as_u32(),
                ContextAction::ProjectFixed {
                    memo: memo.as_u32(),
                    child: *child,
                },
            ),
        }
    }

    /// Announces one evaluated binding attached to a concrete PwZ space.
    ///
    /// The announcement is retained. Existing registered frontiers and zipper
    /// contexts which depend on this space are caught up without replaying an
    /// unrelated historical path.
    pub(crate) fn notify_focus_candidate(&mut self, space: FixedSpaceId, binding: BindingId) {
        if !self.focus_candidate_facts.insert((space, binding)) {
            return;
        }
        self.ensure_focus_space(space);
        self.focus_candidates_by_space[space.index()].push(binding);

        let memos = self.focus_frontiers_by_space[space.index()].clone();
        for memo in memos {
            self.insert_focus_state(State::Memo(memo, Payload::Concrete(binding)));
        }

        let contexts = self.focus_contexts_by_space[space.index()].clone();
        for context in contexts {
            let Some(action) = self
                .contexts
                .get(context as usize)
                .and_then(Option::as_ref)
                .cloned()
            else {
                continue;
            };
            let payloads = self
                .focus_context_payloads
                .get(context as usize)
                .cloned()
                .unwrap_or_default();
            if action.is_input_independent() {
                self.focus_independent_clean.remove(&context);
                if let Some(payload) = payloads.first().copied() {
                    self.focus_agenda
                        .push_back(State::Context(context, payload));
                }
            } else {
                for payload in payloads {
                    self.focus_agenda
                        .push_back(State::Context(context, payload));
                }
            }
        }
    }

    /// Marks the current parser frontier as relevant to focused analysis.
    ///
    /// Repeating an unchanged `(space, memo)` pair is free.  `Any` is retained
    /// as well as concrete candidates because an enclosing ProjectFixed or
    /// ConstructIgnored context can produce a concrete term while ignoring
    /// the current semantic value.
    pub(crate) fn mark_frontier_relevant(&mut self, frontier: &[Frontier]) {
        for item in frontier {
            let space = FixedSpaceId::from_pwz(item.space);
            let memo = item.memo.as_u32();
            if self.focus_frontier_facts.insert((space, memo)) {
                self.ensure_focus_space(space);
                self.focus_frontiers_by_space[space.index()].push(memo);
                self.insert_focus_state(State::Memo(memo, Payload::Any));
                let candidates = self.focus_candidates_by_space[space.index()].clone();
                for binding in candidates {
                    self.insert_focus_state(State::Memo(memo, Payload::Concrete(binding)));
                }
            }
        }
    }

    /// Closes the persistent concrete-focus delta up to `work_budget` units.
    ///
    /// Constructor contexts intern only one shallow node at a time in
    /// `fixed`.  If a constructor cycle or expansion consumes the budget, the
    /// residual agenda is dropped: focus is an optimization and must not make
    /// a later lexeme resume an unbounded old expansion.  Already discovered
    /// states and terms remain available for catch-up from genuinely new
    /// edges or fixed-space candidates.
    pub(crate) fn drain_focus<Value>(
        &mut self,
        fixed: &mut FixedTreeMaterializer<Value>,
        work_budget: usize,
    ) -> usize
    where
        Value: Copy + Eq + Hash,
    {
        let mut budget = Budget {
            limit: work_budget,
            used: 0,
        };
        while let Some(state) = self.focus_agenda.pop_front() {
            if !budget.spend() {
                self.focus_agenda.clear();
                break;
            }
            match state {
                State::Memo(memo, payload) => {
                    let parents = self
                        .parents_by_memo
                        .get(memo as usize)
                        .cloned()
                        .unwrap_or_default();
                    for context in parents {
                        if context != TOP_CONTEXT {
                            self.insert_focus_state(State::Context(context, payload));
                        }
                    }
                }
                State::Context(context, payload) => {
                    let Some(action) = self
                        .contexts
                        .get(context as usize)
                        .and_then(Option::as_ref)
                        .cloned()
                    else {
                        continue;
                    };
                    if action.is_input_independent()
                        && !self.focus_independent_clean.insert(context)
                    {
                        continue;
                    }
                    match action {
                        ContextAction::Alternative { memo }
                        | ContextAction::ProjectHole { memo } => {
                            self.insert_focus_state(State::Memo(memo, payload));
                        }
                        ContextAction::ProjectFixed { memo, child } => {
                            let bindings = fixed
                                .all_candidate_bindings(FixedSpaceId::from_pwz(child))
                                .map(|(_, binding)| binding)
                                .collect::<Vec<_>>();
                            if bindings.is_empty() {
                                self.insert_focus_state(State::Memo(memo, Payload::Any));
                            } else {
                                for binding in bindings {
                                    self.insert_focus_state(State::Memo(
                                        memo,
                                        Payload::Concrete(binding),
                                    ));
                                }
                            }
                        }
                        ContextAction::ConstructHole {
                            constructor,
                            memo,
                            hole_argument,
                            fixed_children,
                        } => match payload {
                            Payload::Any => {
                                self.insert_focus_state(State::Memo(memo, Payload::Any));
                            }
                            Payload::Concrete(hole) => {
                                if fixed.binding_sort(hole)
                                    != fixed.constructor_schema(constructor).inputs[hole_argument]
                                {
                                    continue;
                                }
                                match self.construct(
                                    fixed,
                                    constructor,
                                    Some((hole_argument, hole)),
                                    &fixed_children,
                                    &mut budget,
                                ) {
                                    Some(bindings) => {
                                        for binding in bindings {
                                            self.insert_focus_state(State::Memo(
                                                memo,
                                                Payload::Concrete(binding),
                                            ));
                                        }
                                    }
                                    None => {
                                        self.insert_focus_state(State::Memo(memo, Payload::Any));
                                    }
                                }
                            }
                        },
                        ContextAction::ConstructIgnored {
                            constructor,
                            memo,
                            children,
                        } => match self.construct(fixed, constructor, None, &children, &mut budget)
                        {
                            Some(bindings) => {
                                for binding in bindings {
                                    self.insert_focus_state(State::Memo(
                                        memo,
                                        Payload::Concrete(binding),
                                    ));
                                }
                            }
                            None => {
                                self.insert_focus_state(State::Memo(memo, Payload::Any));
                            }
                        },
                    }
                }
            }
            if budget.used >= budget.limit && !self.focus_agenda.is_empty() {
                self.focus_agenda.clear();
                break;
            }
        }
        budget.used
    }

    /// Enumerates concrete roots for one parser derivative.
    ///
    /// `complete == false` is deliberately conservative.  In particular it
    /// is returned for a reachable zipper cycle, a missing/open selected
    /// value, or exhausted work budget.
    pub(crate) fn enumerate<Value>(
        &self,
        frontier: &[Frontier],
        fixed: &mut FixedTreeMaterializer<Value>,
        work_budget: usize,
    ) -> PrefixOutput
    where
        Value: Copy + Eq + Hash,
    {
        let mut budget = Budget {
            limit: work_budget,
            used: 0,
        };
        if self.reachable_cycle(frontier, &mut budget) {
            return PrefixOutput {
                roots: Vec::new(),
                complete: false,
                work: budget.used,
            };
        }
        let mut complete = true;
        let mut agenda = VecDeque::new();
        let mut seen = HashSet::default();
        let mut roots = HashSet::default();
        let mut independent_done = HashSet::default();

        for item in frontier {
            let bindings = fixed
                .all_candidate_bindings(FixedSpaceId::from_pwz(item.space))
                .map(|(_, binding)| binding)
                .collect::<Vec<_>>();
            if bindings.is_empty() {
                enqueue(
                    &mut agenda,
                    &mut seen,
                    State::Memo(item.memo.as_u32(), Payload::Any),
                );
            } else {
                for binding in bindings {
                    enqueue(
                        &mut agenda,
                        &mut seen,
                        State::Memo(item.memo.as_u32(), Payload::Concrete(binding)),
                    );
                }
            }
        }

        while let Some(state) = agenda.pop_front() {
            if !budget.spend() {
                complete = false;
                break;
            }
            match state {
                State::Memo(memo, payload) => {
                    let Some(parents) = self.parents_by_memo.get(memo as usize) else {
                        complete = false;
                        continue;
                    };
                    if parents.is_empty() {
                        complete = false;
                    }
                    for &context in parents {
                        if context == TOP_CONTEXT {
                            match payload {
                                Payload::Concrete(binding) => {
                                    roots.insert(binding);
                                }
                                Payload::Any => complete = false,
                            }
                        } else {
                            enqueue(&mut agenda, &mut seen, State::Context(context, payload));
                        }
                    }
                }
                State::Context(context, payload) => {
                    let Some(Some(action)) = self.contexts.get(context as usize) else {
                        complete = false;
                        continue;
                    };
                    match action {
                        ContextAction::Alternative { memo } => {
                            enqueue(&mut agenda, &mut seen, State::Memo(*memo, payload))
                        }
                        ContextAction::ProjectHole { memo } => {
                            if payload == Payload::Any {
                                complete = false;
                            }
                            enqueue(&mut agenda, &mut seen, State::Memo(*memo, payload));
                        }
                        ContextAction::ProjectFixed { memo, child } => {
                            if !independent_done.insert(context) {
                                continue;
                            }
                            let bindings = fixed
                                .all_candidate_bindings(FixedSpaceId::from_pwz(*child))
                                .map(|(_, binding)| binding)
                                .collect::<Vec<_>>();
                            if bindings.is_empty() {
                                complete = false;
                                enqueue(&mut agenda, &mut seen, State::Memo(*memo, Payload::Any));
                            } else {
                                for binding in bindings {
                                    enqueue(
                                        &mut agenda,
                                        &mut seen,
                                        State::Memo(*memo, Payload::Concrete(binding)),
                                    );
                                }
                            }
                        }
                        ContextAction::ConstructHole {
                            constructor,
                            memo,
                            hole_argument,
                            fixed_children,
                        } => match payload {
                            Payload::Any => {
                                complete = false;
                                enqueue(&mut agenda, &mut seen, State::Memo(*memo, Payload::Any));
                            }
                            Payload::Concrete(hole) => {
                                if fixed.binding_sort(hole)
                                    != fixed.constructor_schema(*constructor).inputs[*hole_argument]
                                {
                                    continue;
                                }
                                match self.construct(
                                    fixed,
                                    *constructor,
                                    Some((*hole_argument, hole)),
                                    fixed_children,
                                    &mut budget,
                                ) {
                                    Some(bindings) => {
                                        for binding in bindings {
                                            enqueue(
                                                &mut agenda,
                                                &mut seen,
                                                State::Memo(*memo, Payload::Concrete(binding)),
                                            );
                                        }
                                    }
                                    None => {
                                        complete = false;
                                        enqueue(
                                            &mut agenda,
                                            &mut seen,
                                            State::Memo(*memo, Payload::Any),
                                        );
                                    }
                                }
                            }
                        },
                        ContextAction::ConstructIgnored {
                            constructor,
                            memo,
                            children,
                        } => {
                            if !independent_done.insert(context) {
                                continue;
                            }
                            match self.construct(fixed, *constructor, None, children, &mut budget) {
                                Some(bindings) => {
                                    for binding in bindings {
                                        enqueue(
                                            &mut agenda,
                                            &mut seen,
                                            State::Memo(*memo, Payload::Concrete(binding)),
                                        );
                                    }
                                }
                                None => {
                                    complete = false;
                                    enqueue(
                                        &mut agenda,
                                        &mut seen,
                                        State::Memo(*memo, Payload::Any),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        if budget.used >= budget.limit && !agenda.is_empty() {
            complete = false;
        }
        let mut roots = roots.into_iter().collect::<Vec<_>>();
        roots.sort_unstable();
        PrefixOutput {
            roots,
            complete,
            work: budget.used,
        }
    }

    fn construct<Value>(
        &self,
        fixed: &mut FixedTreeMaterializer<Value>,
        constructor: usize,
        hole: Option<(usize, BindingId)>,
        fixed_spaces: &[SpaceId],
        budget: &mut Budget,
    ) -> Option<Vec<BindingId>>
    where
        Value: Copy + Eq + Hash,
    {
        let inputs = fixed.constructor_schema(constructor).inputs.clone();
        if let Some((argument, _)) = hole {
            if argument >= inputs.len() || fixed_spaces.len() + 1 != inputs.len() {
                return None;
            }
        } else if fixed_spaces.len() != inputs.len() {
            return None;
        }

        let mut choices = Vec::<Vec<BindingId>>::with_capacity(inputs.len());
        let mut fixed_offset = 0;
        for (argument, &sort) in inputs.iter().enumerate() {
            if let Some((hole_argument, binding)) = hole
                && argument == hole_argument
            {
                choices.push(vec![binding]);
                continue;
            }
            let space = FixedSpaceId::from_pwz(fixed_spaces[fixed_offset]);
            fixed_offset += 1;
            let candidates = fixed
                .candidates(space, sort)
                .map(|(binding, _)| binding)
                .collect::<Vec<_>>();
            if candidates.is_empty() {
                return None;
            }
            choices.push(candidates);
        }

        if choices.is_empty() {
            if !budget.spend() {
                return None;
            }
            return Some(vec![
                fixed.intern_detached_constructor(constructor, SmallVec::new()),
            ]);
        }
        let mut positions = vec![0usize; choices.len()];
        let mut output = Vec::new();
        loop {
            if !budget.spend() {
                return None;
            }
            let children = choices
                .iter()
                .zip(&positions)
                .map(|(values, &position)| values[position])
                .collect::<SmallVec<[BindingId; 4]>>();
            output.push(fixed.intern_detached_constructor(constructor, children));

            let mut cursor = positions.len();
            let advanced = loop {
                if cursor == 0 {
                    break false;
                }
                cursor -= 1;
                positions[cursor] += 1;
                if positions[cursor] < choices[cursor].len() {
                    break true;
                }
                positions[cursor] = 0;
            };
            if !advanced {
                break;
            }
        }
        Some(output)
    }

    fn reachable_cycle(&self, frontier: &[Frontier], budget: &mut Budget) -> bool {
        // Iterative DFS with grey/black colouring.  A reachable graph cycle can
        // denote unbounded constructor growth, so bounded enumeration must not
        // claim completeness even when state dedup happens to stop it.
        let mut colour = HashMap::<GraphNode, u8>::default();
        for item in frontier {
            let root = GraphNode::Memo(item.memo.as_u32());
            if colour.get(&root) == Some(&2) {
                continue;
            }
            let mut stack = vec![(root, false)];
            while let Some((node, exit)) = stack.pop() {
                if !budget.spend() {
                    return true;
                }
                if exit {
                    colour.insert(node, 2);
                    continue;
                }
                match colour.get(&node).copied() {
                    Some(1) => return true,
                    Some(2) => continue,
                    _ => {}
                }
                colour.insert(node, 1);
                stack.push((node, true));
                let successors = self.graph_successors(node);
                for successor in successors.into_iter().rev() {
                    match colour.get(&successor).copied() {
                        Some(1) => return true,
                        Some(2) => {}
                        _ => stack.push((successor, false)),
                    }
                }
            }
        }
        false
    }

    fn graph_successors(&self, node: GraphNode) -> SmallVec<[GraphNode; 4]> {
        match node {
            GraphNode::Memo(memo) => self
                .parents_by_memo
                .get(memo as usize)
                .into_iter()
                .flatten()
                .filter(|&&context| context != TOP_CONTEXT)
                .map(|&context| GraphNode::Context(context))
                .collect(),
            GraphNode::Context(context) => self
                .contexts
                .get(context as usize)
                .and_then(Option::as_ref)
                .map(|action| smallvec![GraphNode::Memo(action.memo())])
                .unwrap_or_default(),
        }
    }

    fn ensure_memo(&mut self, memo: u32) {
        if self.parents_by_memo.len() <= memo as usize {
            self.parents_by_memo
                .resize_with(memo as usize + 1, SmallVec::new);
        }
    }

    fn install_context(&mut self, context: u32, action: ContextAction) {
        if self.contexts.len() <= context as usize {
            self.contexts.resize_with(context as usize + 1, || None);
        }
        match &self.contexts[context as usize] {
            Some(existing) => {
                assert_eq!(existing, &action, "conflicting immutable zipper facts");
                return;
            }
            None => self.contexts[context as usize] = Some(action.clone()),
        }

        for &space in action.fixed_spaces() {
            let space = FixedSpaceId::from_pwz(space);
            if self.focus_context_space_facts.insert((space, context)) {
                self.ensure_focus_space(space);
                self.focus_contexts_by_space[space.index()].push(context);
            }
        }

        // The context may have become reachable before its immutable shape
        // fact arrived. Reprocess only those retained source payloads.
        let payloads = self
            .focus_context_payloads
            .get(context as usize)
            .cloned()
            .unwrap_or_default();
        for payload in payloads {
            self.focus_agenda
                .push_back(State::Context(context, payload));
        }
    }

    fn insert_focus_state(&mut self, state: State) -> bool {
        if !self.focus_seen.insert(state) {
            return false;
        }
        match state {
            State::Memo(memo, payload) => {
                if self.focus_memo_payloads.len() <= memo as usize {
                    self.focus_memo_payloads
                        .resize_with(memo as usize + 1, SmallVec::new);
                }
                self.focus_memo_payloads[memo as usize].push(payload);
            }
            State::Context(context, payload) => {
                if self.focus_context_payloads.len() <= context as usize {
                    self.focus_context_payloads
                        .resize_with(context as usize + 1, SmallVec::new);
                }
                self.focus_context_payloads[context as usize].push(payload);
            }
        }
        self.focus_agenda.push_back(state);
        true
    }

    fn ensure_focus_space(&mut self, space: FixedSpaceId) {
        let len = space.index() + 1;
        if self.focus_frontiers_by_space.len() < len {
            self.focus_frontiers_by_space
                .resize_with(len, SmallVec::new);
        }
        if self.focus_candidates_by_space.len() < len {
            self.focus_candidates_by_space
                .resize_with(len, SmallVec::new);
        }
        if self.focus_contexts_by_space.len() < len {
            self.focus_contexts_by_space.resize_with(len, SmallVec::new);
        }
    }
}

fn enqueue(agenda: &mut VecDeque<State>, seen: &mut HashSet<State>, state: State) {
    if seen.insert(state) {
        agenda.push_back(state);
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;

    use super::{DEFAULT_PREFIX_OUTPUT_WORK_BUDGET, PrefixOutputBuilder};
    use crate::{
        fixed_tree::{BindingRhs, FixedSpaceId, FixedTreeMaterializer, PendingBinding, TypedExact},
        forest::{ContextId, Frontier, MemoId, SpaceId, ZipperFact},
        realizability::ConstructorSchema,
    };

    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    struct FakeValue(u32);

    fn schema(inputs: &[usize], output: usize) -> ConstructorSchema {
        ConstructorSchema {
            inputs: inputs.to_vec(),
            output,
        }
    }

    fn space(value: u32) -> SpaceId {
        SpaceId::from_u32_for_test(value)
    }

    fn fixed_space(value: u32) -> FixedSpaceId {
        FixedSpaceId::from_index(value as usize)
    }

    fn memo(value: u32) -> MemoId {
        MemoId::from_u32_for_test(value)
    }

    fn context(value: u32) -> ContextId {
        ContextId::from_u32_for_test(value)
    }

    fn frontier(memo_id: u32, space_id: u32) -> Frontier {
        Frontier {
            memo: memo(memo_id),
            space: space(space_id),
        }
    }

    fn resolve_all(
        fixed: &mut FixedTreeMaterializer<FakeValue>,
        requests: &mut Vec<PendingBinding>,
    ) {
        fixed
            .drain_pending(|request| {
                requests.push(request.clone());
                Ok::<_, ()>(FakeValue(request.binding.index() as u32 + 100))
            })
            .unwrap();
    }

    fn parent(builder: &mut PrefixOutputBuilder, memo_id: u32, context_id: u32) {
        builder.add_fact(&ZipperFact::Parent {
            memo: memo(memo_id),
            context: context(context_id),
        });
    }

    #[test]
    fn project_fixed_ignores_unknown_input_and_returns_fixed_child_completely() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "fixed"));
        resolve_all(&mut fixed, &mut Vec::new());
        let fixed_binding = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 1);
        builder.add_fact(&ZipperFact::ProjectFixed {
            context: context(1),
            memo: memo(1),
            child: space(1),
        });
        parent(&mut builder, 1, 0);

        // Space zero is static/open, but ProjectFixed discards its value.
        let output = builder.enumerate(
            &[frontier(0, 0)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(output.complete);
        assert_eq!(output.roots, vec![fixed_binding]);
    }

    #[test]
    fn construct_ignored_nullary_returns_root_from_unknown_input() {
        let mut fixed = FixedTreeMaterializer::<FakeValue>::new(1, 1, vec![schema(&[], 0)]);
        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 1);
        builder.add_fact(&ZipperFact::ConstructIgnored {
            constructor: 0,
            context: context(1),
            memo: memo(1),
            children: smallvec![],
        });
        parent(&mut builder, 1, 0);

        let output = builder.enumerate(
            &[frontier(0, 0)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(output.complete);
        assert_eq!(output.roots.len(), 1);
        assert_eq!(fixed.pending_count(), 1);

        let mut requests = Vec::new();
        resolve_all(&mut fixed, &mut requests);
        assert_eq!(
            requests[0].rhs,
            BindingRhs::Constructor {
                constructor: 0,
                children: smallvec![]
            }
        );
        assert!(fixed.binding_value(output.roots[0]).is_some());
    }

    #[test]
    fn construct_hole_builds_one_shallow_root_from_exact_hole() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![schema(&[0], 0)]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());
        let leaf = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 1);
        builder.add_fact(&ZipperFact::ConstructHole {
            constructor: 0,
            context: context(1),
            memo: memo(1),
            hole_argument: 0,
            fixed_children: smallvec![],
        });
        parent(&mut builder, 1, 0);

        let output = builder.enumerate(
            &[frontier(0, 1)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(output.complete);
        assert_eq!(output.roots.len(), 1);

        let mut requests = Vec::new();
        resolve_all(&mut fixed, &mut requests);
        assert_eq!(
            requests[0].rhs,
            BindingRhs::Constructor {
                constructor: 0,
                children: smallvec![leaf]
            }
        );
    }

    #[test]
    fn open_fixed_constructor_child_makes_enumeration_incomplete() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![schema(&[0, 0], 0)]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "hole"));
        resolve_all(&mut fixed, &mut Vec::new());

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 1);
        builder.add_fact(&ZipperFact::ConstructHole {
            constructor: 0,
            context: context(1),
            memo: memo(1),
            hole_argument: 0,
            // Static space zero is an unknown future child.
            fixed_children: smallvec![space(0)],
        });
        parent(&mut builder, 1, 0);

        let output = builder.enumerate(
            &[frontier(0, 1)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(!output.complete);
        assert!(output.roots.is_empty());
    }

    #[test]
    fn ambiguous_frontier_enumerates_every_concrete_root() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "left"));
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "right"));
        resolve_all(&mut fixed, &mut Vec::new());
        let expected = fixed
            .candidates(fixed_space(1), 0)
            .map(|(binding, _)| binding)
            .collect::<Vec<_>>();

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 0);
        let output = builder.enumerate(
            &[frontier(0, 1)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(output.complete);
        assert_eq!(output.roots, expected);
    }

    #[test]
    fn reachable_zipper_cycle_is_never_reported_complete() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 1);
        builder.add_fact(&ZipperFact::ProjectHole {
            context: context(1),
            memo: memo(0),
        });
        let output = builder.enumerate(
            &[frontier(0, 1)],
            &mut fixed,
            DEFAULT_PREFIX_OUTPUT_WORK_BUDGET,
        );
        assert!(!output.complete);
        assert!(output.roots.is_empty());
    }

    #[test]
    fn tiny_work_budget_is_never_reported_complete() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());

        let mut builder = PrefixOutputBuilder::new();
        parent(&mut builder, 0, 0);
        let output = builder.enumerate(&[frontier(0, 1)], &mut fixed, 1);
        assert!(!output.complete);
    }

    #[test]
    fn persistent_focus_catches_up_a_late_parent_and_context() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![schema(&[0], 0)]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());
        let leaf = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        builder.notify_focus_candidate(fixed_space(1), leaf);
        builder.mark_frontier_relevant(&[frontier(0, 1)]);
        assert!(builder.drain_focus(&mut fixed, 32) > 0);
        assert_eq!(fixed.pending_count(), 0);

        // Shape and parent facts arrive after the memo payload was retained.
        builder.add_fact(&ZipperFact::ConstructHole {
            constructor: 0,
            context: context(1),
            memo: memo(1),
            hole_argument: 0,
            fixed_children: smallvec![],
        });
        parent(&mut builder, 0, 1);
        parent(&mut builder, 1, 0);
        assert!(builder.drain_focus(&mut fixed, 32) > 0);
        assert_eq!(fixed.pending_count(), 1);

        let mut requests = Vec::new();
        resolve_all(&mut fixed, &mut requests);
        assert_eq!(
            requests[0].rhs,
            BindingRhs::Constructor {
                constructor: 0,
                children: smallvec![leaf]
            }
        );
    }

    #[test]
    fn persistent_focus_requeues_a_constructor_when_a_fixed_candidate_arrives() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![schema(&[0, 0], 0)]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "hole"));
        resolve_all(&mut fixed, &mut Vec::new());
        let hole = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        builder.add_fact(&ZipperFact::ConstructHole {
            constructor: 0,
            context: context(1),
            memo: memo(1),
            hole_argument: 0,
            fixed_children: smallvec![space(2)],
        });
        parent(&mut builder, 0, 1);
        parent(&mut builder, 1, 0);
        builder.notify_focus_candidate(fixed_space(1), hole);
        builder.mark_frontier_relevant(&[frontier(0, 1)]);
        builder.drain_focus(&mut fixed, 32);
        assert_eq!(fixed.pending_count(), 0);

        fixed.add_exact(fixed_space(2), TypedExact::string(0, "late"));
        resolve_all(&mut fixed, &mut Vec::new());
        let late = fixed.candidates(fixed_space(2), 0).next().unwrap().0;
        builder.notify_focus_candidate(fixed_space(2), late);
        assert!(builder.drain_focus(&mut fixed, 32) > 0);
        assert_eq!(fixed.pending_count(), 1);

        let mut requests = Vec::new();
        resolve_all(&mut fixed, &mut requests);
        assert_eq!(
            requests[0].rhs,
            BindingRhs::Constructor {
                constructor: 0,
                children: smallvec![hole, late]
            }
        );
    }

    #[test]
    fn persistent_focus_repeated_frontier_and_growing_identity_chain_are_delta_only() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());
        let leaf = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        builder.notify_focus_candidate(fixed_space(1), leaf);
        builder.mark_frontier_relevant(&[frontier(0, 1)]);
        assert_eq!(builder.drain_focus(&mut fixed, 32), 2); // Any and concrete.
        builder.mark_frontier_relevant(&[frontier(0, 1)]);
        assert_eq!(builder.drain_focus(&mut fixed, 32), 0);

        for link in 0..8u32 {
            let inner_memo = link;
            let outer_memo = link + 1;
            let context_id = link + 1;
            builder.add_fact(&ZipperFact::ProjectHole {
                context: context(context_id),
                memo: memo(outer_memo),
            });
            parent(&mut builder, inner_memo, context_id);
            parent(&mut builder, outer_memo, 0);
            let work = builder.drain_focus(&mut fixed, 32);
            assert!(work <= 4, "link {link} replayed historical work: {work}");
            builder.mark_frontier_relevant(&[frontier(0, 1)]);
            assert_eq!(builder.drain_focus(&mut fixed, 32), 0);
        }
    }

    #[test]
    fn persistent_focus_drops_residual_constructor_cycle_work_at_the_budget() {
        let mut fixed = FixedTreeMaterializer::new(1, 1, vec![schema(&[0], 0)]);
        fixed.add_exact(fixed_space(1), TypedExact::string(0, "leaf"));
        resolve_all(&mut fixed, &mut Vec::new());
        let leaf = fixed.candidates(fixed_space(1), 0).next().unwrap().0;

        let mut builder = PrefixOutputBuilder::new();
        builder.add_fact(&ZipperFact::ConstructHole {
            constructor: 0,
            context: context(1),
            memo: memo(0),
            hole_argument: 0,
            fixed_children: smallvec![],
        });
        parent(&mut builder, 0, 1);
        builder.notify_focus_candidate(fixed_space(1), leaf);
        builder.mark_frontier_relevant(&[frontier(0, 1)]);

        assert_eq!(builder.drain_focus(&mut fixed, 16), 16);
        // Residual expansion was deliberately dropped instead of becoming a
        // tax on every later lexeme.
        assert_eq!(builder.drain_focus(&mut fixed, 16), 0);
    }
}
