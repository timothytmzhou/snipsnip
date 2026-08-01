use std::hash::Hash;

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Event-driven insertion-only fixed-point scheduling.
///
/// A relation owner performs its representation-specific duplicate check and
/// enqueues an event only for a genuinely new fact. Closing the program pops
/// exactly those events; there is no scan over unrelated relations or rules.
/// The concrete program retains its own indexes so its event handler can jump
/// directly to the rule continuations affected by the new fact.
#[derive(Clone, Debug)]
pub(crate) struct DeltaEngine<Event> {
    pending: Vec<Event>,
    last_derived: usize,
}

impl<Event> Default for DeltaEngine<Event> {
    fn default() -> Self {
        Self {
            pending: Vec::new(),
            last_derived: 0,
        }
    }
}

impl<Event> DeltaEngine<Event> {
    /// Starts an externally visible update. Programs may enqueue many initial
    /// facts before calling `close`; only facts derived after this reset count
    /// toward `last_derived`.
    pub(crate) fn begin_update(&mut self) {
        debug_assert!(self.pending.is_empty());
        self.last_derived = 0;
    }

    /// Schedules one fact after its owning relation has established novelty.
    #[inline]
    pub(crate) fn enqueue_new(&mut self, event: Event) {
        self.last_derived = self.last_derived.saturating_add(1);
        self.pending.push(event);
    }

    pub(crate) fn last_derived(&self) -> usize {
        self.last_derived
    }

    /// Drains a program whose relations and indexes can be borrowed
    /// independently of this agenda.
    pub(crate) fn close(&mut self, mut dispatch: impl FnMut(Event, &mut Self)) {
        while let Some(event) = self.pending.pop() {
            dispatch(event, self);
        }
    }

    /// Drains a program to its least fixed point. `select` identifies the
    /// program's agenda and `dispatch` applies the rule continuations for one
    /// new fact. Facts derived by `dispatch` are appended to the active agenda
    /// before the next event, so the engine—not each client—owns the closure
    /// loop.
    pub(crate) fn close_program<State>(
        state: &mut State,
        select: impl for<'a> Fn(&'a mut State) -> &'a mut Self + Copy,
        mut dispatch: impl FnMut(&mut State, Event),
    ) {
        let mut active = std::mem::take(select(state));
        while let Some(event) = active.pending.pop() {
            dispatch(state, event);
            let newly_derived = select(state);
            active.pending.append(&mut newly_derived.pending);
            active.last_derived = active
                .last_derived
                .saturating_add(std::mem::take(&mut newly_derived.last_derived));
        }
        *select(state) = active;
    }
}

/// Persistent insertion-only propagation over a directed graph.
///
/// This is a reusable program on [`DeltaEngine`]. Facts have the form
/// `Fact(node, payload)` and the recursive rule is
///
/// ```text
/// Fact(destination, payload) :-
///     Fact(source, payload), Edge(source, destination).
/// ```
///
/// Both relations are indexed in both directions needed by incremental
/// updates: a new fact visits only outgoing edges of its node, while a new
/// edge visits only payloads already known at its source.
pub(crate) struct IncrementalReachability<Node, Payload>
where
    Node: Clone + Eq + Hash,
    Payload: Clone + Eq + Hash,
{
    engine: DeltaEngine<(Node, Payload)>,
    edges: HashSet<(Node, Node)>,
    outgoing: HashMap<Node, Vec<Node>>,
    facts: HashSet<(Node, Payload)>,
    payloads: HashMap<Node, Vec<Payload>>,
    closed_once: bool,
}

impl<Node, Payload> Default for IncrementalReachability<Node, Payload>
where
    Node: Clone + Eq + Hash,
    Payload: Clone + Eq + Hash,
{
    fn default() -> Self {
        Self {
            engine: DeltaEngine::default(),
            edges: HashSet::default(),
            outgoing: HashMap::default(),
            facts: HashSet::default(),
            payloads: HashMap::default(),
            closed_once: false,
        }
    }
}

impl<Node, Payload> IncrementalReachability<Node, Payload>
where
    Node: Clone + Eq + Hash,
    Payload: Clone + Eq + Hash,
{
    pub(crate) fn add_edge(&mut self, source: Node, destination: Node) {
        if !self.edges.insert((source.clone(), destination.clone())) {
            return;
        }
        self.outgoing
            .entry(source.clone())
            .or_default()
            .push(destination.clone());
        if self.closed_once {
            let existing = self.payloads.get(&source).cloned().unwrap_or_default();
            for payload in existing {
                self.insert_fact(destination.clone(), payload);
            }
        }
    }

    pub(crate) fn add_fact(&mut self, node: Node, payload: Payload) {
        self.insert_fact(node, payload);
    }

    /// Closes all facts and edges inserted since the previous call and returns
    /// exactly the facts that became visible during this closure.
    pub(crate) fn close(&mut self) -> Vec<(Node, Payload)> {
        let mut added = Vec::new();
        DeltaEngine::close_program(
            self,
            |flow| &mut flow.engine,
            |flow, (node, payload)| {
                added.push((node.clone(), payload.clone()));
                flow.propagate_fact(&node, &payload);
            },
        );
        self.closed_once = true;
        added
    }

    fn insert_fact(&mut self, node: Node, payload: Payload) {
        Self::insert_fact_into(
            &mut self.engine,
            &mut self.facts,
            &mut self.payloads,
            node,
            payload,
        );
    }

    fn propagate_fact(&mut self, node: &Node, payload: &Payload) {
        let Self {
            engine,
            outgoing,
            facts,
            payloads,
            ..
        } = self;
        let Some(destinations) = outgoing.get(node) else {
            return;
        };
        for destination in destinations {
            Self::insert_fact_into(
                engine,
                facts,
                payloads,
                destination.clone(),
                payload.clone(),
            );
        }
    }

    fn insert_fact_into(
        engine: &mut DeltaEngine<(Node, Payload)>,
        facts: &mut HashSet<(Node, Payload)>,
        payloads: &mut HashMap<Node, Vec<Payload>>,
        node: Node,
        payload: Payload,
    ) {
        if !facts.insert((node.clone(), payload.clone())) {
            return;
        }
        payloads
            .entry(node.clone())
            .or_default()
            .push(payload.clone());
        engine.enqueue_new((node, payload));
    }
}

#[cfg(test)]
mod tests {
    use super::IncrementalReachability;

    #[test]
    fn closes_cycles_once() {
        let mut flow = IncrementalReachability::default();
        flow.add_edge(0, 1);
        flow.add_edge(1, 2);
        flow.add_edge(2, 0);
        flow.add_fact(0, 'x');

        let mut facts = flow.close();
        facts.sort_unstable();
        assert_eq!(facts, [(0, 'x'), (1, 'x'), (2, 'x')]);
        assert!(flow.close().is_empty());
    }

    #[test]
    fn late_edges_catch_up_stable_facts() {
        let mut flow = IncrementalReachability::default();
        flow.add_fact(0, 7);
        assert_eq!(flow.close(), [(0, 7)]);

        flow.add_edge(0, 1);
        flow.add_edge(1, 2);
        let mut facts = flow.close();
        facts.sort_unstable();
        assert_eq!(facts, [(1, 7), (2, 7)]);
    }

    #[test]
    fn late_facts_use_stable_edges_and_duplicates_are_suppressed() {
        let mut flow = IncrementalReachability::default();
        flow.add_edge(0, 1);
        flow.add_edge(0, 1);
        assert!(flow.close().is_empty());

        flow.add_fact(0, 1);
        flow.add_fact(0, 1);
        let mut first = flow.close();
        first.sort_unstable();
        assert_eq!(first, [(0, 1), (1, 1)]);

        flow.add_fact(0, 2);
        let mut second = flow.close();
        second.sort_unstable();
        assert_eq!(second, [(0, 2), (1, 2)]);
    }

    #[test]
    fn shared_descendants_preserve_each_payload() {
        let mut flow = IncrementalReachability::default();
        flow.add_edge(0, 2);
        flow.add_edge(1, 2);
        flow.add_edge(2, 3);
        flow.add_fact(0, "left");
        flow.add_fact(1, "right");

        let mut facts = flow.close();
        facts.sort_unstable();
        assert_eq!(
            facts,
            [
                (0, "left"),
                (1, "right"),
                (2, "left"),
                (2, "right"),
                (3, "left"),
                (3, "right"),
            ]
        );
    }
}
