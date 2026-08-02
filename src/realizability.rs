//! Incremental intersection of a PwZ graph and an e-graph view.
//!
//! PwZ remains the sole owner of parse expressions and continuations. The
//! e-graph view remains the sole owner of e-nodes and equality. This module
//! stores only the two cross-system relations: `Produces` and
//! `RealizableFor` (whose value-independent case is `Realizable`).

use std::hash::Hash;

use rustc_hash::FxHashSet as HashSet;
use smallvec::SmallVec;

use crate::paper_pwz::{
    Context, ContextId, Edit, ExpressionId, ExpressionNode, MemoId, Pwz, Symbol, Zipper,
};

pub(crate) type SortId = usize;
pub(crate) type ConstructorId = usize;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TypedClass<C> {
    pub(crate) sort: SortId,
    pub(crate) class: C,
}

pub(crate) trait TokenClasses<C> {
    fn classes(&self) -> &[TypedClass<C>];
}

impl<C> TokenClasses<C> for Box<[TypedClass<C>]> {
    fn classes(&self) -> &[TypedClass<C>] {
        self
    }
}

impl<C> TokenClasses<C> for SmallVec<[TypedClass<C>; 2]> {
    fn classes(&self) -> &[TypedClass<C>] {
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SemanticAction {
    Construct {
        constructor: ConstructorId,
        /// Zero-based positions in the complete production RHS.
        arguments: Box<[usize]>,
    },
    Project {
        /// Zero-based position in the complete production RHS.
        position: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ConstructorSchema {
    pub(crate) inputs: Box<[SortId]>,
    pub(crate) output: SortId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Schema {
    /// Indexed by `Symbol::Grammar`'s original production index.
    pub(crate) actions: Box<[SemanticAction]>,
    pub(crate) constructors: Box<[ConstructorSchema]>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Enode<C> {
    pub(crate) output: C,
    pub(crate) children: Box<[C]>,
}

/// Read-only access to the current e-graph. Implementations own all e-node
/// storage and equality state; this engine never copies either.
pub(crate) trait EGraphView<C> {
    fn canonical(&self, value: TypedClass<C>) -> TypedClass<C>;
    fn targets(&self) -> &[TypedClass<C>];
    fn terminal_classes(&self, terminal: u32) -> &[TypedClass<C>];
    fn enodes(&self, constructor: ConstructorId) -> &[Enode<C>];
}

/// The two mutations used for focused equality saturation. Implementations
/// decide how terms are named and how relevance is represented.
pub(crate) trait EGraphWriter<C>: EGraphView<C> {
    type Error;

    fn construct(
        &mut self,
        constructor: ConstructorId,
        children: &[TypedClass<C>],
    ) -> Result<TypedClass<C>, Self::Error>;

    fn mark_relevant(&mut self, values: &[TypedClass<C>]) -> Result<(), Self::Error>;
}

/// The smallest notification which can make a previously closed product grow.
/// Equality changes are reported by re-emitting each affected target,
/// terminal value, and constructor row in canonical form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EGraphChange {
    Target,
    Terminal(u32),
    Constructor(ConstructorId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Site {
    Memo(MemoId),
    Context(ContextId),
}

impl Site {
    fn index(self) -> u64 {
        match self {
            Self::Memo(id) => u64::from(id.0) << 1,
            Self::Context(id) => (u64::from(id.0) << 1) | 1,
        }
    }
}

trait DenseKey: Copy + Eq + Hash {
    fn dense_index(self) -> u64;
}

impl DenseKey for ExpressionId {
    fn dense_index(self) -> u64 {
        u64::from(self.0)
    }
}

impl DenseKey for Site {
    fn dense_index(self) -> u64 {
        self.index()
    }
}

const NONE: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct Link<T> {
    value: T,
    next: u32,
}

struct Adjacency<T> {
    heads: Vec<u32>,
    links: Vec<Link<T>>,
}

impl<T> Default for Adjacency<T> {
    fn default() -> Self {
        Self {
            heads: Vec::new(),
            links: Vec::new(),
        }
    }
}

impl<T: Copy> Adjacency<T> {
    fn push(&mut self, key: u32, value: T) {
        let key = key as usize;
        if self.heads.len() <= key {
            self.heads.resize(key + 1, NONE);
        }
        let link = u32::try_from(self.links.len()).expect("adjacency capacity exceeded");
        self.links.push(Link {
            value,
            next: self.heads[key],
        });
        self.heads[key] = link;
    }

    fn values(&self, key: u32) -> SmallVec<[T; 4]> {
        let mut output = SmallVec::new();
        let mut link = self.heads.get(key as usize).copied().unwrap_or(NONE);
        while link != NONE {
            let entry = self.links[link as usize];
            output.push(entry.value);
            link = entry.next;
        }
        output
    }
}

#[derive(Clone, Copy)]
struct RelationEdge<C> {
    value: TypedClass<C>,
    next: u32,
}

/// One relation indexed in both directions. The reverse direction exists only
/// so an e-class merge touches facts mentioning the two merged classes.
struct Relation<C> {
    heads: Vec<u32>,
    edges: Vec<RelationEdge<C>>,
}

impl<C> Default for Relation<C> {
    fn default() -> Self {
        Self {
            heads: Vec::new(),
            edges: Vec::new(),
        }
    }
}

impl<C> Relation<C>
where
    C: Copy + Eq + Hash,
{
    fn insert(&mut self, key: impl DenseKey, value: TypedClass<C>) -> bool {
        let row = usize::try_from(key.dense_index()).expect("relation key exceeds usize");
        if self.heads.len() <= row {
            self.heads.resize(row + 1, NONE);
        }
        let mut edge = self.heads[row];
        while edge != NONE {
            let entry = self.edges[edge as usize];
            if entry.value == value {
                return false;
            }
            edge = entry.next;
        }
        let edge = u32::try_from(self.edges.len()).expect("relation capacity exceeded");
        self.edges.push(RelationEdge {
            value,
            next: self.heads[row],
        });
        self.heads[row] = edge;
        true
    }

    fn values(&self, key: impl DenseKey) -> SmallVec<[TypedClass<C>; 4]> {
        let mut output = SmallVec::new();
        let Ok(row) = usize::try_from(key.dense_index()) else {
            return output;
        };
        let mut edge = self.heads.get(row).copied().unwrap_or(NONE);
        while edge != NONE {
            let entry = self.edges[edge as usize];
            output.push(entry.value);
            edge = entry.next;
        }
        output
    }

    fn len(&self) -> usize {
        self.edges.len()
    }
}

#[derive(Clone, Copy)]
enum Consumer {
    Alternative(ExpressionId),
    Sequence(ExpressionId),
    Context(ContextId),
}

#[derive(Default)]
struct Indexes {
    consumers_by_expression: Adjacency<Consumer>,
    memos_by_context: Adjacency<MemoId>,
    contexts_by_outer_memo: Adjacency<ContextId>,
    consumers_by_constructor: Vec<Vec<Consumer>>,
    expressions_by_terminal: Vec<Vec<ExpressionId>>,
    top_contexts: Vec<ContextId>,
}

struct Closure<C> {
    produces: Relation<C>,
    realizable_for: Relation<C>,
    realizable: Vec<bool>,
}

impl<C> Default for Closure<C> {
    fn default() -> Self {
        Self {
            produces: Relation::default(),
            realizable_for: Relation::default(),
            realizable: Vec::new(),
        }
    }
}

#[derive(Clone, Copy)]
enum Event<C> {
    Produces(ExpressionId, TypedClass<C>),
    RealizableFor(Site, TypedClass<C>),
    Realizable(Site),
}

pub(crate) struct RealizabilityEngine<C> {
    schema: Schema,
    indexes: Indexes,
    closure: Closure<C>,
    agenda: Vec<Event<C>>,
}

impl<C> RealizabilityEngine<C>
where
    C: Copy + Eq + Hash,
{
    pub(crate) fn new<P>(schema: Schema, pwz: &Pwz<P>, egraph: &impl EGraphView<C>) -> Self
    where
        P: TokenClasses<C> + Clone,
    {
        let mut engine = Self {
            schema,
            indexes: Indexes::default(),
            closure: Closure::default(),
            agenda: Vec::new(),
        };
        for expression in pwz.expressions.keys().copied().collect::<Vec<_>>() {
            engine.index_expression(pwz, egraph, expression);
        }
        for context in pwz.contexts.keys().copied().collect::<Vec<_>>() {
            engine.index_context(pwz, egraph, context);
        }
        for (&memo, record) in &pwz.memos {
            for &context in &record.parents {
                engine.index_parent(memo, context);
            }
        }
        engine.seed_targets(egraph);
        engine.close(pwz, egraph);
        engine
    }

    /// Applies exactly the graph changes returned by one PwZ derivative.
    pub(crate) fn update_pwz<P>(
        &mut self,
        pwz: &Pwz<P>,
        edits: &[Edit],
        egraph: &impl EGraphView<C>,
    ) -> usize
    where
        P: TokenClasses<C> + Clone,
    {
        for &edit in edits {
            match edit {
                Edit::NewExpression(expression) => self.index_expression(pwz, egraph, expression),
                Edit::NewContext(context) => self.index_context(pwz, egraph, context),
                Edit::MemoParentAppended { memo, context } => self.index_parent(memo, context),
                Edit::AlternativeChildAppended { alternative, child } => {
                    self.index_alternative_child(alternative, child)
                }
            }
        }
        self.close(pwz, egraph)
    }

    /// Applies e-graph deltas without replaying PwZ history.
    pub(crate) fn update_egraph<P>(
        &mut self,
        pwz: &Pwz<P>,
        changes: &[EGraphChange],
        egraph: &impl EGraphView<C>,
    ) -> usize
    where
        P: TokenClasses<C> + Clone,
    {
        for &change in changes {
            match change {
                EGraphChange::Target => self.seed_targets(egraph),
                EGraphChange::Terminal(terminal) => {
                    let expressions = self
                        .indexes
                        .expressions_by_terminal
                        .get(terminal as usize)
                        .cloned()
                        .unwrap_or_default();
                    for expression in expressions {
                        self.recheck_expression(pwz, egraph, expression);
                    }
                }
                EGraphChange::Constructor(constructor) => {
                    let consumers = self
                        .indexes
                        .consumers_by_constructor
                        .get(constructor)
                        .cloned()
                        .unwrap_or_default();
                    for consumer in consumers {
                        self.recheck_consumer(pwz, egraph, consumer);
                    }
                }
            }
        }
        self.close(pwz, egraph)
    }

    /// Reads only the already-closed relations for the current zippers.
    pub(crate) fn is_realizable<P>(
        &self,
        zippers: &[Zipper<P>],
        egraph: &impl EGraphView<C>,
    ) -> bool
    where
        P: TokenClasses<C>,
    {
        zippers.iter().any(|zipper| {
            let site = Site::Memo(zipper.memo);
            if self.is_realizable_site(site) {
                return true;
            }
            self.focus_classes(&zipper.focus)
                .into_iter()
                .any(|value| self.has_realizable_for(egraph, site, value))
        })
    }

    pub(crate) fn fact_count(&self) -> usize {
        self.closure.produces.len()
            + self.closure.realizable_for.len()
            + self
                .closure
                .realizable
                .iter()
                .filter(|value| **value)
                .count()
    }

    /// Inserts only AST fragments already fixed by the consumed prefix. The
    /// resulting classes are ordinary `Produces` facts, so no second concrete
    /// tree store is needed.
    pub(crate) fn materialize_fixed<P, G>(
        &mut self,
        pwz: &Pwz<P>,
        expressions: &[ExpressionId],
        egraph: &mut G,
    ) -> Result<usize, G::Error>
    where
        P: TokenClasses<C> + Clone,
        G: EGraphWriter<C>,
    {
        let mut expressions = expressions
            .iter()
            .copied()
            .filter(|id| pwz.expressions[id].fixed)
            .collect::<Vec<_>>();
        expressions.sort_unstable_by_key(|id| id.0);

        let mut work = 0usize;
        for &expression in &expressions {
            self.materialize_expression(pwz, egraph, expression)?;
            work = work.saturating_add(self.close(pwz, egraph));
        }

        let mut relevant = Vec::new();
        for expression in expressions {
            relevant.extend(
                self.closure
                    .produces
                    .values(expression)
                    .into_iter()
                    .map(|value| egraph.canonical(value)),
            );
        }
        egraph.mark_relevant(&relevant)?;
        Ok(work)
    }

    /// Materializes the fixed path from each current focus outward until the
    /// first genuinely unfinished grammar child. This is transient zipper
    /// evaluation; PwZ remains the only owner of the contexts.
    pub(crate) fn materialize_focus<P, G>(
        &mut self,
        pwz: &Pwz<P>,
        egraph: &mut G,
    ) -> Result<usize, G::Error>
    where
        P: TokenClasses<C> + Clone,
        G: EGraphWriter<C>,
    {
        let mut agenda = Vec::new();
        for zipper in &pwz.zippers {
            let classes = self.focus_classes(&zipper.focus);
            if classes.is_empty() {
                agenda.push((zipper.memo, None));
            } else {
                agenda.extend(
                    classes
                        .into_iter()
                        .map(|value| (zipper.memo, Some(egraph.canonical(value)))),
                );
            }
        }

        let mut seen = HashSet::default();
        let mut relevant = Vec::new();
        let mut work = 0usize;
        while let Some((memo, value)) = agenda.pop() {
            let value = value.map(|value| egraph.canonical(value));
            if !seen.insert((memo, value)) {
                continue;
            }
            work = work.saturating_add(1);
            if let Some(value) = value {
                relevant.push(value);
            }
            for &context in &pwz.memos[&memo].parents {
                match pwz.contexts[&context].clone() {
                    Context::Top => {}
                    Context::Alt { memo } => agenda.push((memo, value)),
                    Context::Seq {
                        memo, symbol, left, ..
                    } => {
                        for output in self.materialize_context(egraph, &symbol, &left, value)? {
                            agenda.push((memo, Some(output)));
                        }
                    }
                }
            }
        }
        egraph.mark_relevant(&relevant)?;
        Ok(work)
    }

    fn materialize_context<P, G>(
        &self,
        egraph: &mut G,
        symbol: &Symbol<P>,
        left: &[ExpressionId],
        hole: Option<TypedClass<C>>,
    ) -> Result<Vec<TypedClass<C>>, G::Error>
    where
        G: EGraphWriter<C>,
    {
        let action = match symbol {
            Symbol::Bottom => SemanticAction::Project {
                position: left.len(),
            },
            Symbol::Grammar(action) => self.schema.actions[*action as usize].clone(),
            Symbol::Token(_) => return Ok(Vec::new()),
        };
        match action {
            SemanticAction::Project { position } => {
                if position < left.len() {
                    Ok(self.closure.produces.values(left[position]).to_vec())
                } else if position == left.len() {
                    Ok(hole.into_iter().collect())
                } else {
                    Ok(Vec::new())
                }
            }
            SemanticAction::Construct {
                constructor,
                arguments,
            } => {
                let schema = &self.schema.constructors[constructor];
                let mut choices = Vec::with_capacity(arguments.len());
                for (argument, position) in arguments.iter().copied().enumerate() {
                    let values = if position < left.len() {
                        self.closure.produces.values(left[position]).to_vec()
                    } else if position == left.len() {
                        hole.into_iter().collect()
                    } else {
                        Vec::new()
                    };
                    let mut row = Vec::new();
                    for value in values {
                        let value = egraph.canonical(value);
                        if value.sort == schema.inputs[argument] && !row.contains(&value) {
                            row.push(value);
                        }
                    }
                    if row.is_empty() {
                        return Ok(Vec::new());
                    }
                    choices.push(row);
                }
                let mut outputs = Vec::new();
                for children in products(&choices) {
                    outputs.push(egraph.construct(constructor, &children)?);
                }
                Ok(outputs)
            }
        }
    }

    fn materialize_expression<P, G>(
        &mut self,
        pwz: &Pwz<P>,
        egraph: &mut G,
        expression: ExpressionId,
    ) -> Result<(), G::Error>
    where
        P: TokenClasses<C> + Clone,
        G: EGraphWriter<C>,
    {
        let ExpressionNode::Seq {
            symbol: Symbol::Grammar(action),
            children,
        } = &pwz.expressions[&expression].node
        else {
            return Ok(());
        };
        let SemanticAction::Construct {
            constructor,
            arguments,
        } = self.schema.actions[*action as usize].clone()
        else {
            return Ok(());
        };
        let schema = self.schema.constructors[constructor].clone();
        let mut choices = Vec::with_capacity(arguments.len());
        for (argument, &position) in arguments.iter().enumerate() {
            let mut row = Vec::new();
            for value in self.closure.produces.values(children[position]) {
                let value = egraph.canonical(value);
                if value.sort == schema.inputs[argument] && !row.contains(&value) {
                    row.push(value);
                }
            }
            if row.is_empty() {
                return Ok(());
            }
            choices.push(row);
        }

        for children in products(&choices) {
            let output = egraph.construct(constructor, &children)?;
            self.insert_produces(expression, output);
        }
        Ok(())
    }

    fn close<P>(&mut self, pwz: &Pwz<P>, egraph: &impl EGraphView<C>) -> usize
    where
        P: TokenClasses<C> + Clone,
    {
        let mut work = 0usize;
        while let Some(event) = self.agenda.pop() {
            work = work.saturating_add(1);
            match event {
                Event::Produces(expression, value) => {
                    for consumer in self.indexes.consumers_by_expression.values(expression.0) {
                        match consumer {
                            Consumer::Alternative(alternative) => {
                                self.insert_produces(alternative, value)
                            }
                            _ => self.recheck_consumer(pwz, egraph, consumer),
                        }
                    }
                }
                Event::RealizableFor(site, value) => match site {
                    Site::Context(context) => {
                        for memo in self.indexes.memos_by_context.values(context.0) {
                            self.insert_realizable_for(Site::Memo(memo), value);
                        }
                    }
                    Site::Memo(memo) => {
                        for context in self.indexes.contexts_by_outer_memo.values(memo.0) {
                            self.recheck_context(pwz, egraph, context);
                        }
                    }
                },
                Event::Realizable(site) => match site {
                    Site::Context(context) => {
                        for memo in self.indexes.memos_by_context.values(context.0) {
                            self.insert_realizable(Site::Memo(memo));
                        }
                    }
                    Site::Memo(memo) => {
                        for context in self.indexes.contexts_by_outer_memo.values(memo.0) {
                            self.recheck_context(pwz, egraph, context);
                        }
                    }
                },
            }
        }
        work
    }

    fn index_expression<P>(
        &mut self,
        pwz: &Pwz<P>,
        egraph: &impl EGraphView<C>,
        expression: ExpressionId,
    ) where
        P: TokenClasses<C> + Clone,
    {
        match pwz.expressions[&expression].node.clone() {
            ExpressionNode::Tok(terminal) => {
                let terminal = terminal as usize;
                if self.indexes.expressions_by_terminal.len() <= terminal {
                    self.indexes
                        .expressions_by_terminal
                        .resize_with(terminal + 1, Vec::new);
                }
                self.indexes.expressions_by_terminal[terminal].push(expression);
            }
            ExpressionNode::Alt { children } => {
                for child in children {
                    self.index_alternative_child(expression, child);
                }
            }
            ExpressionNode::Seq { symbol, children } => {
                self.index_sequence(expression, &symbol, &children);
            }
        }
        self.recheck_expression(pwz, egraph, expression);
    }

    fn index_alternative_child(&mut self, alternative: ExpressionId, child: ExpressionId) {
        self.indexes
            .consumers_by_expression
            .push(child.0, Consumer::Alternative(alternative));
        for value in self.closure.produces.values(child) {
            self.insert_produces(alternative, value);
        }
    }

    fn index_sequence<P>(
        &mut self,
        expression: ExpressionId,
        symbol: &Symbol<P>,
        children: &[ExpressionId],
    ) {
        match symbol {
            Symbol::Token(_) => {}
            Symbol::Bottom => {
                if let Some(&child) = children.last() {
                    self.indexes
                        .consumers_by_expression
                        .push(child.0, Consumer::Sequence(expression));
                }
            }
            Symbol::Grammar(action) => match self.schema.actions[*action as usize].clone() {
                SemanticAction::Project { position } => self
                    .indexes
                    .consumers_by_expression
                    .push(children[position].0, Consumer::Sequence(expression)),
                SemanticAction::Construct {
                    constructor,
                    arguments,
                } => {
                    self.ensure_constructor(constructor);
                    self.indexes.consumers_by_constructor[constructor]
                        .push(Consumer::Sequence(expression));
                    for position in arguments.iter().copied() {
                        self.indexes
                            .consumers_by_expression
                            .push(children[position].0, Consumer::Sequence(expression));
                    }
                }
            },
        }
    }

    fn index_context<P>(&mut self, pwz: &Pwz<P>, egraph: &impl EGraphView<C>, context: ContextId)
    where
        P: TokenClasses<C> + Clone,
    {
        match pwz.contexts[&context].clone() {
            Context::Top => {
                self.indexes.top_contexts.push(context);
                for target in egraph.targets() {
                    self.insert_realizable_for(Site::Context(context), egraph.canonical(*target));
                }
            }
            Context::Alt { memo } => {
                self.indexes.contexts_by_outer_memo.push(memo.0, context);
            }
            Context::Seq {
                memo,
                symbol,
                left,
                right,
            } => {
                self.indexes.contexts_by_outer_memo.push(memo.0, context);
                self.index_context_action(context, &symbol, &left, &right);
            }
        }
        self.recheck_context(pwz, egraph, context);
    }

    fn index_context_action<P>(
        &mut self,
        context: ContextId,
        symbol: &Symbol<P>,
        left: &[ExpressionId],
        right: &[ExpressionId],
    ) {
        match symbol {
            Symbol::Token(_) => {}
            Symbol::Bottom => {
                if let Child::Fixed(expression) = context_child(left, right, 1) {
                    self.indexes
                        .consumers_by_expression
                        .push(expression.0, Consumer::Context(context));
                }
            }
            Symbol::Grammar(action) => match self.schema.actions[*action as usize].clone() {
                SemanticAction::Project { position } => {
                    if let Child::Fixed(expression) = context_child(left, right, position) {
                        self.indexes
                            .consumers_by_expression
                            .push(expression.0, Consumer::Context(context));
                    }
                }
                SemanticAction::Construct {
                    constructor,
                    arguments,
                } => {
                    self.ensure_constructor(constructor);
                    self.indexes.consumers_by_constructor[constructor]
                        .push(Consumer::Context(context));
                    for position in arguments.iter().copied() {
                        if let Child::Fixed(expression) = context_child(left, right, position) {
                            self.indexes
                                .consumers_by_expression
                                .push(expression.0, Consumer::Context(context));
                        }
                    }
                }
            },
        }
    }

    fn index_parent(&mut self, memo: MemoId, context: ContextId) {
        self.indexes.memos_by_context.push(context.0, memo);
        let context_site = Site::Context(context);
        if self.is_realizable_site(context_site) {
            self.insert_realizable(Site::Memo(memo));
        }
        for value in self.closure.realizable_for.values(context_site) {
            self.insert_realizable_for(Site::Memo(memo), value);
        }
    }

    fn seed_targets(&mut self, egraph: &impl EGraphView<C>) {
        for context in self.indexes.top_contexts.clone() {
            for target in egraph.targets() {
                self.insert_realizable_for(Site::Context(context), egraph.canonical(*target));
            }
        }
    }

    fn recheck_consumer<P>(&mut self, pwz: &Pwz<P>, egraph: &impl EGraphView<C>, consumer: Consumer)
    where
        P: TokenClasses<C> + Clone,
    {
        match consumer {
            Consumer::Alternative(expression) | Consumer::Sequence(expression) => {
                self.recheck_expression(pwz, egraph, expression)
            }
            Consumer::Context(context) => self.recheck_context(pwz, egraph, context),
        }
    }

    fn recheck_expression<P>(
        &mut self,
        pwz: &Pwz<P>,
        egraph: &impl EGraphView<C>,
        expression: ExpressionId,
    ) where
        P: TokenClasses<C> + Clone,
    {
        match pwz.expressions[&expression].node.clone() {
            ExpressionNode::Tok(terminal) => {
                for value in egraph.terminal_classes(terminal) {
                    self.insert_produces(expression, egraph.canonical(*value));
                }
            }
            ExpressionNode::Alt { children } => {
                for child in children {
                    for value in self.closure.produces.values(child) {
                        self.insert_produces(expression, value);
                    }
                }
            }
            ExpressionNode::Seq { symbol, children } => match symbol {
                Symbol::Token(token) => {
                    for value in token.payload.classes() {
                        self.insert_produces(expression, egraph.canonical(*value));
                    }
                }
                Symbol::Bottom => {
                    if let Some(&child) = children.last() {
                        for value in self.closure.produces.values(child) {
                            self.insert_produces(expression, value);
                        }
                    }
                }
                Symbol::Grammar(action) => match self.schema.actions[action as usize].clone() {
                    SemanticAction::Project { position } => {
                        for value in self.closure.produces.values(children[position]) {
                            self.insert_produces(expression, value);
                        }
                    }
                    SemanticAction::Construct {
                        constructor,
                        arguments,
                    } => {
                        let schema = self.schema.constructors[constructor].clone();
                        for enode in egraph.enodes(constructor) {
                            assert_eq!(schema.inputs.len(), enode.children.len());
                            if arguments.iter().enumerate().all(|(argument, position)| {
                                self.has_produces(
                                    egraph,
                                    children[*position],
                                    TypedClass {
                                        sort: schema.inputs[argument],
                                        class: enode.children[argument],
                                    },
                                )
                            }) {
                                self.insert_produces(
                                    expression,
                                    egraph.canonical(TypedClass {
                                        sort: schema.output,
                                        class: enode.output,
                                    }),
                                );
                            }
                        }
                    }
                },
            },
        }
    }

    fn recheck_context<P>(&mut self, pwz: &Pwz<P>, egraph: &impl EGraphView<C>, context: ContextId)
    where
        P: TokenClasses<C> + Clone,
    {
        let Context::Seq {
            memo,
            symbol,
            left,
            right,
        } = pwz.contexts[&context].clone()
        else {
            if let Context::Alt { memo } = pwz.contexts[&context] {
                let outer = Site::Memo(memo);
                if self.is_realizable_site(outer) {
                    self.insert_realizable(Site::Context(context));
                }
                for value in self.closure.realizable_for.values(outer) {
                    self.insert_realizable_for(Site::Context(context), value);
                }
            }
            return;
        };

        let outer = Site::Memo(memo);
        if self.is_realizable_site(outer) {
            self.insert_realizable(Site::Context(context));
        }
        let demands = self.closure.realizable_for.values(outer);
        match symbol {
            Symbol::Token(_) => {}
            Symbol::Bottom => {
                self.recheck_project_context(
                    egraph,
                    context,
                    context_child(&left, &right, 1),
                    &demands,
                );
            }
            Symbol::Grammar(action) => match self.schema.actions[action as usize].clone() {
                SemanticAction::Project { position } => self.recheck_project_context(
                    egraph,
                    context,
                    context_child(&left, &right, position),
                    &demands,
                ),
                SemanticAction::Construct {
                    constructor,
                    arguments,
                } => {
                    let schema = self.schema.constructors[constructor].clone();
                    for demand in demands {
                        if demand.sort != schema.output {
                            continue;
                        }
                        for enode in egraph.enodes(constructor) {
                            let output = egraph.canonical(TypedClass {
                                sort: schema.output,
                                class: enode.output,
                            });
                            if output != demand {
                                continue;
                            }
                            let mut hole = None;
                            let fixed_match =
                                arguments.iter().enumerate().all(|(argument, position)| {
                                    match context_child(&left, &right, *position) {
                                        Child::Hole => {
                                            hole = Some(argument);
                                            true
                                        }
                                        Child::Fixed(expression) => self.has_produces(
                                            egraph,
                                            expression,
                                            TypedClass {
                                                sort: schema.inputs[argument],
                                                class: enode.children[argument],
                                            },
                                        ),
                                    }
                                });
                            if !fixed_match {
                                continue;
                            }
                            if let Some(argument) = hole {
                                self.insert_realizable_for(
                                    Site::Context(context),
                                    egraph.canonical(TypedClass {
                                        sort: schema.inputs[argument],
                                        class: enode.children[argument],
                                    }),
                                );
                            } else {
                                self.insert_realizable(Site::Context(context));
                            }
                        }
                    }
                }
            },
        }
    }

    fn recheck_project_context(
        &mut self,
        egraph: &impl EGraphView<C>,
        context: ContextId,
        child: Child,
        demands: &[TypedClass<C>],
    ) {
        match child {
            Child::Hole => {
                for &demand in demands {
                    self.insert_realizable_for(Site::Context(context), demand);
                }
            }
            Child::Fixed(expression) => {
                if demands
                    .iter()
                    .any(|demand| self.has_produces(egraph, expression, *demand))
                {
                    self.insert_realizable(Site::Context(context));
                }
            }
        }
    }

    fn has_produces(
        &self,
        egraph: &impl EGraphView<C>,
        expression: ExpressionId,
        value: TypedClass<C>,
    ) -> bool {
        let value = egraph.canonical(value);
        self.closure
            .produces
            .values(expression)
            .into_iter()
            .any(|candidate| egraph.canonical(candidate) == value)
    }

    fn has_realizable_for(
        &self,
        egraph: &impl EGraphView<C>,
        site: Site,
        value: TypedClass<C>,
    ) -> bool {
        let value = egraph.canonical(value);
        self.closure
            .realizable_for
            .values(site)
            .into_iter()
            .any(|candidate| egraph.canonical(candidate) == value)
    }

    fn focus_classes<P: TokenClasses<C>>(
        &self,
        focus: &ExpressionNode<P>,
    ) -> SmallVec<[TypedClass<C>; 2]> {
        let mut classes = SmallVec::new();
        if let ExpressionNode::Seq {
            symbol: Symbol::Token(token),
            ..
        } = focus
        {
            classes.extend_from_slice(token.payload.classes());
        }
        classes
    }

    fn insert_produces(&mut self, expression: ExpressionId, value: TypedClass<C>) {
        if self.closure.produces.insert(expression, value) {
            self.agenda.push(Event::Produces(expression, value));
        }
    }

    fn insert_realizable_for(&mut self, site: Site, value: TypedClass<C>) {
        if self.closure.realizable_for.insert(site, value) {
            self.agenda.push(Event::RealizableFor(site, value));
        }
    }

    fn insert_realizable(&mut self, site: Site) {
        let index = usize::try_from(site.index()).expect("site ID exceeds usize");
        if self.closure.realizable.len() <= index {
            self.closure.realizable.resize(index + 1, false);
        }
        if !self.closure.realizable[index] {
            self.closure.realizable[index] = true;
            self.agenda.push(Event::Realizable(site));
        }
    }

    fn is_realizable_site(&self, site: Site) -> bool {
        self.closure
            .realizable
            .get(site.index() as usize)
            .copied()
            .unwrap_or(false)
    }

    fn ensure_constructor(&mut self, constructor: ConstructorId) {
        let len = constructor + 1;
        assert!(len <= self.schema.constructors.len(), "unknown constructor");
        if self.indexes.consumers_by_constructor.len() < len {
            self.indexes
                .consumers_by_constructor
                .resize_with(len, Vec::new);
        }
    }
}

#[derive(Clone, Copy)]
enum Child {
    Hole,
    Fixed(ExpressionId),
}

fn context_child(left: &[ExpressionId], right: &[ExpressionId], position: usize) -> Child {
    if position < left.len() {
        Child::Fixed(left[position])
    } else if position == left.len() {
        Child::Hole
    } else {
        Child::Fixed(right[position - left.len() - 1])
    }
}

fn products<C: Copy>(choices: &[Vec<TypedClass<C>>]) -> Vec<Vec<TypedClass<C>>> {
    let mut products = vec![Vec::new()];
    for choices in choices {
        let mut next = Vec::with_capacity(products.len().saturating_mul(choices.len()));
        for product in &products {
            for &choice in choices {
                let mut row = product.clone();
                row.push(choice);
                next.push(row);
            }
        }
        products = next;
    }
    products
}

#[cfg(test)]
mod tests {
    use super::{
        ConstructorSchema, EGraphChange, EGraphView, Enode, RealizabilityEngine, Schema,
        SemanticAction, TokenClasses, TypedClass,
    };
    use crate::paper_pwz::{
        ExpressionId as E, ExpressionNode, Grammar, Pwz, Symbol, Token, Zipper,
    };

    const SORT: usize = 0;
    const A: u32 = 0;
    const B: u32 = 1;

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Payload(Vec<TypedClass<u32>>);

    impl TokenClasses<u32> for Payload {
        fn classes(&self) -> &[TypedClass<u32>] {
            &self.0
        }
    }

    #[derive(Default)]
    struct TestEGraph {
        parents: Vec<u32>,
        targets: Vec<TypedClass<u32>>,
        terminals: Vec<Vec<TypedClass<u32>>>,
        constructors: Vec<Vec<Enode<u32>>>,
    }

    impl TestEGraph {
        fn ensure_class(&mut self, class: u32) {
            while self.parents.len() <= class as usize {
                self.parents.push(self.parents.len() as u32);
            }
        }

        fn find(&self, mut class: u32) -> u32 {
            while self.parents[class as usize] != class {
                class = self.parents[class as usize];
            }
            class
        }

        fn merge(&mut self, left: u32, right: u32) {
            self.ensure_class(left.max(right));
            let left = self.find(left);
            let right = self.find(right);
            self.parents[left as usize] = right;
        }

        fn target(&mut self, class: u32) {
            self.ensure_class(class);
            self.targets.push(typed(class));
        }

        fn terminal(&mut self, terminal: u32, class: u32) {
            self.ensure_class(class);
            if self.terminals.len() <= terminal as usize {
                self.terminals.resize_with(terminal as usize + 1, Vec::new);
            }
            self.terminals[terminal as usize].push(typed(class));
        }

        fn enode(&mut self, constructor: usize, output: u32, children: &[u32]) {
            self.ensure_class(children.iter().copied().chain([output]).max().unwrap());
            if self.constructors.len() <= constructor {
                self.constructors.resize_with(constructor + 1, Vec::new);
            }
            self.constructors[constructor].push(Enode {
                output,
                children: children.into(),
            });
        }
    }

    impl EGraphView<u32> for TestEGraph {
        fn canonical(&self, value: TypedClass<u32>) -> TypedClass<u32> {
            TypedClass {
                sort: value.sort,
                class: self.find(value.class),
            }
        }

        fn targets(&self) -> &[TypedClass<u32>] {
            &self.targets
        }

        fn terminal_classes(&self, terminal: u32) -> &[TypedClass<u32>] {
            self.terminals
                .get(terminal as usize)
                .map(Vec::as_slice)
                .unwrap_or_default()
        }

        fn enodes(&self, constructor: usize) -> &[Enode<u32>] {
            self.constructors
                .get(constructor)
                .map(Vec::as_slice)
                .unwrap_or_default()
        }
    }

    fn typed(class: u32) -> TypedClass<u32> {
        TypedClass { sort: SORT, class }
    }

    fn payload(classes: &[u32]) -> Payload {
        Payload(classes.iter().copied().map(typed).collect())
    }

    fn grammar(
        nodes: impl IntoIterator<Item = (u32, ExpressionNode<Payload>)>,
    ) -> Grammar<Payload> {
        Grammar {
            root: E(0),
            expressions: nodes.into_iter().map(|(id, node)| (E(id), node)).collect(),
            select: Default::default(),
        }
    }

    fn tok(terminal: u32) -> ExpressionNode<Payload> {
        ExpressionNode::Tok(terminal)
    }

    fn seq(action: u32, children: &[u32]) -> ExpressionNode<Payload> {
        ExpressionNode::Seq {
            symbol: Symbol::Grammar(action),
            children: children.iter().copied().map(E).collect(),
        }
    }

    fn schema(actions: Vec<SemanticAction>, constructors: Vec<ConstructorSchema>) -> Schema {
        Schema {
            actions: actions.into(),
            constructors: constructors.into(),
        }
    }

    fn constructor(inputs: usize) -> ConstructorSchema {
        ConstructorSchema {
            inputs: vec![SORT; inputs].into(),
            output: SORT,
        }
    }

    fn step(
        parser: &mut Pwz<Payload>,
        engine: &mut RealizabilityEngine<u32>,
        egraph: &TestEGraph,
        terminal: u32,
        values: &[u32],
    ) -> Vec<Zipper<Payload>> {
        let derivative = parser.derive(Token {
            terminal,
            payload: payload(values),
        });
        let zippers = derivative.zippers.to_vec();
        let edits = derivative.edits.to_vec();
        engine.update_pwz(parser, &edits, egraph);
        zippers
    }

    #[test]
    fn initial_prefix_uses_future_grammar_and_target_eclass() {
        let grammar = grammar([(0, seq(0, &[1, 2])), (1, tok(A)), (2, tok(B))]);
        let schema = schema(
            vec![SemanticAction::Construct {
                constructor: 0,
                arguments: vec![0, 1].into(),
            }],
            vec![constructor(2)],
        );
        let mut egraph = TestEGraph::default();
        egraph.terminal(A, 10);
        egraph.terminal(B, 20);
        egraph.enode(0, 30, &[10, 20]);
        egraph.target(30);

        let parser = Pwz::new(grammar);
        let engine = RealizabilityEngine::new(schema, &parser, &egraph);

        assert!(engine.is_realizable(&parser.zippers, &egraph));
    }

    #[test]
    fn late_target_and_terminal_facts_do_not_rebuild_the_parser_product() {
        let grammar = grammar([(0, seq(0, &[1])), (1, tok(A))]);
        let schema = schema(vec![SemanticAction::Project { position: 0 }], Vec::new());
        let mut egraph = TestEGraph::default();
        egraph.ensure_class(6);
        let parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);
        assert!(!engine.is_realizable(&parser.zippers, &egraph));

        egraph.target(6);
        egraph.terminal(A, 6);
        engine.update_egraph(
            &parser,
            &[EGraphChange::Target, EGraphChange::Terminal(A)],
            &egraph,
        );
        assert!(engine.is_realizable(&parser.zippers, &egraph));
    }

    #[test]
    fn exact_focus_and_late_merge_complete_the_cached_product() {
        let grammar = grammar([(0, seq(0, &[1, 2])), (1, tok(A)), (2, tok(B))]);
        let schema = schema(
            vec![SemanticAction::Construct {
                constructor: 0,
                arguments: vec![0, 1].into(),
            }],
            vec![constructor(2)],
        );
        let mut egraph = TestEGraph::default();
        egraph.terminal(B, 4);
        egraph.enode(0, 9, &[1, 4]);
        egraph.target(9);
        egraph.ensure_class(2);
        let mut parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);

        let zippers = step(&mut parser, &mut engine, &egraph, A, &[2]);
        assert!(!engine.is_realizable(&zippers, &egraph));

        // The matching row is re-emitted after rebuild. This case deliberately
        // chooses the already-produced class as the winner: merely copying
        // relation facts on union would do no work and miss the new match.
        egraph.merge(1, 2);
        engine.update_egraph(&parser, &[EGraphChange::Constructor(0)], &egraph);
        assert!(engine.is_realizable(&zippers, &egraph));
    }

    #[test]
    fn late_enode_uses_existing_parser_relations_without_replay() {
        let grammar = grammar([(0, seq(0, &[1, 2])), (1, tok(A)), (2, tok(B))]);
        let schema = schema(
            vec![SemanticAction::Construct {
                constructor: 0,
                arguments: vec![0, 1].into(),
            }],
            vec![constructor(2)],
        );
        let mut egraph = TestEGraph::default();
        egraph.terminal(B, 4);
        egraph.target(9);
        egraph.ensure_class(9);
        let mut parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);
        let zippers = step(&mut parser, &mut engine, &egraph, A, &[1]);
        assert!(!engine.is_realizable(&zippers, &egraph));

        egraph.enode(0, 9, &[1, 4]);
        let work = engine.update_egraph(&parser, &[EGraphChange::Constructor(0)], &egraph);
        assert!(work > 0);
        assert!(engine.is_realizable(&zippers, &egraph));
    }

    #[test]
    fn action_which_ignores_focus_uses_realizable_without_a_fake_value() {
        let grammar = grammar([(0, seq(0, &[1])), (1, tok(A))]);
        let schema = schema(
            vec![SemanticAction::Construct {
                constructor: 0,
                arguments: Vec::new().into(),
            }],
            vec![constructor(0)],
        );
        let mut egraph = TestEGraph::default();
        egraph.enode(0, 7, &[]);
        egraph.target(7);
        let mut parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);

        let zippers = step(&mut parser, &mut engine, &egraph, A, &[]);
        assert!(engine.is_realizable(&zippers, &egraph));
    }

    #[test]
    fn left_recursive_context_cycle_closes_once_and_keeps_projection() {
        // E ::= E A {$1} | B {$1}
        let grammar = grammar([
            (
                0,
                ExpressionNode::Alt {
                    children: vec![E(1), E(2)],
                },
            ),
            (1, seq(0, &[0, 3])),
            (2, seq(1, &[4])),
            (3, tok(A)),
            (4, tok(B)),
        ]);
        let schema = schema(
            vec![
                SemanticAction::Project { position: 0 },
                SemanticAction::Project { position: 0 },
            ],
            Vec::new(),
        );
        let mut egraph = TestEGraph::default();
        egraph.terminal(B, 5);
        egraph.target(5);
        let mut parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);

        let mut zippers = step(&mut parser, &mut engine, &egraph, B, &[5]);
        assert!(engine.is_realizable(&zippers, &egraph));
        for _ in 0..4 {
            zippers = step(&mut parser, &mut engine, &egraph, A, &[]);
            assert!(engine.is_realizable(&zippers, &egraph));
        }
        assert!(engine.fact_count() < 200);
    }

    #[test]
    fn absence_of_a_witness_remains_only_a_negative_positive_query() {
        let grammar = grammar([(0, seq(0, &[1])), (1, tok(A))]);
        let schema = schema(vec![SemanticAction::Project { position: 0 }], Vec::new());
        let mut egraph = TestEGraph::default();
        egraph.target(2);
        egraph.ensure_class(3);
        let mut parser = Pwz::new(grammar);
        let mut engine = RealizabilityEngine::new(schema, &parser, &egraph);
        let zippers = step(&mut parser, &mut engine, &egraph, A, &[3]);

        assert!(!engine.is_realizable(&zippers, &egraph));
    }
}
