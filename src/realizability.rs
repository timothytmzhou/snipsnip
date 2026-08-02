//! Incremental intersection of a PwZ graph and Egglog.
//!
//! PwZ remains the sole owner of parse expressions and continuations. The
//! Egglog adapter remains the sole owner of applications and equality. This module
//! stores only the two cross-system relations: `Produces` and
//! `RealizableFor` (whose value-independent case is `Realizable`).

use std::{hash::Hash, sync::Arc};

use rustc_hash::FxHashSet as HashSet;
use smallvec::SmallVec;

use crate::{
    egglog_backend::{EgglogBackend, ValueId},
    error::MonitorError,
    paper_pwz::{Change, Context, ContextId, ExpressionId, ExpressionNode, MemoId, Pwz, Symbol},
};

pub(crate) type SortId = usize;
pub(crate) type ConstructorId = usize;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TypedClass<C> {
    pub(crate) sort: SortId,
    pub(crate) class: C,
}

pub(crate) type TokenValues = SmallVec<[TypedClass<ValueId>; 2]>;

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
    pub(crate) constructors: Arc<[ConstructorSchema]>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Application<C> {
    pub(crate) output: C,
    pub(crate) children: Box<[C]>,
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

trait DenseKey: Copy {
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

pub(crate) struct RealizabilityEngine {
    schema: Schema,
    indexes: Indexes,
    closure: Closure<ValueId>,
    agenda: Vec<Event<ValueId>>,
}

impl RealizabilityEngine {
    pub(crate) fn new(schema: Schema, pwz: &Pwz<TokenValues>, egraph: &EgglogBackend) -> Self {
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
        engine.add_target(egraph);
        engine.close(pwz, egraph);
        engine
    }

    /// Applies exactly the graph changes returned by one PwZ derivative.
    pub(crate) fn update_pwz(
        &mut self,
        pwz: &Pwz<TokenValues>,
        changes: &[Change],
        egraph: &EgglogBackend,
    ) {
        for &change in changes {
            match change {
                Change::NewExpression(expression) => self.index_expression(pwz, egraph, expression),
                Change::NewContext(context) => self.index_context(pwz, egraph, context),
                Change::MemoParentAppended { memo, context } => self.index_parent(memo, context),
                Change::AlternativeChildAppended { alternative, child } => {
                    self.index_alternative_child(alternative, child)
                }
            }
        }
        self.close(pwz, egraph);
    }

    /// Applies e-graph deltas without replaying PwZ history.
    pub(crate) fn update_egraph(
        &mut self,
        pwz: &Pwz<TokenValues>,
        changes: &[EGraphChange],
        egraph: &EgglogBackend,
    ) {
        for &change in changes {
            match change {
                EGraphChange::Target => self.add_target(egraph),
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
        self.close(pwz, egraph);
    }

    /// Reads only the already-closed relations for the current zippers.
    pub(crate) fn is_realizable(&self, pwz: &Pwz<TokenValues>, egraph: &EgglogBackend) -> bool {
        let zippers = pwz.zippers();
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

    /// Inserts only AST fragments already fixed by the consumed prefix. The
    /// resulting classes are ordinary `Produces` facts, so no second concrete
    /// tree store is needed.
    pub(crate) fn materialize_fixed(
        &mut self,
        pwz: &Pwz<TokenValues>,
        expressions: &[ExpressionId],
        egraph: &mut EgglogBackend,
    ) -> Result<bool, MonitorError> {
        let mut expressions = expressions
            .iter()
            .copied()
            .filter(|id| pwz.expressions[id].fixed)
            .collect::<Vec<_>>();
        expressions.sort_unstable_by_key(|id| id.0);

        for &expression in &expressions {
            self.materialize_expression(pwz, egraph, expression)?;
            self.close(pwz, egraph);
        }

        let mut relevant = Vec::new();
        for expression in expressions {
            relevant.extend(self.closure.produces.values(expression));
        }
        egraph.saturate_near(&relevant)
    }

    /// Materializes the fixed path from each current focus outward until the
    /// first genuinely unfinished grammar child. This is transient zipper
    /// evaluation; PwZ remains the only owner of the contexts.
    pub(crate) fn materialize_focus(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &mut EgglogBackend,
    ) -> Result<bool, MonitorError> {
        let mut agenda = Vec::new();
        for zipper in pwz.zippers() {
            let classes = self.focus_classes(&zipper.focus);
            if classes.is_empty() {
                agenda.push((zipper.memo, None, SmallVec::<[ContextId; 8]>::new()));
            } else {
                agenda.extend(
                    classes
                        .into_iter()
                        .map(|value| (zipper.memo, Some(value), SmallVec::<[ContextId; 8]>::new())),
                );
            }
        }

        let mut seen = HashSet::default();
        let mut relevant = Vec::new();
        while let Some((memo, value, path)) = agenda.pop() {
            if !seen.insert((memo, value)) {
                continue;
            }
            if let Some(value) = value {
                relevant.push(value);
            }
            for &context in &pwz.memos[&memo].parents {
                // A cyclic context denotes arbitrarily many possible
                // completions. Materialization may follow each concrete
                // context once, but must not enumerate that infinite family.
                // The relation closure below handles the cycle symbolically.
                if path.contains(&context) {
                    continue;
                }
                let mut next_path = path.clone();
                next_path.push(context);
                match pwz.contexts[&context].clone() {
                    Context::Top => {}
                    Context::Alt { memo } => agenda.push((memo, value, next_path)),
                    Context::Seq {
                        memo,
                        symbol,
                        left,
                        right,
                    } => {
                        for expression in left.iter().chain(&right) {
                            if pwz.expressions[expression].fixed {
                                relevant.extend(self.closure.produces.values(*expression));
                            }
                        }
                        for output in
                            self.materialize_context(egraph, &symbol, &left, &right, value)?
                        {
                            agenda.push((memo, Some(output), next_path.clone()));
                        }
                    }
                }
            }
        }
        egraph.saturate_near(&relevant)
    }

    fn materialize_context(
        &self,
        egraph: &mut EgglogBackend,
        symbol: &Symbol<TokenValues>,
        left: &[ExpressionId],
        right: &[ExpressionId],
        hole: Option<TypedClass<ValueId>>,
    ) -> Result<Vec<TypedClass<ValueId>>, MonitorError> {
        let action = match symbol {
            Symbol::Bottom => SemanticAction::Project {
                position: left.len() + right.len(),
            },
            Symbol::Grammar(action) => self.schema.actions[*action as usize].clone(),
            Symbol::Token(_) => return Ok(Vec::new()),
        };
        match action {
            SemanticAction::Project { position } => {
                Ok(self.context_values(left, right, hole, position))
            }
            SemanticAction::Construct {
                constructor,
                arguments,
            } => {
                let schema = &self.schema.constructors[constructor];
                let mut choices = Vec::with_capacity(arguments.len());
                for (argument, position) in arguments.iter().copied().enumerate() {
                    let values = self.context_values(left, right, hole, position);
                    let mut row = Vec::new();
                    for value in values {
                        if value.sort == schema.inputs[argument]
                            && !row.iter().any(|known| egraph.equivalent(*known, value))
                        {
                            row.push(value);
                        }
                    }
                    if row.is_empty() {
                        return Ok(Vec::new());
                    }
                    choices.push(row);
                }

                // If the action depends on syntax to the right of the hole,
                // use only constructor rows already present in Egglog. Those
                // rows are concrete completions of the current prefix. When
                // every selected child is already fixed, construct the one
                // fixed AST fragment so user rewrites can see it immediately.
                if arguments.iter().any(|position| *position > left.len()) {
                    let mut outputs = Vec::new();
                    let mut applications = Vec::new();
                    egraph.for_each_application(constructor, |application| {
                        applications.push(application)
                    });
                    for application in applications {
                        if application.children.len() != choices.len()
                            || !application
                                .children
                                .iter()
                                .enumerate()
                                .all(|(argument, class)| {
                                    choices[argument].iter().any(|candidate| {
                                        egraph.equivalent(
                                            *candidate,
                                            TypedClass {
                                                sort: schema.inputs[argument],
                                                class: *class,
                                            },
                                        )
                                    })
                                })
                        {
                            continue;
                        }
                        outputs.push(TypedClass {
                            sort: schema.output,
                            class: application.output,
                        });
                    }
                    return Ok(outputs);
                }

                let mut outputs = Vec::new();
                for children in products(&choices) {
                    outputs.push(egraph.add_application(constructor, &children)?);
                }
                Ok(outputs)
            }
        }
    }

    fn context_values(
        &self,
        left: &[ExpressionId],
        right: &[ExpressionId],
        hole: Option<TypedClass<ValueId>>,
        position: usize,
    ) -> Vec<TypedClass<ValueId>> {
        if position < left.len() {
            self.closure.produces.values(left[position]).to_vec()
        } else if position == left.len() {
            hole.into_iter().collect()
        } else {
            right
                .get(position - left.len() - 1)
                .map(|expression| self.closure.produces.values(*expression).to_vec())
                .unwrap_or_default()
        }
    }

    fn materialize_expression(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &mut EgglogBackend,
        expression: ExpressionId,
    ) -> Result<(), MonitorError> {
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
                if value.sort == schema.inputs[argument]
                    && !row.iter().any(|known| egraph.equivalent(*known, value))
                {
                    row.push(value);
                }
            }
            if row.is_empty() {
                return Ok(());
            }
            choices.push(row);
        }

        for children in products(&choices) {
            let output = egraph.add_application(constructor, &children)?;
            self.insert_produces(expression, output);
        }
        Ok(())
    }

    fn close(&mut self, pwz: &Pwz<TokenValues>, egraph: &EgglogBackend) {
        while let Some(event) = self.agenda.pop() {
            match event {
                Event::Produces(expression, value) => {
                    for consumer in self.indexes.consumers_by_expression.values(expression.0) {
                        match consumer {
                            Consumer::Alternative(alternative) => {
                                self.insert_produces(alternative, value)
                            }
                            Consumer::Sequence(sequence) => self
                                .propagate_sequence_value(pwz, egraph, sequence, expression, value),
                            Consumer::Context(context) => self
                                .propagate_context_value(pwz, egraph, context, expression, value),
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
                            self.propagate_context_demand(pwz, egraph, context, value);
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
                            self.insert_realizable(Site::Context(context));
                        }
                    }
                },
            }
        }
    }

    fn index_expression(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        expression: ExpressionId,
    ) {
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

    fn index_context(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        context: ContextId,
    ) {
        match pwz.contexts[&context].clone() {
            Context::Top => {
                self.indexes.top_contexts.push(context);
                self.insert_realizable_for(Site::Context(context), egraph.target());
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
                if let Child::Fixed(expression) = bottom_child(left, right) {
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

    fn add_target(&mut self, egraph: &EgglogBackend) {
        for context in self.indexes.top_contexts.clone() {
            self.insert_realizable_for(Site::Context(context), egraph.target());
        }
    }

    fn recheck_consumer(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        consumer: Consumer,
    ) {
        match consumer {
            Consumer::Alternative(expression) | Consumer::Sequence(expression) => {
                self.recheck_expression(pwz, egraph, expression)
            }
            Consumer::Context(context) => self.recheck_context(pwz, egraph, context),
        }
    }

    /// Joins one newly produced child value with only the rules that consume
    /// that child. Rechecking the whole expression here would replay every old
    /// child value after each insertion and turn a linear e-graph delta into a
    /// cubic closure.
    fn propagate_sequence_value(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        sequence: ExpressionId,
        child: ExpressionId,
        value: TypedClass<ValueId>,
    ) {
        let ExpressionNode::Seq { symbol, children } = pwz.expressions[&sequence].node.clone()
        else {
            return;
        };
        match symbol {
            Symbol::Token(_) => {}
            Symbol::Bottom => {
                if children.last() == Some(&child) {
                    self.insert_produces(sequence, value);
                }
            }
            Symbol::Grammar(action) => match self.schema.actions[action as usize].clone() {
                SemanticAction::Project { position } => {
                    if children[position] == child {
                        self.insert_produces(sequence, value);
                    }
                }
                SemanticAction::Construct {
                    constructor,
                    arguments,
                } => {
                    let schema = self.schema.constructors[constructor].clone();
                    let mut applications = Vec::new();
                    egraph.for_each_application(constructor, |application| {
                        applications.push(application)
                    });
                    for changed_argument in
                        arguments
                            .iter()
                            .enumerate()
                            .filter_map(|(argument, &position)| {
                                (children[position] == child
                                    && value.sort == schema.inputs[argument])
                                    .then_some(argument)
                            })
                    {
                        for application in &applications {
                            let changed_child = TypedClass {
                                sort: schema.inputs[changed_argument],
                                class: application.children[changed_argument],
                            };
                            if !egraph.equivalent(changed_child, value) {
                                continue;
                            }
                            if !arguments.iter().enumerate().all(|(argument, position)| {
                                argument == changed_argument
                                    || self.has_produces(
                                        egraph,
                                        children[*position],
                                        TypedClass {
                                            sort: schema.inputs[argument],
                                            class: application.children[argument],
                                        },
                                    )
                            }) {
                                continue;
                            }
                            self.insert_produces(
                                sequence,
                                TypedClass {
                                    sort: schema.output,
                                    class: application.output,
                                },
                            );
                        }
                    }
                }
            },
        }
    }

    fn propagate_context_value(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        context: ContextId,
        expression: ExpressionId,
        value: TypedClass<ValueId>,
    ) {
        let Context::Seq {
            memo,
            symbol,
            left,
            right,
        } = pwz.contexts[&context].clone()
        else {
            return;
        };
        let demands = self.closure.realizable_for.values(Site::Memo(memo));
        match symbol {
            Symbol::Token(_) => {}
            Symbol::Bottom => {
                if matches!(bottom_child(&left, &right), Child::Fixed(id) if id == expression)
                    && demands
                        .iter()
                        .any(|demand| egraph.equivalent(*demand, value))
                {
                    self.insert_realizable(Site::Context(context));
                }
            }
            Symbol::Grammar(action) => match self.schema.actions[action as usize].clone() {
                SemanticAction::Project { position } => {
                    if matches!(context_child(&left, &right, position), Child::Fixed(id) if id == expression)
                        && demands
                            .iter()
                            .any(|demand| egraph.equivalent(*demand, value))
                    {
                        self.insert_realizable(Site::Context(context));
                    }
                }
                SemanticAction::Construct {
                    constructor,
                    arguments,
                } => {
                    for argument in
                        arguments
                            .iter()
                            .enumerate()
                            .filter_map(|(argument, position)| {
                                matches!(
                                    context_child(&left, &right, *position),
                                    Child::Fixed(id) if id == expression
                                )
                                .then_some(argument)
                            })
                    {
                        for &demand in &demands {
                            self.propagate_construct_context(
                                egraph,
                                context,
                                constructor,
                                &arguments,
                                &left,
                                &right,
                                demand,
                                Some((argument, value)),
                            );
                        }
                    }
                }
            },
        }
    }

    fn propagate_context_demand(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        context: ContextId,
        demand: TypedClass<ValueId>,
    ) {
        match pwz.contexts[&context].clone() {
            Context::Top => {}
            Context::Alt { .. } => {
                self.insert_realizable_for(Site::Context(context), demand);
            }
            Context::Seq {
                symbol,
                left,
                right,
                ..
            } => match symbol {
                Symbol::Token(_) => {}
                Symbol::Bottom => self.propagate_project_context_demand(
                    egraph,
                    context,
                    bottom_child(&left, &right),
                    demand,
                ),
                Symbol::Grammar(action) => match self.schema.actions[action as usize].clone() {
                    SemanticAction::Project { position } => self.propagate_project_context_demand(
                        egraph,
                        context,
                        context_child(&left, &right, position),
                        demand,
                    ),
                    SemanticAction::Construct {
                        constructor,
                        arguments,
                    } => self.propagate_construct_context(
                        egraph,
                        context,
                        constructor,
                        &arguments,
                        &left,
                        &right,
                        demand,
                        None,
                    ),
                },
            },
        }
    }

    fn propagate_project_context_demand(
        &mut self,
        egraph: &EgglogBackend,
        context: ContextId,
        child: Child,
        demand: TypedClass<ValueId>,
    ) {
        match child {
            Child::Hole => self.insert_realizable_for(Site::Context(context), demand),
            Child::Fixed(expression) => {
                if self.has_produces(egraph, expression, demand) {
                    self.insert_realizable(Site::Context(context));
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn propagate_construct_context(
        &mut self,
        egraph: &EgglogBackend,
        context: ContextId,
        constructor: ConstructorId,
        arguments: &[usize],
        left: &[ExpressionId],
        right: &[ExpressionId],
        demand: TypedClass<ValueId>,
        changed: Option<(usize, TypedClass<ValueId>)>,
    ) {
        let schema = self.schema.constructors[constructor].clone();
        if demand.sort != schema.output {
            return;
        }
        let mut applications = Vec::new();
        egraph.for_each_application(constructor, |application| applications.push(application));
        for application in applications {
            let output = TypedClass {
                sort: schema.output,
                class: application.output,
            };
            if !egraph.equivalent(output, demand) {
                continue;
            }
            if let Some((argument, value)) = changed {
                let child = TypedClass {
                    sort: schema.inputs[argument],
                    class: application.children[argument],
                };
                if !egraph.equivalent(child, value) {
                    continue;
                }
            }
            let mut hole = None;
            let fixed_match = arguments.iter().enumerate().all(|(argument, position)| {
                match context_child(left, right, *position) {
                    Child::Hole => {
                        hole = Some(argument);
                        true
                    }
                    Child::Fixed(expression) => {
                        changed.is_some_and(|(changed_argument, _)| changed_argument == argument)
                            || self.has_produces(
                                egraph,
                                expression,
                                TypedClass {
                                    sort: schema.inputs[argument],
                                    class: application.children[argument],
                                },
                            )
                    }
                }
            });
            if !fixed_match {
                continue;
            }
            if let Some(argument) = hole {
                self.insert_realizable_for(
                    Site::Context(context),
                    TypedClass {
                        sort: schema.inputs[argument],
                        class: application.children[argument],
                    },
                );
            } else {
                self.insert_realizable(Site::Context(context));
            }
        }
    }

    fn recheck_expression(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        expression: ExpressionId,
    ) {
        match pwz.expressions[&expression].node.clone() {
            ExpressionNode::Tok(terminal) => {
                egraph.for_each_terminal_value(terminal, |value| {
                    self.insert_produces(expression, value)
                });
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
                    for value in &token.payload {
                        self.insert_produces(expression, *value);
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
                        let mut applications = Vec::new();
                        egraph.for_each_application(constructor, |application| {
                            applications.push(application)
                        });
                        for application in applications {
                            assert_eq!(schema.inputs.len(), application.children.len());
                            if arguments.iter().enumerate().all(|(argument, position)| {
                                self.has_produces(
                                    egraph,
                                    children[*position],
                                    TypedClass {
                                        sort: schema.inputs[argument],
                                        class: application.children[argument],
                                    },
                                )
                            }) {
                                self.insert_produces(
                                    expression,
                                    TypedClass {
                                        sort: schema.output,
                                        class: application.output,
                                    },
                                );
                            }
                        }
                    }
                },
            },
        }
    }

    fn recheck_context(
        &mut self,
        pwz: &Pwz<TokenValues>,
        egraph: &EgglogBackend,
        context: ContextId,
    ) {
        let memo = match pwz.contexts[&context] {
            Context::Top => return,
            Context::Alt { memo } | Context::Seq { memo, .. } => memo,
        };
        let outer = Site::Memo(memo);
        if self.is_realizable_site(outer) {
            self.insert_realizable(Site::Context(context));
            return;
        }
        for demand in self.closure.realizable_for.values(outer) {
            self.propagate_context_demand(pwz, egraph, context, demand);
        }
    }

    fn has_produces(
        &self,
        egraph: &EgglogBackend,
        expression: ExpressionId,
        value: TypedClass<ValueId>,
    ) -> bool {
        self.closure
            .produces
            .values(expression)
            .into_iter()
            .any(|candidate| egraph.equivalent(candidate, value))
    }

    fn has_realizable_for(
        &self,
        egraph: &EgglogBackend,
        site: Site,
        value: TypedClass<ValueId>,
    ) -> bool {
        self.closure
            .realizable_for
            .values(site)
            .into_iter()
            .any(|candidate| egraph.equivalent(candidate, value))
    }

    fn focus_classes(
        &self,
        focus: &ExpressionNode<TokenValues>,
    ) -> SmallVec<[TypedClass<ValueId>; 2]> {
        let mut classes = SmallVec::new();
        if let ExpressionNode::Seq {
            symbol: Symbol::Token(token),
            ..
        } = focus
        {
            classes.extend_from_slice(&token.payload);
        }
        classes
    }

    fn insert_produces(&mut self, expression: ExpressionId, value: TypedClass<ValueId>) {
        if self.closure.produces.insert(expression, value) {
            self.agenda.push(Event::Produces(expression, value));
        }
    }

    fn insert_realizable_for(&mut self, site: Site, value: TypedClass<ValueId>) {
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

fn bottom_child(left: &[ExpressionId], right: &[ExpressionId]) -> Child {
    debug_assert_eq!(left.len() + right.len() + 1, 2);
    context_child(left, right, left.len() + right.len())
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
