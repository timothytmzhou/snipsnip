# Streaming realizability: reference design and work plan

## Status and purpose

This document describes the intended design. It is a reference for upcoming
refactors, not a description of everything the current implementation already
does.

The monitor answers, after each complete lexeme, whether the current prefix has
a completion whose annotated parse produces an AST in the target Egglog
e-class:

- `Some(true)` means a concrete intersection witness is represented now.
- `Some(false)` means syntax is dead, or every syntactic completion has an AST
  covered by an e-class proved `Disjoint` from the target by the user's Egglog
  program.
- `None` means neither result has been proved.

The implementation must optimize latency for the common LL(1) case. Outside
the work performed by the PwZ derivative itself, a token should wake only the
relations and Egglog rules affected by that derivative. Ambiguity, a large
e-class merge, or a productive equality-saturation step may necessarily cause
more work; those costs must be proportional to newly relevant facts rather
than to all historical prefixes.

## Non-negotiable invariants

1. `paper_pwz` follows *Parsing with Zippers*. It owns the cyclic parse graph
   and current zippers. It has no lexer, semantic action, Egglog, or
   realizability logic.
2. The Egglog adapter owns exactly one normal `egglog::EGraph`. It contains no
   PwZ expression, memo, context, or zipper IDs and no Rust realizability
   relations.
3. The linking code is the only component allowed to inspect both PwZ and
   Egglog-facing values.
4. The user's Egglog program is authoritative. The monitor never invents a
   typing rule, equation, rewrite, `Disjoint` fact, or reverse application of a
   directed rewrite.
5. Incomplete lexer candidates never reach `Pwz::derive`.
6. A definite answer never depends on a work limit:
   - `Some(true)` has a represented witness;
   - `Some(false)` has a complete disjointness proof;
   - exhausting a budget produces `None`.
7. State has one owner. The parser graph is not copied by the linker, and
   Egglog constructor tables are not mirrored wholesale in Rust.
8. Rust relation updates, and safely indexable Egglog rewrites, are driven by
   new facts or new dependency edges. General Egglog rules may remain global,
   and an Egglog change with no precise public delta may require conservative
   invalidation.
9. Historical PwZ nodes and their relation rows are retained intentionally,
   but inactive history is not revisited by ordinary forward updates.

## Known gaps in the current tree

The current implementation does not yet satisfy the full design:

- the shared `DeltaEngine` that existed before the paper-PwZ rebuild was
  deleted;
- grammar productivity, nullability, FIRST, and FOLLOW now use independent
  repeated scans;
- positive realizability has a private relation store and work-list loop;
- unrealizability constructs and discards a temporary whole-zipper walk for
  each query;
- `egglog_backend.rs` imports neutral types from `realizability.rs`, while
  `realizability.rs` imports the backend;
- unfinished-child rewrite matching is currently decided inside the backend;
- Egglog change notifications are coarse enough to cause repeated constructor
  table scans and can wake inactive historical consumers.

The first four implementation phases correct the architecture. The final
phase removes avoidable local-saturation and inactive-history work.

## Intended module boundaries

```text
dataflow.rs                    (no project-domain dependencies)
paper_pwz.rs                   (no lexer, grammar analysis, or Egglog)
semantic.rs                    (neutral records only)
egglog_program.rs              -> Egglog AST
pwz_grammar.rs                 -> grammar, dataflow, paper_pwz, semantic
egglog_backend.rs              -> grammar, semantic, egglog_program, Egglog
realizability.rs               -> dataflow, paper_pwz, semantic, egglog_backend
monitor.rs                     -> all coordinating components
```

### `paper_pwz.rs`

Owns:

- permanent compiled grammar-node structure, with parser-private memo caches
  that may change;
- dynamically created parse expressions, memos, and contexts;
- the current list of zippers;
- the derivative implementation;
- an edit batch describing new graph structure.

Its operational interface remains small:

```rust
Pwz::new(grammar) -> Pwz<P>
Pwz::derive(token) -> Changes
Pwz::zippers() -> &[Zipper<P>]
```

The linker may read the ID-indexed maps. It must not ask PwZ to perform
semantic evaluation. A sequence context is an immutable snapshot: advancing
through the sequence creates another context rather than modifying the old
one.

### `dataflow.rs`

Owns the shared low-latency fixed-point mechanism used by grammar flow
analysis and by streaming realizability. It is not a dynamic Datalog parser.
The Rust program fixes the relation schemas and rule handlers at compile time.

The core type is deliberately small:

```rust
struct DeltaEngine<Event> {
    pending: Vec<Event>,
}

impl<Event> DeltaEngine<Event> {
    fn enqueue_new(&mut self, event: Event);
    fn close_program<State>(
        state: &mut State,
        agenda: fn(&mut State) -> &mut DeltaEngine<Event>,
        dispatch: impl FnMut(&mut State, Event),
    );
}
```

A typed relation performs its own duplicate check and compact indexing. It
enqueues an event only when a fact is new. The event handler directly invokes
the few rule continuations indexed for that relation. This preserves the
important optimization: the generic engine owns fixed-point scheduling, while
the client retains dense, domain-specific storage and joins.

Reusable programs such as `IncrementalReachability<Node, Payload>` may live in
the same module. They use the same rules for late updates:

- a new fact follows all stable outgoing edges;
- a new edge immediately catches up all stable facts at its source;
- duplicates do not enter the agenda.

### `semantic.rs`

Owns neutral types shared at the boundary, for example:

```rust
type SortId = usize;
type ConstructorId = usize;

struct TypedClass<C> { sort: SortId, class: C }
struct ConstructorSchema { inputs: Box<[SortId]>, output: SortId }
struct Application<C> { output: C, children: Box<[C]> }
type ClassValues<C> = SmallVec<[TypedClass<C>; 2]>;

enum SemanticAction {
    Construct { constructor: ConstructorId, arguments: Box<[usize]> },
    Project { position: usize },
}

struct SemanticSchema { /* production actions and constructors */ }
```

These types must not live in `realizability.rs`, because doing so makes the
Egglog adapter import the implementation it is supposed to be isolated from.
The exact module name is less important than the one-way dependency.

This module contains only records. It does not call the concrete backend.
`pwz_grammar` compiles CFG structure and semantic actions from a constructor
resolver supplied at initialization; it does not import Egglog.

### `egglog_backend.rs`

This is a grammar-configured semantic adapter around one normal e-graph, not a
second analysis engine. It may retain the constructor/sort and terminal/value
mapping established during initialization, which is why it can emit terminal
invalidations. It never receives the runtime PwZ graph.

Owns:

- `egglog::EGraph`;
- parsing and executing user Egglog commands;
- canonical e-class lookup and equality;
- constructor row lookup and insertion;
- the distinguished target binding;
- reads of the user-defined `Disjoint` relation;
- the Egglog scheduler used to run rules near a supplied set of e-classes;
- change notifications caused by Egglog work.

It does not own:

- PwZ IDs or graph nodes;
- `Produces`, `RealizableFor`, or negative relations;
- the current zipper;
- the decision that an unfinished child has been covered.

The current name `focus` should not cross this boundary because focus is PwZ
terminology. The scheduler receives only a set of relevant typed e-classes.
It does not know why they are relevant.

The intended local-saturation interface is:

```rust
fn reset_relevance(&mut self);
fn extend_relevance(&mut self, classes: &[TypedClass<ValueId>]) -> bool;
fn step_relevant_rules(&mut self) -> Result<RuleProgress, MonitorError>;
fn take_delta(&mut self) -> Result<EGraphDelta, MonitorError>;

fn existing_nullary(&self, name: &str) -> Option<TypedClass<ValueId>>;
fn add_nullary(
    &mut self,
    name: &str,
) -> Result<Option<TypedClass<ValueId>>, MonitorError>;

enum RuleProgress {
    Quiescent,
    More,
    BudgetExhausted,
}

struct ProgramUpdate {
    rewrites: Vec<RewriteShape>,
    partial_error: Option<MonitorError>,
}
```

`reset_relevance` resets only the scheduler's active relevance set; it does not
delete historical PwZ or relation state. It installs the target-derived roots
and closes those roots downward. The monitor supplies only classes obtained
from live zippers to `extend_relevance`.
`step_relevant_rules` performs one bounded internal batch. Filling that batch
while work remains returns `More`. `Quiescent` means the current relevant
schedule is closed. `BudgetExhausted` is reserved for exhaustion of a separate
per-query scheduler budget, which starts when `reset_relevance` begins the
query; it stops an unresolved query with `None` and must not masquerade as
quiescence.

Every mutating backend operation queues change topics. Only `take_delta`
drains them. Neither `step_relevant_rules` nor `run_commands` also returns a
delta, so a notification cannot be dropped or applied twice.

`EGraphDelta` exists solely so the Rust relations update from Egglog changes
without replaying PwZ history. Initially it may contain conservative keys:

```rust
enum EGraphChange {
    Target,
    Terminal(TerminalId),
    Constructor(ConstructorId),
    Disjoint,
    All,
}
```

The relation engine already indexes consumers by these keys. A later
optimization may report exact added constructor rows or affected canonical
classes when the Egglog API provides enough information. The interface must
not require a whole relation rebuild. `Disjoint` is its own topic because a
late fact or rule can change `None` to `Some(false)` without changing a grammar
constructor or the target. `All` is the conservative fallback when Egglog
reports that an update occurred but its public API does not identify the
affected merges or tables. It rechecks target, all bound terminals and grammar
constructors, and `Disjoint` without replaying PwZ history. While `Disjoint`
exists, any updated rule step which cannot report its exact relation delta must
at least mark `Disjoint` (or `All`), because equality can change canonical
endpoints without increasing the table size.

If the user defines `Disjoint`, the backend validates that it is a relation
with exactly two arguments of the target sort. A constructor or primitive
function with the same name is rejected. Queries check both argument orders,
so the user's facts need not be duplicated. Direct facts, facts derived by
ordinary rules, and equality changes which alter either canonical endpoint all
produce `Disjoint` or conservative `All` notifications. Any reflexive row after
canonicalization poisons the monitor as described below.

`ProgramUpdate` preserves the existing partial-command behavior explicitly:
the monitor synchronizes commands which were successfully applied, installs
only their returned rewrite descriptions in the linker, and then reports the
error. If an update makes `Disjoint(x, x)` true, the monitor enters an invalid
state and must not continue returning cached answers.

The monitor records that invalid state. Thereafter `realizability()` returns
`None`, and every mutating call returns the stored consistency error. This
avoids cloning the whole e-graph merely to make updates transactional and must
be covered by a query-after-error regression.

### Rewrite summaries for unfinished children

The current backend makes the prefix-specific decision through methods named
`guaranteed_outputs` and `materialize_guaranteed_output`. That is too much
realizability policy inside the Egglog adapter.

The clean split is:

1. The backend parses and resolves user commands because it speaks Egglog.
2. For a supported directed rewrite, it emits an Egglog-program description of
   that rewrite. It does not decide whether a zipper is covered or retain the
   description as semantic state.
3. The realizability code indexes those descriptions by constructor and
   decides whether every unfinished argument is covered.
4. If the result term is needed, the linker uses ordinary backend operations
   to look up or insert that exact term.

The Egglog-specific syntax inspection lives in a stateless
`egglog_program.rs` helper; it owns no e-graph or incremental state. The first
supported description can remain intentionally narrow:

```rust
struct RewriteShape {
    lhs_constructor: Box<str>,
    arguments: Box<[RewriteArgument]>,
    output: Box<str>, // nullary in the first implementation
}

enum RewriteArgument {
    Any,
    Nullary(Box<str>),
}
```

Only unconditional directed rewrites with a grammar-constructor call on the
left, distinct local variables or nullary patterns as arguments, and a
nullary result are summarized. An unsupported shape contributes no universal
fact; another supported rewrite or exact application may still prove the
answer. A birewrite is handled as two directed rewrites. Matching an existing
right-hand-side class may help schedule the forward rule, but never authorizes
running a one-way rewrite backward. Initialization and a late program update
return descriptions only for commands that were successfully installed. The
linker resolves the LHS name to a grammar `ConstructorId`, stores the
descriptions, and uses generic backend nullary lookup/insertion when a result
is demanded.

### `realizability.rs`

Owns the Rust relations and all joins between PwZ IDs and opaque Egglog class
IDs. It may read PwZ maps and use the neutral Egglog operations, but it does
not parse Egglog source or own an e-graph.

### `monitor.rs`

Is the only coordinator and the public API. It owns one lexer/runtime input,
one PwZ parser, one Egglog adapter, and one realizability state. It controls
the ordering of derivative edits, relation closure, materialization, local
Egglog steps, and final queries.

No second monitor, disequality engine, prefix evaluator, or copied parse forest
is introduced.

## Grammar flow analysis on the shared engine

`pwz_grammar` computes productivity, nullability, FIRST, FOLLOW, and SELECT
before constructing the paper PwZ graph. These analyses must return to the
shared `DeltaEngine`; the current repeated whole-production scans are a
regression.

- Productivity and nullability use an occurrence count for every production.
  Repeated occurrences are separate obligations: `A -> B B` decrements twice
  when `B` becomes known.
- FIRST and FOLLOW use `IncrementalReachability<NonterminalId, TerminalId>` or
  the equivalent dense program on `DeltaEngine`.
- SELECT is computed once from the closed nullable/FIRST/FOLLOW facts.
- Lexer terminals without a complete lexeme remain unproductive and must be
  included in the productivity calculation.

This is a useful independent client of the same engine: grammar nodes are
data, not new variables or new Datalog rules.

## Incremental positive relations

The maintained relations are:

```text
Produces(expression, class)
RealizableFor(memo-or-context, class)
Realizable(memo-or-context)
```

Their meanings are:

- `Produces(e, C)`: expression `e` can produce an AST represented by `C`.
- `RealizableFor(s, C)`: filling the hole at memo/context `s` with `C` can
  complete to the target class.
- `Realizable(s)`: `s` can complete to the target without depending on the
  hole value.

Each novel fact becomes one `DeltaEngine` event. The handlers are fixed Rust
code corresponding to the relation rules:

- a new `Produces` fact wakes only alternatives, sequences, and contexts that
  consume that expression;
- a new `RealizableFor(context, C)` crosses only parent edges into memos;
- a new `RealizableFor(memo, C)` wakes only contexts whose outer memo is that
  memo;
- `Realizable` follows the same context/memo edges without an e-class payload.

PwZ structural edits must catch up stable facts before the agenda closes:

- `NewExpression` and `NewContext` install their consumer indexes;
- `MemoParentAppended` copies already-known context facts across the new edge;
- `AlternativeChildAppended` copies already-known child outputs into the
  alternative;
- Egglog target, terminal, constructor, and rewrite-summary changes wake only
  their indexed consumers.

The derivative update is deliberately two-phase:

1. Register every structural edit in the returned `Changes` batch.
2. Drain the relation agenda to its fixed point.

This ensures that all parse alternatives discovered by one derivative are
present before any universal conclusion is published.

## Incremental unrealizability

The temporary whole-zipper walk in the current code must be replaced. It is
sound, but it repeats work on every `realizability()` call and is not the
desired streaming design.

### Stable parse nodes at derivative boundaries

PwZ may append several completed children to one fixed `Alt` result while a
single derivative is running. Once `derive` returns, that result represents
all alternatives finishing at that input position. A parse finishing at a
later position gets a different result expression. The same batching rule
applies to memo-parent edges created at one starting position.

This boundary must be documented and tested. If it cannot be guaranteed from
the paper transcription, `Changes` must include explicit sealing events. If a
later derivative can append to what was thought to be sealed, the append must
create a new versioned snapshot and current queries must stop referring to the
old version; an insertion-only universal fact must never be invalidated. A
universal fact must never be emitted for an unsealed child or parent list.

### Complete expression outputs

The negative side reuses `Produces`; it must not build a second store of
concrete terms. It adds one marker:

```text
OutputsComplete(expression)
```

`OutputsComplete(e)` means that every AST class which the fixed expression
`e` can produce is already present as `Produces(e, class)`. It is stronger
than having found one or more outputs. The marker is derived as follows:

- a consumed-token expression becomes complete only after all semantic values
  of that concrete token have been installed;
- a sealed alternative becomes complete when every child is complete;
- a projection becomes complete when its selected child is complete and all
  of that child's outputs have been forwarded;
- a constructor expression becomes complete when all selected children are
  complete, the complete finite product of their outputs has been considered,
  and every resulting application output has been inserted;
- an expression standing for unconsumed future syntax is not complete merely
  because some values of the same terminal or nonterminal have been seen.

An exceeded combination budget, a missing application which was not safely
materialized, or an unsupported rewrite prevents this marker. It never
produces a negative answer. Complete-output markers are published only after
the positive agenda for the whole derivative batch has closed. Later e-class
merges may identify outputs, but a sealed complete expression cannot acquire
a new unequal output.

### Outward safety and conjunction

The maintained outward proofs are:

```text
UnrealizableFor(memo-or-context, exact-class)
Unrealizable(memo-or-context)
```

- `UnrealizableFor(s, C)` means every syntactic continuation represented by
  `s`, when its hole contains `C`, produces a whole AST proved `Disjoint` from
  the target.
- `Unrealizable(s)` is the value-independent form used when the semantic action
  ignores the unfinished hole. This includes projecting a fixed sibling,
  constructing from arguments which omit the hole, and a supported user
  rewrite which fixes the outward result. It quantifies over syntactically
  possible hole values, not arbitrary unrelated e-classes.

At a top context, the only direct base case is an exact class:

```text
UnrealizableFor(Top, C) :- Egglog.Disjoint(C, Target).
```

`Unrealizable(Top)` is not a base case. A value-independent intermediate step
must first produce a concrete result which is disjoint from the target.

All branching is universal:

- an expression used by a continuation is covered only after
  `OutputsComplete(expression)` is known and every `Produces` value satisfies
  that continuation;
- a memo is covered only after every context in its sealed parent list is
  covered;
- an alternative is covered only after every child in its sealed child list
  is covered;
- a constructor is covered only after every semantic child combination and
  every resulting application is covered.

The implementation stores the number of unfinished requirements for each
expanded proof state. A newly proved requirement decrements only the states
which directly depend on it; siblings are not rescanned. The final expected
count is installed only after the derivative batch has registered and sealed
all new alternatives and memo parents.

For an unfinished child, no finite child enumeration is assumed. A context can
cross it only when a supported unconditional rewrite from the user's program
makes the result independent of that child. Missing applications, unsupported
conditional or repeated-variable rewrites, and exceeded budgets leave the
state unproved, so the public result remains `None`.

The zipper's focus is an inline `ExpressionNode`, not an `ExpressionId`, so it
is read directly rather than copied into `OutputsComplete`. A consumed-token
focus has a complete payload list; every payload class must satisfy the exact
memo proof. Any other unfinished inline focus starts with the
value-independent case and succeeds only if an outward supported rewrite makes
its eventual value irrelevant. The answer is `Some(false)` only when this
succeeds for every live zipper. An empty zipper set remains the separate exact
syntax-death case handled by PwZ.

### Context cycles

Universal reasoning over cyclic contexts is a greatest-fixed-point problem.
A plain insertion-only least-fixed-point rule is insufficient. For example, a
cycle with a disjoint finite exit is safe even though one obligation points
back to the fact being proved.

Use an on-demand finite obligation graph. Its stable nodes are expression
conjunctions and memo/context states paired with either an exact typed class or
the value-independent case. These are indexes into existing PwZ and relation
state, not copied contexts or concrete terms.

1. Expanding a state records every required successor. Expansion is marked
   complete only if all syntax branches and semantic combinations were
   covered.
2. Already-proved successors discharge their obligations immediately.
3. For the remaining demanded subgraph, compute strongly connected
   components. Expression-completeness components and outward-safety
   components close separately. Both require every node to be completely
   expanded and every outgoing obligation to be inside the component or
   already proved. An expression component must also reach a finite semantic
   output/base case; an outward component must reach a finite disjoint whole
   output at `Top`. These witness conditions prevent a closed cycle with no
   concrete exit from proving itself vacuously.
4. Emit the corresponding `UnrealizableFor`/`Unrealizable` facts through the
   shared `DeltaEngine` and wake their dependents.
5. Unknown states retain their indexed unsatisfied obligations and component
   metadata. A later `Disjoint` fact, constructor row, e-class merge, or
   supported rewrite wakes only the affected active unresolved states. PwZ
   edges from the current derivative are registered before sealing; no later
   derivative may append to that sealed node. Repeating a query with no changes
   performs no new graph expansion.

This preserves the current repeated-state treatment of recursive contexts
without rebuilding the graph per query. The state transition is monotone:
`Unknown -> Proved`. A proved state cannot become false because its PwZ node
was sealed, Egglog updates are monotone, and the backend rejects any merge
that would create `Disjoint(x, x)`.

Once an entire prefix is proved unrealizable, every longer prefix has a subset
of its completions. That negative answer may be latched, subject to the same
monotone-Egglog and `Disjoint` consistency requirements.

The publication order for one derivative is fixed:

1. PwZ derives the complete edit batch.
2. Register every new expression, context, alternative child, and memo parent.
3. Drain positive `Produces` and realizability events.
4. Seal the universal nodes touched by this batch and publish any newly valid
   `OutputsComplete` markers.
5. Drain ordinary universal events, then close affected cyclic components.
6. Query the current zippers.

This order is part of correctness, not an optimization.

## Local equality saturation

Local saturation is demand-driven work over the user's rules; it is not part
of PwZ and it does not define realizability facts itself.

After one complete-token derivative, `Monitor` performs:

1. Apply the entire PwZ edit batch and close the Rust relations.
2. Return `Some(false)` immediately if no zipper remains.
3. Return `Some(true)` immediately if the existing relations contain a
   witness.
4. Return `Some(false)` immediately if the maintained universal facts cover
   every live zipper.
5. Materialize only newly fixed semantic applications and exact applications
   required while walking outward from the current zippers.
6. Drain the resulting Egglog delta, close the Rust relations, and repeat the
   three cheap queries above.
7. Call `reset_relevance()`, then extend relevance only with parser-derived
   e-classes exposed by the current live zippers. The backend adds its own
   target-derived roots and closes the resulting set downward through existing
   e-nodes.
8. If still unknown, run one relevant rule batch, apply its delta, add any new
   relevant classes exposed by the updated intersection, and repeat.
9. Stop on a definite answer. An unresolved loop is quiescent only when the
   rule scheduler says `Quiescent`, materialization added nothing, relevance
   did not grow, and `take_delta()` was empty. `BudgetExhausted` returns
   `None`. No fixed number of equality-saturation rounds is part of the
   semantics.

The scheduler may select a directed rewrite match through its left root or an
already-existing right root, but the action is always the user's forward
union. General Egglog rules that cannot be safely localized remain global.

The backend currently scans all installed internal rules and may later rescan
all rows of a dirty constructor. These are implementation costs, not required
parts of the boundary. Optimize them by indexing rules by their top-level
function and, where Egglog permits, journaling exact selected roots, added
rows, and canonical-class changes. Preserve the conservative delta path for
general user rules.

Any match or combination cap is a query budget, not a proof rule. Hitting it
returns `RuleProgress::BudgetExhausted` or otherwise leaves the answer `None`;
it never silently declares local saturation complete.

## Retained history

Do not delete old contexts or old relation rows. The append-only maps avoid
cyclic ownership machinery, keep stable IDs, and leave useful groundwork for a
future undo operation.

Retention must not make current updates proportional to all prior prefixes.
Distinguish stored state from active state. Active means the complete transitive
dependency cone of every current zipper query, whether or not a proof has been
found. It includes unresolved memo/context obligations and every selected
expression or relation state which could contribute to either answer. It is
not limited to nodes which already have facts.

Maintain that cone without scanning history:

1. Treat current zippers as roots of the PwZ/relation dependency graph. The
   monitor keeps the old current-frontier keys only across the `derive` call,
   diffs them with the new exposed zippers, updates root counts, and then drops
   that temporary snapshot. The returned derivative edits identify edge
   changes; neither operation rediscovers historical nodes or duplicates PwZ
   state persistently.
2. Collapse reachable dependency cycles into components. On the resulting
   acyclic graph, store the number of active incoming components plus current
   root references.
3. A root or edge change propagates only when a component's count changes
   between zero and nonzero. If an appended edge closes a cycle, recompute
   components only in the affected region and preserve the aggregate active
   count.
4. Activation installs that component's consumers in current-only indexes;
   deactivation removes them from those indexes but leaves every PwZ node,
   relation fact, and historical edge stored.

Every event path uses the current-only indexes. This includes `Produces`
propagation, target/terminal/constructor/`Disjoint` notifications, supported
rewrite changes, and the conservative `EGraphChange::All` fallback. A shared
dependency stays active until its final active predecessor/root disappears.
Cycles are marked once per transition.

Local Egglog relevance likewise contains only the target-derived roots and
classes exposed by the current prefix, so inactive parse branches do not keep
scheduling rules.

Syntactic structure is sealed at derivative boundaries, and already published
positive or universal proof facts remain valid under accepted monotone Egglog
updates. An archived state which was not proved may be missing facts enabled by
later updates; that is harmless while it is inactive because no current query
uses it. Ordinary forward parsing can reactivate a shared grammar expression or
historical context, so activation—not only future undo—must catch its reachable
subgraph up before querying it. Each archived component stores the Egglog
version at which it was last closed. A stale component is rechecked
conservatively across its newly active cone, then records the current version.
A retained proved fact never needs retraction.

Undo itself is out of scope for this plan. Retaining IDs and facts is useful
but not sufficient: undo would also need prior zipper roots and careful
handling of parser position and mutable memo pointers.

## Implementation sequence

Each phase should be a separate reviewable commit and must leave the full test
suite passing.

### Phase 0: capture the behavioral and performance baseline

1. Finish the complete debug and release test suites on the current working
   implementation.
2. Run both Criterion benchmark groups and preserve the raw results; current
   historical timing numbers are not a baseline.
3. Record peak memory for a long LL(1) stream and a deeply nested TypeScript
   stream.
4. Add only the missing behavioral stress cases: a long prefix which remains
   `None`, many irrelevant rows of a monitored constructor, and the old deep
   grammar-flow cases.
5. Keep the temporary negative walk as a differential oracle until its
   incremental replacement is complete, then delete it rather than retaining
   two production implementations.

### Phase 1: restore the shared relation engine

1. Restore a reduced `dataflow.rs` based on the previous `DeltaEngine` and
   `IncrementalReachability` implementation.
2. Port productivity, nullability, FIRST, FOLLOW, and SELECT to it while
   preserving incomplete-lexeme productivity.
3. Replace `RealizabilityEngine`'s private `Vec<Event>` closure loop with
   `DeltaEngine<Event>`.
4. Keep the current compact relation tables and exact consumer indexes; do not
   replace them with boxed dynamic rules or generic tuple maps.

### Phase 2: make the Egglog boundary one-way

1. Move neutral IDs, typed classes, constructor schemas, applications, token
   values, and semantic actions into `semantic.rs`.
2. Move `EGraphChange` and `EGraphDelta` into `egglog_backend.rs`.
3. Remove every import from `egglog_backend.rs` to `realizability.rs`.
4. Rename `begin_focus`/`saturate_near`/`saturate_local` to the relevance API
   above.
5. Keep the local scheduler private and verify that it accepts only typed
   e-classes, never PwZ IDs.
6. Replace ambiguous `updated`/`more_rule_work` booleans with `RuleProgress`,
   and make `take_delta` the only delta-draining operation.

### Phase 3: move unfinished-child policy to the linker

1. Have the backend emit Egglog-program descriptions of supported installed
   rewrites.
2. Index those descriptions in the realizability state.
3. Replace backend prefix-specific guarantee queries with ordinary nullary
   lookup/insertion and constructor operations.
4. Preserve directed-rewrite, birewrite, late-rule, global-variable, and dead
   parse-branch regressions.

### Phase 4: incremental negative relations

1. State and test the derivative-batch sealing invariant.
2. Add `OutputsComplete` markers and outstanding-obligation counts for sealed
   alternatives, projections, and finite constructor combinations.
3. Add `UnrealizableFor` and `Unrealizable` relations to the shared agenda.
4. Add on-demand strongly connected component closure for cyclic context
   obligations, including the finite-`Top`-exit requirement.
5. Index unknown obligations by the Egglog or PwZ event that can discharge
   them, and persist unresolved component state across unchanged queries.
6. Enforce the batch publication order: structural edits, positive closure,
   sealing, universal closure, then query.
7. Delete the temporary whole-zipper negative walk once differential tests
   prove equivalent or better precision.

### Phase 5: remove avoidable local-saturation work

1. Index scheduled rules by top-level functions rather than iterating over all
   rules for each local step.
2. Avoid repeated full constructor-table scans for one new class. Prefer exact
   row or affected-class deltas when available.
3. Avoid rebuilding the downward relevance graph from all Egglog rows after
   each small change; maintain it incrementally or rebuild only dirty
   functions.
4. Remove lifetime-wide heuristic counters that can silently suppress newly
   relevant work. A configured budget must surface as
   `RuleProgress::BudgetExhausted` and `None`.
5. Maintain the active dependency components and incoming counts described
   above; keep historical PwZ and relation rows, but remove inactive consumers
   from every current event index.
6. Record the Egglog version at which archived relation state was last closed.
   Any ordinary forward activation catches up only that newly active cone;
   future undo can use the same mechanism.

## Correctness validation

### Shared engine and grammar flow

- duplicate facts and duplicate edges;
- a late edge catching up existing facts;
- a late fact following existing edges;
- cycles closing once;
- repeated dependencies such as `A -> B B`;
- unproductive cycles;
- nullable FIRST/FOLLOW cycles;
- a chain of at least 4,096 nonterminals;
- lexer terminals without complete lexemes.

### Positive streaming relations

- nullable and left-recursive grammars;
- cyclic contexts and cyclic e-classes;
- one expression supplying multiple constructor arguments;
- late target, terminal, constructor, and equality changes;
- a deep late rewrite chain reaching its relevant fixed point;
- no replay of prior PwZ changes after an Egglog update;
- an inactive historical context is not woken by a current-prefix Egglog
  update;
- reactivating archived state during ordinary forward parsing catches up that
  state before it is queried;
- an unresolved active dependency becomes provable after a late equality;
- deactivation stops event delivery, while a dependency shared by two roots
  remains active after only one root disappears;
- cyclic active marking terminates, and `EGraphChange::All` visits only active
  consumers.

### Incremental negative relations

- one disjoint completion cannot hide another possible completion;
- every child of a fixed ambiguous result is required;
- alternatives appended within one derivative are sealed before proof;
- memo parents appended within one derivative are sealed before proof;
- a recursive context with only disjoint finite exits is proved;
- a recursive context with one uncovered exit remains `None`;
- a closed recursive component with no finite `Top` output remains `None`;
- missing poison rewrites remain `None`;
- late `Disjoint` facts and late supported rewrites wake the current prefix;
- `Disjoint` derived by an ordinary Egglog rule wakes the current prefix;
- `Disjoint` facts work in either argument order, while a wrong signature or a
  same-named constructor is rejected;
- an Egglog global is never treated as a wildcard;
- conditional and repeated-variable rewrites remain unsupported and cannot
  prove a negative answer;
- a partial command batch summarizes only rewrites installed before its error;
- a dead parse branch is never materialized or used by a late rewrite;
- exceeding a combination or rule-work budget returns `None`;
- merging the endpoints of `Disjoint` is rejected;
- after a reflexive `Disjoint` update poisons the monitor, queries return
  `None` and later mutations return the stored error;
- repeating `realizability()` with no changes performs zero new negative graph
  work.

### Lexer and TypeScript behavior

- incomplete trailing lexemes do not call `derive` and are not highlighted;
- nested primitive property errors become unrealizable as soon as every
  completion is poisoned;
- primitive values are not callable while callable constructors remain
  realizable;
- removing the exact relevant TypeScript rule changes `Some(false)` to `None`,
  demonstrating that the user program, not Rust, supplies the type semantics;
- thousands of nested calls/operators preserve the expected result without a
  depth cutoff.

### Local scheduler behavior

- a constant-headed general rule remains eligible when it can affect a
  relevant class;
- finding a directed rewrite through an existing RHS class still runs only the
  user's forward rewrite;
- a birewrite behaves as two directed rewrites;
- duplicate rule names do not merge or skip distinct rules;
- an irrelevant or quiescent update schedules no historical rules.

Use a finite exhaustive oracle on small grammars to compare all three answers
where possible. Keep PwZ tests independent from Egglog tests so a linker bug
cannot be hidden by parser behavior.

## Performance validation

Deterministic counters should accompany timing benchmarks. They are compiled
only for tests/benchmarks or behind a disabled-by-default metrics feature, so
they add no production hot-path cost. For each update, record at least:

- new PwZ nodes and edges;
- new relation facts;
- relation events dispatched;
- constructor rows inspected;
- Egglog rules considered and matches selected;
- negative obligation states expanded;
- dependency components/edges inspected;
- active components entered/exited, active-index insertions/removals, and
  inactive events skipped;
- retained parser and relation rows.

Required geometric benchmarks:

1. vanilla PwZ versus the full monitor on a long LL(1) stream;
2. repeated `None` prefixes, to detect rebuilding the negative walk;
3. many historical contexts with a constant-size current frontier;
4. many rows of a monitored constructor, not merely unrelated Egglog junk;
5. irrelevant, relevant-no-result, and result-changing Egglog updates;
6. many irrelevant Egglog rules versus a small relevant set;
7. deep TypeScript expressions and nested calls;
8. long streams retaining all historical contexts, verifying that update time
   depends on active state rather than retained state.

The primary structural gate for the common LL(1) case is that relation work per
lexeme stays bounded by the newly returned PwZ edits, newly reported Egglog
changes, and the joins/facts those changes actually enable. Total time should
be linear in token count when the live frontier, dependency fan-out, and those
quantities are bounded. Do not publish old timing numbers after changing the
implementation; rerun release benchmarks and report recognition-only PwZ
separately from Egglog work.

Initial numeric gates are:

- vanilla PwZ must not regress materially;
- the shared-engine and boundary-only phases should show no statistically
  significant regression beyond 10% in repeated Criterion comparisons against
  the captured full-monitor and TypeScript baselines, unless raw event counts
  expose a justified tradeoff;
- a latched `Some(false)` query must be independent of prefix length;
- a repeated-`None` LL(1) stream with bounded active frontier and fan-out must
  have linear total work rather than a growing per-token graph walk;
- changing the active root set with a bounded dependency delta must not inspect
  retained inactive components;
- after Phase 5, a no-op or irrelevant Egglog update should be independent of
  retained prefix history when the Egglog API reports a sufficiently precise
  delta;
- after Phase 5, tenfold growth in irrelevant rows of a monitored constructor
  should not cause tenfold update latency when exact row/class deltas are
  available.

Relevant merge latency may grow with the number of newly enabled facts. Report
that fact count alongside the timing rather than labeling the work a constant
update.

## Final validation commands

Run these from the repository root before merging an implementation phase:

```sh
cargo fmt --check
cargo test --all --no-fail-fast
cargo test --release --all --no-fail-fast
cargo clippy --workspace --all-targets --all-features -- -D warnings
./scripts/build-web.sh
node ./scripts/smoke-web.mjs
cargo bench --bench live
cargo bench -p prefixspace-web --bench typescript
```

Record the toolchain versions and raw Criterion output when comparing a
performance phase. The benchmark is not replaced by a single hand-timed run.

## Definition of done

The design is implemented when:

- grammar analysis and all maintained Rust relations use the shared
  `DeltaEngine`;
- the Egglog adapter imports no PwZ or realizability implementation types;
- local scheduling accepts only relevant e-classes, reports `RuleProgress`, and
  exposes changes only through `take_delta`;
- both positive and negative answers are maintained incrementally;
- cyclic universal proofs use sound component closure;
- definite answers remain independent of work budgets;
- all correctness, differential, release, WebAssembly, and web-demo tests pass;
- release benchmarks demonstrate no historical replay on the LL(1) path;
- retained historical contexts and relations are not eagerly revisited by
  current-prefix Egglog updates.
