# Live algorithm and correctness proof

## 1. Problem at a snapshot

Let \(G\) be a CFG over terminal alphabet \(T\). A constructor action is

\[
A\to x_1\cdots x_m
\quad\triangleright\quad f(a_1,\ldots,a_k),
\qquad 1\le a_1<\cdots<a_k\le m.
\]

The implementation also supports a projection action `$a`, which returns the
semantic value of \(x_a\) without adding a constructor. A selected terminal
denotes its complete lexeme as an egglog `String` or `i64`; unselected RHS
positions do not affect the result. Ambiguous grammars are interpreted as a
set of parses.

At time \(\tau\), let \(\equiv_\tau\) be the equality represented by the current
egglog e-graph and let \(r_\tau\) be the current canonical value of the
distinguished equality-sorted binding. For a word \(w\) of already-delimited
`(terminal, complete-lexeme)` events, define

\[
Q_\tau(w)\iff
\exists u,t.\;
 yield(t)=wu\land h(t)\equiv_\tau r_\tau .
\]

Thus \(Q_\tau(w)\) says that the current prefix has some syntactic completion
whose AST is in the current target class. `intersection_is_empty()` returns
\(\neg Q_\tau(w)\) for compatibility. The stronger `realizability()` query is
three-valued:

\[
\begin{array}{ll}
\texttt{Some(true)}  & \text{a witness establishes }Q_\tau(w),\\
\texttt{Some(false)} & \text{syntax death or disjointness proves no completion can work},\\
\texttt{None}        & \text{neither result is proved.}
\end{array}
\]

In particular, failure to find a current equality witness is not itself a
proof of `Some(false)`.
This token-stream model is deliberate. A Lex specification validates and
values individual selected lexemes, and `push_complete_text` tokenizes text
already supplied, but the existential suffix does not model cross-token
maximal-munch interactions in an unknown raw character suffix.

Both dimensions change online:

- a lexeme update changes \(w\) to \(wa\);
- a monotone egglog update grows the e-graph and may merge classes while \(w\)
  remains unchanged.

The second operation is why a product compiled once at startup is
insufficient. Rebuilding that product after every equality-saturation step
would unnecessarily replay work proportional to the whole prefix.

## 2. Persistent components

The live monitor retains these monotone databases:

1. a value-producing PwZ representation of all semantic spaces and zipper
   continuations discovered while parsing;
2. a target-directed projection of relevant e-graph rows;
3. a local least-fixed-point relation joining the first two components;
4. private bindings for finite, already-parsed semantic trees;
5. an append-only index of zipper facts used for bounded reconstruction of the
   current prefix's concrete output roots;
6. captured positive disjointness facts for the configured target sort.

Only the current PwZ frontier and its bounded output-enumeration result are
replaced after each lexeme. Historical facts and private bindings remain useful
because a later e-class merge can make an old continuation relevant. The
answer always queries only the current frontier, so retaining old facts cannot
make an old prefix become current again.

Before streaming, the parser removes syntactically unproductive productions.
For example, \(U\to U\) without a finite base contributes no semantic space.
This guarantees that every full nonterminal space used for a pending sibling
has a finite syntactic completion.

## 3. Target-directed e-graph delta

For each semantic sort \(s\), write \(R_s(q)\) for target reachability. Equality
sorts use e-class values. Primitive `String` and `i64` sorts use a domain
relation \(D_s(v)\). The private egglog rules add the initial fact

\[
R_{s_r}(r_\tau).
\]

For every constructor used by a grammar action, with schema

\[
f:s_1\times\cdots\times s_k\to s_0,
\]

the rules match a target-reachable e-node and derive

\[
R_{s_0}(q_0)\land q_0=f(q_1,\ldots,q_k)
\Longrightarrow
\bigwedge_i demand_{s_i}(q_i),
\]

where `demand` is \(R\) for an equality sort and \(D\) for a primitive sort.
A capture primitive exports the row

\[
E_f(q_0;q_1,\ldots,q_k)
\]

to Rust. Primitive-domain captures export each demanded `String`, and the
numeric value plus canonical spelling of each demanded `i64`.

These rules do not serialize the full e-graph. They follow only paths from the
target through constructor schemas which can occur in source ASTs. Egglog's
seminaive timestamps and rebuild processing cause later saturation to export
newly enabled rows. A merge can also create a newly canonicalized row even
when its underlying e-node existed before; such a row is a real delta because
it can enable a new join.

The private projection rules run during monitor construction and after
`run_egglog`. They may also run after a lexeme push when that derivative has
enabled the focused e-graph path—for example because managed rewrites or a
disjointness theory are installed. On the positive-only fast path, a lexeme
push still avoids egglog rule execution.

### Target-export lemma

**Lemma 1.** At a private-ruleset fixed point, every finite, grammar-shaped AST
represented in the target class has a finite tree of captured \(E_f\) rows
rooted at \(r_\tau\), with all selected primitive leaves present in their
domain relations. Conversely, assembling captured rows from the target starting class
uses genuine e-nodes in the corresponding e-classes.

**Proof.** For the forward direction, inspect the finite AST from the root.
Its root e-node is in the target e-class, so the matching constructor rule
fires. It captures that row and demands each child. Repeat by structural
induction on equality-sorted children; primitive children are captured by the
domain rule. Every constructor in this AST occurs in a grammar action and
therefore has a private rule. For the reverse direction, each captured row was
matched against an actual egglog constructor application whose output was
already demanded. Following those rows from the target therefore constructs a
term represented by the target class. Cyclic e-classes cause no problem:
only finite AST witnesses are used. ∎

### Managed equality saturation

`add_managed_rewrites` owns a persistent private rule set and alternates it
with the target projection above. Let \(S_s(q)\) be a private
saturation-demand relation. The distinguished target and newly materialized
fixed-prefix bindings are marked in it, and relevance is projected through
equality-sorted children of every declared e-graph function whose output has
an equality sort. This includes context constructors which occur in neither
the grammar nor a rewrite; otherwise a child merge under such a context could
be missed. Function and constructor declarations added by later updates are
tracked and receive projection rules before the answer is refreshed.

Every managed direction (l\to r) runs forward only with the indexed body guard
(S(l)). A `rewrite` contributes one direction; a `birewrite` is normalized to
two directions, (l\to r) and (r\to l), with its conditions preserved on both.
Duplicate directions are installed only once. After a union, canonicalization
carries (S) to the merged class and projection exposes nested redexes. Managed
directions, saturation demand, and target export are stepped to a joint fixed
point. Saturation demand is not exported to the Rust product.

For symmetric rules, this restriction reproduces any finite unrestricted
`birewrite` derivation connecting either starting class to a term. Traverse its
equality steps starting at the target or a fixed-prefix class. At a rewrite step,
the direction needed by the traversal is installed and its LHS is demanded,
so it constructs and merges the next term. At a congruence step, projection
for that declared function demands the child class containing the next redex,
whether or not the function appears in the grammar or rewrite text. Induction
on the finite derivation therefore reproduces it inside the demanded basin.
Conversely, every guarded match is a match of an original direction.

For an ordinary directed rule, the managed semantics is intentionally
focus-rooted: an LHS outside the area marked by the target or fixed prefix is not
inspected merely because its RHS might eventually connect back to that area.
Installed rules are persistent, so a later parser or e-graph update which
makes that LHS focused activates it without replaying the lexeme stream.

Term-generating systems need not terminate. Explicit managed-saturation
methods permit 1,024 joint rounds by default;
`add_managed_rewrites_with_round_limit`,
`run_egglog_with_managed_saturation_round_limit`, and
`continue_managed_saturation` make interruption and resumption explicit.
This is a round limit, not a work bound: a single egglog round may apply many
matches and allocate many e-nodes. Exhausting the limit returns a typed error
only after captured rows and local relations have been synchronized with the
sound partial e-graph state. A lexeme push performs at most 64 automatic joint
rounds when focused execution is enabled. Reaching that automatic allowance
keeps the partial state sound and prevents the incomplete saturation alone
from justifying a negative answer. As with the explicit limit, this bounds
rounds rather than matches, allocation, time, or memory within one round.

## 4. PwZ semantic spaces

The value-producing PwZ parser allocates a compact semantic-space ID \(P\) for
completed fragments. It emits monotone facts of four forms:

- `Alias(P,C)`: \(P\) includes everything in \(C\);
- `Apply_f(P;P_1,...,P_k)`: \(P\) includes constructor applications whose
  selected children come from \(P_1,\ldots,P_k\);
- `TokenAny(P,t)`: \(P\) includes any complete lexeme emitted as terminal \(t\);
- `TokenExact(P,t,l)`: \(P\) is the already-consumed terminal \(t\) with exact
  lexeme \(l\).

Full terminal and nonterminal spaces are allocated once. Newly completed
ambiguous results are unioned with aliases. Constructor applications and exact
tokens are hash-consed, and ordinary aliases are duplicate-suppressed. The
first alias out of a freshly allocated ambiguity union takes a shorter path
which does not populate the general alias-deduplication table. If the same
completion is later rediscovered, one semantically redundant alias may
therefore be recorded. This does not change the set-valued Horn closure.
When productive SELECT sets prove a predictive choice, an unambiguous
completion instead reuses its incoming semantic space directly and allocates
neither the union nor its alias. These facts denote finite semantic values of
complete source fragments; call that language \(L_s(P)\) at sort \(s\).

The local realizability engine materializes the target-directed restriction of
the relation

\[
\operatorname{Produces}_s(P,q)\quad\text{meaning}\quad q\in L_s(P).
\]

Only values in the captured target-directed universe need rows; the abstract
relation itself has the membership meaning above.

It is the least relation closed under these rules:

\[
\frac{Alias(P,C)\quad \operatorname{Produces}_s(C,q)}
{\operatorname{Produces}_s(P,q)}
\]

and

\[
\frac{
 Apply_f(P;P_1,\ldots,P_k)\quad
 E_f(q_0;q_1,\ldots,q_k)\quad
 \bigwedge_i \operatorname{Produces}_{s_i}(P_i,q_i)
}{\operatorname{Produces}_{s_0}(P,q_0)}.
\]

For `TokenExact`, the rule compares the lexeme's `String` or parsed `i64`
value with the captured primitive value. For a `String` `TokenAny`, it asks
whether the captured string is one complete instance of that terminal. An
`i64` can have noncanonical spellings such as `01`, `+1`, or `-0`; a finite
product-DFA cycle search decides whether *some* decimal spelling of the value
is emitted as the terminal. Only demanded primitive values need to be
enumerated.

### Space-production lemma

**Lemma 2.** For every captured target-reachable value \(q\),

\[
\operatorname{Produces}_s(P,q)\iff q\in L_s(P).
\]

**Proof.** Soundness is induction on the Horn derivation of `Produces`. Alias is
language inclusion, constructor rows combine exactly the selected children of
the annotated action, and token rules use exactly the terminal's complete
lexical value. Completeness is induction on a finite derivation of a value in
\(L_s(P)\). Its final space fact is an alias, constructor application, or token
fact. Lemma 1 supplies the required constructor/domain row, and the induction
hypothesis supplies each child production fact. Taking the least fixed point
excludes unsupported cycles on both sides. ∎

## 5. Persistent zipper continuations

Eagerly applying every pending context to every frontier value would copy a
linear AST spine at every prefix. Instead, PwZ records its immutable memo and
context graph. Let the continuation relations mean:

- \(\operatorname{RealizableFor}^M_s(m,q)\) means that completing memo \(m\)
  with value \(q\) can reach the target through one of its recorded parent
  contexts;
- \(\operatorname{RealizableFor}^C_s(c,q)\) means that plugging \(q\) into
  context \(c\) can reach the target;
- \(\operatorname{Realizable}^M(m)\) and \(\operatorname{Realizable}^C(c)\)
  record a finite target-realizing continuation witness whose action erases,
  and therefore does not inspect, the semantic value at this hole. Its syntax
  must still complete. This is neither existential over `RealizableFor` facts
  nor inferred merely because every currently materialized value has a typed
  witness.

The top context is \(c_0\), and the backward closure starts with

\[
\operatorname{RealizableFor}^C_{s_r}(c_0,r_\tau).
\]

PwZ emits the following continuation facts as it traverses alternatives and
production sequences.

### Structural rules

`Parent(m,c)` records a memo evaluated under a context:

\[
\operatorname{RealizableFor}^C_s(c,q)
\Rightarrow \operatorname{RealizableFor}^M_s(m,q),
\qquad \operatorname{Realizable}^C(c)
\Rightarrow \operatorname{Realizable}^M(m).
\]

`Alternative(c,m)` records a child alternative context whose result completes
memo \(m\):

\[
\operatorname{RealizableFor}^M_s(m,q)
\Rightarrow \operatorname{RealizableFor}^C_s(c,q),
\qquad \operatorname{Realizable}^M(m)
\Rightarrow \operatorname{Realizable}^C(c).
\]

Each production-sequence context emits exactly one of the action-specific
facts below; there is no standalone `Sequence` zipper fact. Every such fact
also carries the common value-independent implication

\[
\operatorname{Realizable}^M(m)\Rightarrow \operatorname{Realizable}^C(c).
\]

All pending siblings represented by a sequence context use productive full
spaces, so this value-independent case still has a finite syntactic completion.

### Constructor and projection rules

Suppose the current RHS hole supplies constructor argument \(h\). PwZ records
`ConstructHole_f(c,m,h;P_j for j != h)`, using completed spaces for past
siblings and full spaces for future siblings. Its inverse-image rule is

\[
\frac{
 \operatorname{RealizableFor}^M_{s_0}(m,q_0)\quad
 E_f(q_0;q_1,\ldots,q_k)\quad
 \bigwedge_{j\ne h}\operatorname{Produces}_{s_j}(P_j,q_j)
}{\operatorname{RealizableFor}^C_{s_h}(c,q_h)}.
\]

If the current syntactic child is not selected by the action, PwZ records
`ConstructIgnored_f(c,m;P_1,...,P_k)`. Once all selected children can produce
one target-realizing e-node, the hole is value-independent:

\[
\frac{
 \operatorname{RealizableFor}^M_{s_0}(m,q_0)\quad
 E_f(q_0;q_1,\ldots,q_k)\quad
 \bigwedge_j \operatorname{Produces}_{s_j}(P_j,q_j)
}{\operatorname{Realizable}^C(c)}.
\]

For a projection action, `ProjectHole(c,m)` gives

\[
\operatorname{RealizableFor}^M_s(m,q)
\Rightarrow \operatorname{RealizableFor}^C_s(c,q).
\]

If the projected child is a fixed sibling space \(P\),
`ProjectFixed(c,m,P)` gives

\[
\operatorname{RealizableFor}^M_s(m,q)
\land \operatorname{Produces}_s(P,q)
\Rightarrow \operatorname{Realizable}^C(c).
\]

These are positive Horn rules. The implementation indexes their premises by
sort, space, memo, context, and constructor and enqueues a conclusion only on
its first insertion.

### Continuation lemma

**Lemma 3.** For a memo or context owner \(o\) and a finite captured value
\(q\), its recorded PwZ continuation can reach the target with \(q\) exactly
when

\[
\operatorname{Realizable}(o)
\quad\lor\quad
\operatorname{RealizableFor}_s(o,q).
\]

The first disjunct specifically has a value-erasing witness; it is not an
existential or universal summary of the second relation.

**Proof.** Consider one finite path from a memo through its parent context to
the top. `Parent` and `Alternative` preserve the supplied semantic value.
For a sequence, the action either selects the current child, selects a fixed
sibling, or ignores the current child. The constructor and projection rules
above are exactly those three inverse images; Lemma 2 supplies precisely the
possible fixed-sibling values. An outer value-independent fact propagates
through an `Alternative` or through the action-specific fact for a sequence
context, because only syntactic completion remains relevant. Thus structural
induction on the context path proves soundness.

Conversely, take a finite completed parse continuing from the hole to the
start. Reading its context path from the top downward chooses one of the same
rules at every alternative and production. Its fixed siblings give the
`Produces`
premises by Lemma 2 and its root constructor gives the \(E_f\) premise by
Lemma 1, deriving the required `RealizableFor` or `Realizable` fact. Recursive and
ambiguous contexts are handled by the least fixed point: every derived fact
still has a finite witness, while all finite witnesses eventually fire. ∎

## 6. Fixed trees and focused prefix saturation

The static spaces allocated for grammar nonterminals and terminals may denote
infinite languages and are never turned into concrete egglog terms. Every
later exact-token, constructor-application, and alias space, however, denotes
already-parsed finite candidates. The fixed-tree materializer consumes those
space deltas and interns a private binding for each concrete candidate.

A binding stores only one primitive leaf or one constructor whose children are
earlier binding IDs. Thus a deep parsed tree is represented as a DAG of
constant-depth requests; no push copies its whole AST spine. Aliases attach an
existing binding to another space without reinserting the term. Equality of
returned egglog values suppresses duplicate candidates before a parent
constructor cross-product is extended.

The current zipper can contain an action result which has not yet appeared as
a completed space. Two consumers therefore follow the immutable zipper facts:

- a persistent focus worklist retains already-seen `(memo/context, binding)`
  facts and wakes only when a frontier pair, parent edge, context, or fixed
  candidate is new;
- a fresh bounded snapshot pass is used only when every current semantic root
  must be enumerated for a universal disjointness proof.

Both use the same transformations:

- `Parent`, `Alternative`, and `ProjectHole` carry the current binding outward;
- `ProjectFixed` replaces it with every binding of the selected fixed space;
- `ConstructHole` constructs candidates with the current binding in the hole;
- `ConstructIgnored` constructs candidates entirely from its recorded spaces.

The snapshot pass is complete only if every reachable selected value is concrete, every
candidate combination is visited, no reachable zipper cycle is present, and
the 2,048-step work allowance is not exhausted. An unrestricted future space
is represented internally as unknown. If an action selects that value, or it
reaches the root, completeness is cleared. This is deliberately conservative:
an incomplete pass may still provide useful focus terms, but it cannot support
a universal negative conclusion.

New completed and zipper-constructed terms are inserted into private egglog
bindings once. Their equality-sorted classes are marked in the same focus relation used
by managed rewrites. Historical identity chains are not walked again: a late
parent or fixed candidate catches up only the retained payloads at its indexed
memo or context. Residual work from a term-generating context cycle is dropped
at the focus-work limit; already derived terms remain sound.

When new terms or relevance facts make local closure dirty, the monitor
alternates the installed managed directions, focus projection, generated
free-constructor rules, and target projection. The free
rules require both compared constructor outputs to be in private free-focus
relations, which mark the target and fixed terms and project relevance into
free-sort children. Thus unrelated e-graph components do not form a global
disjointness cross-product. This happens automatically after a lexeme when any
focused facility is enabled. Zipper-root propagation and universal snapshot
reconstruction are deferred until the exact positive product is empty. A
reachable zipper cycle makes the finite universal snapshot incomplete, so
that pass returns immediately rather than spending the rest of its bound on
roots which cannot justify a negative answer. The ordinary positive-only
monitor retains its smaller no-egglog push path.

## 7. Positive disjointness and the three-way result

A configured disjointness relation has schema

\[
Disjoint:s_r\times s_r\to Unit.
\]

It is positive evidence supplied and maintained inside egglog. The private
projection captures relevant rows in either orientation and checks the
invariant `Disjoint(x, x)` by panic. Rust never derives a negative fact from
the absence of an equality or relation row.

The extension `(free S Disjoint)` expands before the egglog program is run. It
declares the relation and ordinary rules for:

- symmetry;
- different constructors of `S` being disjoint;
- equal free constructors merging their equality-sorted fields;
- disjoint recursive fields, or unequal primitive fields, making equal-headed
  constructor terms disjoint;
- failure if a disjoint pair becomes equal.

The generated theory marks a mutually recursive free family complete only
when every constructor field is primitive or belongs to another complete free
sort.

There are three independent ways to justify the result:

1. The positive `Produces`/`RealizableFor` closure finds one frontier witness.
   This yields `Some(true)` even if a bounded saturation attempt did not reach
   a fixed point.
2. An empty parser frontier proves that no suffix can repair the prefix. This
   yields `Some(false)` permanently.
3. If bounded zipper reconstruction is complete and nonempty, and every
   reconstructed root has an explicit `Disjoint(root, target)` row, every
   syntactic completion is excluded and the result is `Some(false)`.

For a complete free-constructor family, a structural shortcut is also sound:
once the target class has a constructor representative and all constructors
used by the semantic grammar belong to that family, constructor
no-confusion, injectivity, and primitive inequality make equality exhaustive.
After focused saturation is complete, failure of the exact positive product
then proves disjointness of every completion.

Every other state yields `None`. This includes an opaque or open selected
value, a reachable zipper cycle, exhausted output work, incomplete local
saturation when the structural shortcut is needed, or simply a missing
disjointness row. `None` is therefore an explicit statement about proof
availability, not a guess about likely validity.

### Negative-soundness lemma

**Lemma 4.** Whenever `realizability()` returns `Some(false)`, no completion of
the current prefix can be equal to the target without violating the declared
disjointness invariant.

**Proof.** Syntax death is immediate from the CFG derivative. Otherwise, the
explicit path is used only when zipper reconstruction is complete, so every
semantic root of every current frontier branch occurs in the enumerated root
set. Each root has a captured `Disjoint(root, target)` fact; equality would
canonicalize that row to `Disjoint(x, x)`, which the invariant rejects. In the
free-family path, structural induction on the finite grammar AST gives either
the unique equal constructor/field shape, which the exact positive product
would witness, or a generated disjointness derivation at the first differing
constructor or primitive field. Since the positive product is empty, only the
second case remains. No incomplete enumeration or absent fact participates in
either proof. ∎

## 8. Reading the current frontier

At epsilon, PwZ has not made a terminal frontier. Let \(P_S\) be the productive
full space of the start nonterminal. Then

\[
Q_\tau(\epsilon)\iff \operatorname{Produces}_{s_r}(P_S,r_\tau).
\]

After at least one lexeme, each current frontier item contains a terminal memo
\(m\) and the exact semantic space \(P_l\) of the just-consumed lexeme. The
prefix is viable exactly when some item satisfies

\[
\operatorname{Realizable}^M(m)
\quad\lor\quad
\exists s,q.\;
\operatorname{RealizableFor}^M_s(m,q)
\land \operatorname{Produces}_s(P_l,q).
\]

An exact terminal space is a singleton at every inferred lexical sort, so the
implementation performs the second test directly with the current lexeme's
egglog value. The operation is a hash lookup per frontier item and inferred
terminal sort. On an LL(1) path both counts are bounded.

If PwZ's frontier is empty, the syntactic prefix has no completion and the
answer is permanently empty. By contrast, a nonempty syntactic frontier with
no current realizability fact is not discarded: a later e-graph delta can derive
one and revive the unchanged prefix.

## 9. Positive-intersection theorem

**Theorem 5.** At every lexeme boundary or supported egglog update for which
private target projection and the local relations have reached their fixed
point, `intersection_is_empty()` is true exactly when

\[
PrefixSpace_G(w)\cap[r_\tau]=\varnothing.
\]

**Proof.** PwZ correctness says its frontier represents exactly the derivative
of the CFG language after \(w\). Its value-producing extension associates each
completed fragment and pending sibling with the semantic spaces generated by
the grammar actions. Productivity filtering ensures those pending spaces have
finite completions.

At epsilon, Lemma 2 says the start space intersects the target exactly when a
complete parse with a target AST exists. At a nonempty prefix, Lemma 3 says a
frontier memo has a value-sensitive or value-independent target continuation
exactly when its matched terminal can be extended to such a parse. The
frontier test in Section 8 is therefore equivalent to

\[
\exists u,t.\;yield(t)=wu\land h(t)\equiv_\tau r_\tau,
\]

which is \(Q_\tau(w)\). The compatibility emptiness API caches and returns its
negation; Section 7 gives the additional requirements for a proved negative. ∎

If an automatic prefix-round allowance is exhausted, all retained relations
are a sound subset of that fixed point. Consequently
`intersection_is_empty() == false` and `Some(true)` still have a concrete
witness, but `intersection_is_empty() == true` alone is not a completeness
claim. The three-way API returns `None` unless an independent explicit
disjointness proof already establishes `Some(false)`.

## 10. Why incremental updates equal recomputation

All parser-space, captured e-graph, `Produces`, `RealizableFor`, and
`Realizable` databases grow monotonically. Most source facts and all derived
relations suppress duplicates. The fresh-union fast path described in Section
4 can admit one redundant alias premise; because the closure relations are
sets, processing that premise leaves the same least fixed point.

On a lexeme push, PwZ emits newly discovered facts, with only the harmless
fresh-alias exception above. The local worklist joins those facts with retained
captured rows. If no focused facility is enabled, this remains the complete
push path. Otherwise, new finite spaces and concrete zipper outputs are
materialized, their bindings are marked relevant, and the bounded joint
egglog schedule is stepped before captures and the local worklist are drained.
No earlier parser fact or lexeme is replayed. Replacing the current frontier
changes the positive query and starts a fresh bounded output reconstruction.
If that frontier becomes empty, the CFG left quotient is empty and stays empty
under every suffix. Facts emitted while discovering this absorbing state can
therefore be discarded, and later pushes skip lexical materialization and
local matching entirely.

On an egglog update, the user program runs first. The private rules then export
new target-reachable or canonicalized e-node/domain rows, the canonical target
is marked locally, and the same worklist drains. No parser fact is reinserted
and no earlier lexeme is replayed.

A standard seminaive invariant applies while the parser is live: after each
drain, every Horn-rule instance over all facts seen so far has its conclusion in
the database. When a
new premise arrives, constructor/space/memo/context indexes revisit every rule
instance which can contain that premise. Induction over insertion events shows
that the resulting relations are the same least fixed point a from-scratch run
would compute. Therefore the positive intersection depends only on the final
pair \((w,E_\tau)\), not on whether a merge occurred before or after the
lexemes. The three-way query additionally records whether its bounded
saturation and output-proof obligations completed; an exhausted attempt
conservatively reports `None` and may become decisive after later progress.

Monotonicity is essential. A deletion, subsumption, replacement, or scope
rollback could invalidate a retained \(E_f\), `Produces`, `RealizableFor`, or
`Realizable` fact. Both the
initial egglog program and every later update are parsed and validated before
execution. Validation recursively inspects rule heads, so it also rejects a
nonmonotone rule installed initially but triggered only by a later `run`. The
implementation has no truth-maintenance layer and rejects `delete`,
`subsume`, `set`, `push`, `pop`, `include`, `input`, and opaque user-defined
commands. The API contract requires all updates to be monotone.
Grammar action symbols are additionally checked against constructors declared
by initial egglog `datatype`/`constructor` commands. User commands cannot name
the private matcher namespace, and operational commands (`panic`, `check`,
`extract`, printing, and output) are rejected. Because egglog command batches
execute sequentially, a batch which errors after a successful monotone command
is synchronized through the private and local fixed points before its error is
returned.

## 11. Complexity

The useful bound is delta- and output-sensitive, not a claim that every
equality-saturation step is constant time. For one update, let

- \(p\) be the number of new PwZ space and continuation facts;
- \(e\) be the number of newly exported target-reachable/canonicalized e-graph
  rows;
- \(j\) be the constructor and indexed relation candidates examined while
  joining those deltas;
- \(d\) be the number of new `Produces`, `RealizableFor`, and `Realizable`
  tuples derived;
- \(z\) be the current frontier size and \(\ell\) the number of inferred lexical
  sorts for its terminal;
- \(b\) be the number of lexeme bytes inspected, hashed, or interned by the
  selected-terminal or validated-token path;
- \(m\) be the number of new fixed-term bindings and concrete constructor
  combinations materialized;
- \(x\) be the zipper-output states and combinations inspected by the bounded
  negative-proof pass;
- \(y\) be new memo/context payload events handled by incremental focus
  propagation;
- \(T_{focus}\) be egglog work performed by the automatic focused rounds.

With expected constant-time hash-table operations, a lexeme update costs

\[
T_{PwZ}(a)+O(b+p+j+d+z\ell+m+x+y)+T_{focus}.
\]

On the positive-only fast path, \(m=x=y=T_{focus}=0\). When disjointness or
managed saturation is enabled, \(x\) and per-update \(y\) are capped by their
work allowances and the number of joint egglog rounds is capped separately.
Ordinary acyclic LL(1) focus propagation is delta-only, so historical zipper
length does not appear in \(y\). None of these caps bounds work inside one
egglog round. Ambiguous fixed spaces may expose a real constructor
cross-product, which is counted in \(m\) and may cause the output pass to stop
with `None`.

A new syntax constructor/continuation fact probes retained \(E_f\) rows of the
same constructor. A new \(E_f\) row probes retained syntax applications and
continuations for that constructor. A `Produces`, `RealizableFor`, or
`Realizable` delta follows indexes containing its exact
sort/space/memo/context. Thus \(j\) records real candidate work even when a
candidate does not produce an output; the bound does not hide that cost inside
\(d\).

For a fixed grammar and fixed target-reachable e-graph on an LL(1) stream,
\(p,j,d,z,\ell\) are bounded per lexeme. The positive-only overhead is therefore
\(O(1)\) with bounded lexemes. The focused path has the same bound when each
derivative creates a bounded number of bindings and its seminaive egglog delta
per automatic round is bounded. This is the intended common path, not a theorem
about arbitrary rewrite systems. With variable-length selected lexemes the
byte term sums to the total selected input size. Ambiguity, a growing focus
basin, or an expanding rewrite can increase the work; the general bound above
applies.

The implementation keeps those constants small by interning action
constructors once, packing arena references into `u32` records, using
`SmallVec<[SpaceId; 4]>` for ordinary constructor arities, storing each common
zero-or-one-value row of the compact relation in an eight-byte cell and
promoting exceptional wide rows to hashed membership, using dense adjacency
lists, and reusing fact buffers. When productive SELECT sets
are pairwise disjoint, the predictive path also uses the direct-completion
optimization from Section 4. These representation choices do not change the
asymptotic bound.

For an egglog update,

\[
T_{update}
=T_{user\text{-}egglog}
 +T_{private\text{-}reach}
 +O(e+j+d+z\ell).
\]

There is no unconditional \(O(n)\) term for rebuilding or replaying the
prefix. An unrelated target-unreachable change has \(e=j=d=0\) on the local
side after the private schedule finds no new rows, but it still pays the user
update and private-schedule invocation costs. \(T_{private\text{-}reach}\)
includes egglog's own seminaive matching and rebuild-candidate work; it is not
assumed to be a function of output count \(e\) alone. However, one relevant
merge can enable \(\Omega(n)\) historical continuations, so no correct
materialized algorithm can promise \(O(1)\) for every e-graph update.
Posting-list indexes choose candidates satisfying an exact output or child
premise; unmatched new e-nodes therefore do not scan every historical
application of their constructor. Any remaining candidate checks are included
explicitly in \(j\).

Memory is

\[
O(M_{PwZ}+E+Produces+RealizableFor+Realizable+FixedTerms+Disjoint+\text{indexes}),
\]

where \(E\) contains only captured target-reachable rows. In the worst case the
materialized production/realizability relations and ambiguous fixed-term
combinations have product size. On the intended fixed-egraph LL(1) workload
they grow linearly with the prefix. Fixed terms are stored as a DAG of shallow
bindings, while the persistent zipper avoids quadratic AST-spine copying.
