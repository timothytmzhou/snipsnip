# Streaming realizability

## Question answered

For a prefix of complete lexer tokens `w`, the monitor asks whether some
completion `w'` parses and produces an AST equal to the Egglog value named by
the target binding.

The answer is `Option<bool>`:

- `Some(true)`: the current e-graph contains a witness.
- `Some(false)`: the parser has no live zipper, or every possible current
  output is explicitly proved disjoint from the target.
- `None`: neither statement is proved.

Not finding a witness is never treated as a negative proof.

## Three separate components

### Paper PwZ

`paper_pwz` is an ID-and-map implementation of *Parsing with Zippers*, with
optional SELECT sets that only prune branches unable to consume the next
terminal. It does not compute grammar analyses or know about semantic actions,
lexing, or Egglog. `Pwz::new` builds the initial cyclic grammar graph.
`Pwz::derive` consumes one token and reports new expressions and contexts plus
appended memo-parent and alternative-child edges.

The current `Zipper` values contain a focus and a memo ID. Expressions,
contexts, and memos live in maps, so cycles do not require pointer graphs.

### Egglog adapter

`egglog_backend` owns the only e-graph. It validates the constructors used by
grammar actions, converts complete token values to Egglog values, reads
constructor applications and equality classes, runs the user's rules, and
reports structural changes. It also indexes the restricted unconditional
rewrite shapes that can guarantee a result despite unfinished constructor
arguments. It does not own or copy PwZ state.

The user's program is authoritative. The monitor does not invent equations,
rewrites, or typing rules.

### Monitor link state

`Monitor` owns one PwZ parser, one Egglog adapter, and the indexed links between
them. It consumes the `Changes` returned by `derive`; it does not retain a
second parse forest or a second e-graph.

## Positive intersection

The linking fixed point has three useful meanings:

- `Produces(expression, class)`: a semantic value of this completed PwZ
  expression is represented by this e-class.
- `RealizableFor(site, class)`: putting this class in the hole at this memo or
  context can eventually reach the target class.
- `Realizable(site)`: that site can reach the target without depending on the
  hole's value.

These are Rust data structures, not relations injected into the user's
Egglog program. Each new PwZ edge or relevant e-graph row is placed on a work
list. Exact indexes wake only the propagation cases which mention it. Facts
are deduplicated, so draining the work list computes the least fixed point.

A current zipper is realizable when its focus value and memo satisfy the
closed linking facts. The engine can also recognize an already-materialized
current output equal to the target. This is the `Some(true)` witness.

The important incremental property is that a token derivative contributes
only its returned PwZ changes. Egglog changes are summarized as target,
terminal, or constructor notifications; an arbitrary user update may
conservatively notify every monitored schema. Neither operation replays the
old token stream or rebuilds the full product.

## Negative proof

Egglog may optionally define a binary relation named `Disjoint` over the
target equality sort. It can contain direct facts or facts derived by the
user's rules. The relation is read in either argument order. The backend
rejects `Disjoint(x, x)` after canonicalizing e-classes. An absent or empty
relation costs no zipper walk.

For a negative answer, the monitor computes a temporary finite e-class cover
of every AST represented by every live zipper. Alternation requires every
branch; construction requires every combination of selected children. Known
combinations use existing Egglog applications. An unfinished child can be
crossed only when an unconditional user rewrite guarantees the constructor's
result for every value of that child, for example `Add(Error, x) -> Error`.
Outer applications reached from such a result are materialized on demand and
sent through focused saturation. Nothing outside a current zipper proof path
is created.

The current fragment is never compared directly with the target: later syntax
may wrap or transform it. The cover is carried through every live context to a
top-level result. Repeated pairs of a PwZ memo and carried e-class close context
cycles; processing the pair once has already considered every finite exit.

The result is `Some(false)` only when the cover is nonempty and
`Disjoint(output, target)` holds for every covering class. An uncovered branch,
unsupported rewrite shape, recursive expression whose cover cannot be closed,
missing value, or more than 4,096 combinations at one constructor yields
`None`. Thus a work limit or incomplete saturation can reduce precision but
cannot create a negative answer. The program author remains responsible for
the truth of user-defined rewrites and `Disjoint` facts.

## Focused equality saturation

After a derivative, syntax death returns immediately. Otherwise the monitor
checks the already-closed positive intersection; an existing witness skips
materialization and rule execution. The disjointness proof is attempted only
after synchronization.

When no positive witness is present, it materializes selected fixed subtrees
in postorder and then the exact applications needed along current zipper
contexts. A negative cover may additionally demand an outer application after
a user rewrite has summarized unfinished syntax. The target class and classes
found on those paths form the current focus. Focus is closed downward through
every visible equality-output constructor, so nested relevant redexes are
included.

Each local step selects at most 64 matches per installed internal rule. The
monitor propagates the delta and repeats while the e-graph changed or relevant
matches were deferred, stopping early on a positive witness. A rewrite may be
selected when either its left-hand-side root or an already-existing
right-hand-side root is focused, but it always performs the user's forward
union. A birewrite is two directed rewrites. General `rule` commands are
considered globally by the same batched scheduler.

Selection is capped at 4,096 matches per rule and focused class over the
monitor's lifetime. This can limit positive precision, and it does not globally
terminate a rule that keeps creating fresh focused classes. An explicit
`Disjoint` fact remains authoritative; if later equality makes its endpoints
equal, the backend rejects the inconsistent program.

This scheduling changes when work is attempted, not the meaning of an
answer. `Some(true)` always has a represented witness, and `Some(false)` never
depends on saturation having stopped early.

## Lexer boundary

`Pwz::derive` accepts tokens, not partial source text. A caller streaming raw
text should use `Grammar::lex_prefix`: it returns tokens whose maximal-munch
boundaries are fixed and a trailing pending slice. The pending slice must be
held outside the monitor until a later character fixes its boundary. The web
analyzer follows this rule.

`Monitor::push_complete_text` is for a chunk known to contain only complete
lexemes. It lexes the entire chunk before calling any derivative, so a lexing
error leaves the parser unchanged. `push_token`, `push_token_name`, and
`push_lexeme` likewise describe an already-confirmed token boundary.

## Correctness argument

The PwZ theorem says that after deriving `w`, the live zippers represent
exactly the parse trees of strings beginning with `w`. Adding simple linear
actions to sequence completion preserves that invariant by structural
induction: selected children are combined in source order and unselected
children contribute no semantic value.

For the positive direction, induction over expression and context edges shows
that every linking fact denotes a real PwZ fragment joined to a real Egglog
class. Conversely, any finite target-equal AST represented by a live zipper
decomposes into the same constructor rows, so work-list closure derives its
`Produces` and `RealizableFor` facts. Therefore `Some(true)` is equivalent to
an exhibited member of `PrefixSpace(w)` in the target class.

Syntax death is exact by the PwZ invariant. In the other negative case, each
live route is covered either by an existing constructor application or by an
unconditional rewrite whose result does not depend on its unfinished
arguments. Structural induction over expressions and contexts therefore shows
that every possible completed AST belongs to one of the returned classes. If
every such class is related to the target by sound `Disjoint`, none can be the
target. Therefore every returned `Some(false)` is sound. All remaining cases
return `None`.
