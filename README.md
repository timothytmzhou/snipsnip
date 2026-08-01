# prefixspace

`prefixspace` maintains the following question while two streams evolve:

\[
\text{does there exist a suffix }u\text{ and a parse of }wu
\text{ whose AST is in the distinguished egglog e-class?}
\]

The syntax stream grows by one complete lexeme at a time. Between lexemes, the
egglog program may also grow and run equality saturation. The monitor exposes
both the original positive-intersection answer and a conservative three-way
answer:

- `Some(true)` means a completion in the distinguished e-class has been
  witnessed;
- `Some(false)` means every completion has been proved impossible;
- `None` means neither statement is currently proved.

`intersection_is_empty()` remains the compatibility view: it reports whether
the positive intersection currently has no witness, and therefore does not
distinguish a proved negative from `None`.

This is a live intersection. A prefix which is semantically empty can become
viable again after an e-class merge, without replaying the prefix. A prefix
which is syntactically dead remains dead, because appending tokens cannot repair
a CFG prefix which has no completion.

## Web demo

The browser demo is deployed at
[timothytmzhou.github.io/snipsnip](https://timothytmzhou.github.io/snipsnip/).
It runs the Rust monitor and egglog entirely inside a Web Worker. The default
example checks a small TypeScript declaration fragment, colors every complete
lexeme by the three-way result at that prefix, and shows its processing time.
The Egglog program is editable. A trailing incomplete keyword or string stays
uncolored until it is complete, and editor updates are debounced for 300 ms.

To build the static site locally, install `wasm-bindgen-cli` 0.2.126 and run:

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.126 --locked
./scripts/build-web.sh
```

Serve `dist/` over HTTP; loading it directly with a `file:` URL cannot start
the module worker. GitHub Actions runs the Rust suite, builds the WASM bundle,
exercises it from JavaScript, and deploys `dist/` to Pages.

## How the live monitor works

The implementation keeps the parser and e-graph incremental for different
reasons and joins their deltas locally:

1. A value-producing Parsing-with-Zippers recognizer records compact,
   persistent AST-space and zipper-continuation facts. It does not copy the
   whole pending AST spine at every prefix.
2. Private egglog rules start at the distinguished class and follow only
   constructors used by grammar actions. Egglog capture primitives export
   newly enabled target-reachable e-nodes and primitive child values.
3. An indexed `RealizabilityEngine` maintains the least fixed point of
   `Produces`, `RealizableFor`, and value-independent `Realizable` facts.
4. When focused equality saturation or disjointness is enabled, completed
   concrete fragments are inserted once as private egglog bindings. The
   focused path propagates new bindings through new zipper edges with an
   append-only delta worklist. A separate bounded snapshot pass constructs all
   concrete candidate roots only when a universal disjointness proof needs
   them.
5. Those bindings mark their e-classes as relevant to focused saturation. Managed
   rewrites, focus-guarded free-constructor disjointness rules, and private
   target projection are stepped automatically after the derivative, with a
   bounded prefix-round allowance.
6. The current answer first checks for a positive witness, then accepts a
   negative answer only from syntax death or an explicit, complete
   disjointness proof. Every incomplete or exhausted proof attempt yields
   `None`.

Both parser implementations consume one `GrammarFlowAnalysis`. Productivity
and nullability use counted dependency agendas; FIRST and FOLLOW use the same
generic event-driven delta scheduler as `RealizabilityEngine`. Each program
keeps its own compact relations and indexes, so sharing the scheduler does not
reintroduce whole-program scans on the singleton lexeme path.

On the positive-only fast path, `push_lexeme` still performs just the PwZ and
local-worklist delta. When focused saturation or disjointness is configured, a
push may additionally materialize newly fixed terms and step the focused
egglog rules. It never serializes the e-graph, builds an explicit CFG/e-graph
product, or replays an earlier token. Each private term is inserted once and
each historical parser fact is indexed once. `run_egglog` runs the user update,
recloses installed managed saturation rules, and runs private target
projection, then feeds only new or newly canonicalized rows into the local
worklist.

The hot representation uses interned constructor IDs, packed `u32` arena
records, inline small vectors for ordinary constructor arities, reusable fact
buffers, and compact dense relations. On grammars whose productive SELECT sets
prove predictive choice, completed PwZ values flow through directly instead of
allocating an ambiguity-union space and alias at every completion. These are
constant-factor optimizations; the live semantics and general ambiguity path
are unchanged.

The older `PrefixMonitor` API is still available for a fixed e-graph. It
compiles a frozen regular-tree-grammar product once. Use `LivePrefixMonitor`
when lexemes and equality-saturation steps must be interleaved.

## Grammar and lexer input

The frontend accepts an ordinary Yacc grammar and, optionally, a Lex
specification. Every production needs one deliberately small semantic action:

```yacc
%start expr
%token ID PLUS LPAREN RPAREN
%%
expr: ID             { Var(1) }
    | expr PLUS expr { Add(1, 3) }
    | LPAREN expr RPAREN { $2 }
    ;
```

`Constructor(1, 3)` uses one-based RHS positions, which must be strictly
increasing. A selected position may be a nonterminal or a terminal. `$2` is a
projection action: it returns one RHS value without constructing a wrapper.
Unselected RHS values are ignored.

A selected terminal gets its value from the complete lexeme. Its constructor
schema must infer the terminal sort as egglog `String` or `i64`, and the grammar
must have a Lex specification. Basic regexes, longest-match behavior, and skip
rules use standard Lex syntax:

```lex
%%
\+                         'PLUS'
\(                         'LPAREN'
\)                         'RPAREN'
[0-9]+                     'INT'
[a-zA-Z_][a-zA-Z0-9_]*     'ID'
[ \t\r\n]+                 ;
```

The stream is lexeme-granular, not character-granular. `push_complete_text`
lexes one complete source string and reports an answer after every emitted
lexeme; ignored text creates no update. `push_token_name` accepts one terminal
name and its complete spelling and validates that spelling against the lexer.
`push_lexeme` is the lower-level pretokenized API and trusts its token kind.
Formally, completions range over already-delimited `(terminal, lexeme)` events;
they do not solve cross-token maximal-munch constraints for an unknown raw
source suffix. `push_complete_text` is an adapter for text already supplied,
not a change to that completion alphabet. `TerminalId` and `Token` values are
grammar-local handles: obtain them from the same `Grammar` used to construct
the monitor (the implementation can range-check, but cannot brand equal numeric
IDs from different grammars).

The supported Yacc subset is raw BNF, including recursion, ambiguity, and
epsilon productions. Precedence declarations, embedded programs, and stateful
Lex features are rejected instead of being assigned different semantics.

## Live API

```rust
use prefixspace::{Grammar, LivePrefixMonitor};

let yacc = r#"
    %start id
    %token ID
    %%
    id: ID { Var(1) };
"#;
let lex = r#"
    %%
    [a-z]+ 'ID'
"#;
let egglog = r#"
    (datatype Ast (Var String))
    (let $root (Var "x"))
"#;

let grammar = Grammar::from_yacc_lex(yacc, lex)?;
let mut monitor = LivePrefixMonitor::from_egglog(&grammar, egglog, "$root")?;

// The empty prefix has the completion `x`.
assert!(!monitor.intersection_is_empty());
assert_eq!(monitor.realizability(), Some(true));

// Var("y") is not initially in the target class.
assert!(monitor.push_token_name("ID", "y")?);
// With no disjointness proof, absence of a witness is not a proved negative.
assert_eq!(monitor.realizability(), None);

// No lexeme is replayed or pushed here. The same prefix becomes viable.
assert!(!monitor.run_egglog("(union $root (Var \"y\"))")?);
assert_eq!(monitor.realizability(), Some(true));
# Ok::<(), Box<dyn std::error::Error>>(())
```

The main operations are:

- `push_lexeme(terminal, text)`, `push_token`, and `push_token_name` advance the
  syntax stream. Their Boolean return is the compatibility emptiness answer;
  `realizability()` reads the stronger `Option<bool>` result.
- `push_complete_text` is the complete-input Lex adapter.
- `run_egglog(update)` executes a monotone egglog update, incrementally closes
  the private reachability rules, and returns the answer for the unchanged
  prefix.
- `add_managed_rewrites(source)` installs focused equality rules. Each directed
  `rewrite` runs forward only when its left-hand side is in the relevant area
  starting at the target or a materialized fixed prefix term; each `birewrite` installs
  both guarded directions. Rules remain installed and are reconsidered as
  later parser or e-graph deltas grow that basin.
- `add_managed_rewrites_with_round_limit`,
  `run_egglog_with_managed_saturation_round_limit`, and
  `continue_managed_saturation` provide resumable execution for expanding rule
  systems. The number limits joint fixed-point rounds, not work, time, e-node
  allocation, or memory within a round. Exhausting it returns a typed error
  after synchronizing the sound partial e-graph delta.
- `intersection_is_empty()` reads the cached current answer.
- `realizability()` returns `Some(true)`, `Some(false)`, or `None` as described
  above.
- `stats()` exposes PwZ work, persistent representation sizes, local
  production/realizability tuples, and delta-rule activity. `full_rebuilds` is
  always zero for the live architecture.

Grammar action symbols must already be declared by an egglog `datatype` or
`constructor` command when the monitor is created; arbitrary custom functions
are not ranked AST constructors. The target binding must have an egglog
equality sort.
The live API supports monotone updates such as adding terms, unions, rewrites,
and runs. Both the initial egglog program and every later update are parsed and
validated. This also rejects a nonmonotone rule installed initially but only
triggered by a later `run`. Operations which can remove or opaquely replace
facts—`delete`, `subsume`, `set`, `push`, `pop`, `include`, `input`, and
user-defined commands—are rejected: retained delta facts would require truth
maintenance to retract them. Diagnostic/side-effecting commands such as
`panic`, `check`, `extract`, printing, and output are also outside the update
API. User updates cannot refer to the monitor's reserved private namespace. If
egglog nevertheless returns an error after partially executing a command
batch, the monitor consumes that monotone partial delta before returning the
error, so its cached answer remains current.

### Disjointness and proved negatives

`from_egglog_with_disjointness` names a positive egglog relation of type
`(TargetSort TargetSort) -> Unit`. A row `Disjoint(a, b)` is treated as a proof
that the two classes cannot consistently merge. The monitor never treats a
missing equality or a missing relation row as negative evidence.

The source extension `(free Sort Disjoint)` declares the constructors of
`Sort` to be free. It expands to ordinary egglog rules for constructor
no-confusion, injectivity, recursive field disjointness, primitive inequality,
symmetry, and an invariant which panics if `Disjoint(x, x)` is ever derived.
For example:

```rust
# use prefixspace::{Grammar, LivePrefixMonitor};
# let grammar = Grammar::from_yacc("%start s\n%token S\n%%\ns: S { StringType() };\n")?;
let program = r#"
    (datatype Type (Number) (StringType))
    (free Type TypeDisjoint)
    (let $required (Number))
"#;
let mut monitor = LivePrefixMonitor::from_egglog_with_disjointness(
    &grammar,
    program,
    "$required",
    "TypeDisjoint",
)?;
monitor.push_token_name("S", "string")?;
assert_eq!(monitor.realizability(), Some(false));
# Ok::<(), Box<dyn std::error::Error>>(())
```

For a general disjointness relation, the bounded zipper pass must enumerate
every semantic root of the current prefix before rows for all of those roots
can prove `Some(false)`. An open future value, a reachable zipper cycle, a
missing relation row, or work-budget exhaustion leaves the answer as `None`.
The closed free-constructor case additionally admits a structural proof once
the target has a constructor representative and every grammar constructor is
covered by the complete free family.

For a symmetric equality rule, managed saturation can remain entirely inside
the focus area marked by the target and fixed prefix terms:

```rust
# use prefixspace::{Grammar, LivePrefixMonitor};
# let grammar = Grammar::from_yacc("%start s\n%token BAD\n%%\ns: BAD { Bad() };\n")?;
# let mut monitor = LivePrefixMonitor::from_egglog(
#     &grammar,
#     "(datatype Ast (Good) (Bad)) (let $root (Good))",
#     "$root",
# )?;
# monitor.push_token_name("BAD", "bad")?;
assert!(!monitor.add_managed_rewrites("(birewrite (Bad) (Good))")?);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Complexity contract

For a fixed grammar, fixed target-reachable e-graph, fixed lexer, and bounded
lexeme size, an LL(1) stream creates a bounded parser/realizability increment
per lexeme. On the positive-only path, the work beyond the PwZ derivative is
therefore constant per lexeme. The focused path also remains constant per
lexeme when it creates a bounded number of concrete bindings and each bounded
egglog round performs bounded delta work. Its round limit is a termination
guard, not a constant-time guarantee: one round may still contain many rule
matches. Variable-size selected lexemes cost their byte length to validate,
hash, and intern. Ambiguity can expose a constructor cross-product, while open
or cyclic zipper output is conservatively abandoned as `None` at the work
limit.

An equality-saturation update is delta-driven, not prefix-driven: there is no
mandatory scan or replay of all prior lexemes. Its cost includes the user's
egglog work, newly target-reachable or canonicalized e-graph rows, candidate
joins for their constructors, and newly derived local tuples. A single relevant
merge can legitimately enable results at many historical continuations, so
e-graph updates do not have a universal `O(1)` bound. No-op and
target-unreachable updates add no local realizability facts.

Managed saturation is output-sensitive in the focused basin. An ordinary
directed rule whose LHS is outside the area marked by the target or fixed prefix is
deliberately not fired; this API therefore has focused forward semantics rather
than an unrestricted egglog schedule. Only newly materialized terms and the
resulting target-projection delta are processed, so parser history is never
replayed.

The exact bounds and proof are in [docs/algorithm.md](docs/algorithm.md#11-complexity).
Structural checks and reproducible benchmarks are described in
[docs/performance.md](docs/performance.md).

## Validation

Run the complete test suite with:

```sh
cargo test
```

The suite includes independent finite-language differential oracles for
nullable, projected, ignored, selected-lexeme, cyclic, left-recursive, and
ambiguous cases; merge-before/merge-after convergence tests; rewrite and
congruence updates; and structural linear-growth checks.

It also ports ChopChop's e-graph expression cases, dynamic and nested-let
cases, duplicate-name negative, syntax baseline, and all ten benchmark headers
at lexeme boundaries. Additional tests interleave e-class unions with lexeme
pushes. Attribution and the pinned upstream commit are recorded in
`THIRD_PARTY_NOTICES.md`.

Run the live benchmarks with:

```sh
cargo bench --bench live
```

The streaming group reports three layers: recognition-only PwZ, the explicit
value forest plus indexes with no productive target join, and the complete live
intersection. A whole-process 100,000-lexeme reference, including setup, is
recorded in [docs/performance.md](docs/performance.md#measured-reference).

## Reference

The parser is an arena-based, iterative specialization of Pierce Darragh and
Michael D. Adams, “Parsing with Zippers (Functional Pearl),” ICFP 2020,
DOI 10.1145/3408990. It extends the recognizer with compact semantic spaces and
explicit continuation facts needed by the live intersection.
