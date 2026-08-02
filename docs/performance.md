# Performance validation

## What is expected to be cheap

When a positive witness is already represented, one complete lexeme normally
causes:

1. one PwZ derivative;
2. insertion of only the `Changes` emitted by that derivative;
3. work-list propagation from those changes;
4. a lookup against the current zipper frontier.

No earlier token is replayed, no parse/e-graph product is rebuilt, and no
Egglog copy is made. If the lookup fails, the monitor may also materialize
relevant fixed applications, run focused rule batches, and attempt a negative
cover only when `Disjoint` currently has facts. With bounded token and
constructor arity, the positive path is expected to take constant work per
lexeme and linear total work.

Ambiguous grammars can create more zippers and semantic combinations. A
relevant e-class merge can enable many historical links at once. Those costs
are output-sensitive and cannot in general be constant.

## Equality saturation

The monitor checks the existing intersection before running user rules. When
that is inconclusive, exact classes along current zipper contexts and the
target class become the focus. User rules run in batches of at most 64 matches
per internal rule; each delta is propagated and checked for a positive witness.
Negative proof is attempted after this local work stops. Rewrites are selected
from a focused left or existing right root but still run only forward. General
rules are considered globally.

There is no fixed number of rounds per lexeme. Selection is capped at 4,096
matches per rule and focused class over the monitor lifetime. This may reduce
positive precision, while rules which keep creating fresh focused classes can
still fail to terminate.

The negative cover caps a single constructor's Cartesian child combinations
at 4,096 and returns `None` when that limit is exceeded. Each combination uses
an indexed constructor-row lookup or an indexed unconditional-rewrite
guarantee. Only outer applications demanded after a guarantee are created.
Context cycles are closed by visited pairs of the PwZ memo and carried value;
long acyclic fixed subtrees are materialized iteratively rather than rejected
by a depth limit.

## Lexer cost

Performance measurements count derivatives per confirmed lexeme, not per
keystroke. `Grammar::lex_prefix` withholds the trailing maximal-munch candidate
and the web analyzer sends only confirmed tokens to `Monitor`. Token text can
still make lexing and primitive-value conversion proportional to its byte
length.

## Tests

Run correctness and structural performance coverage in both profiles:

```sh
cargo test --all --no-fail-fast
cargo test --release --all --no-fail-fast
```

The main stress coverage includes:

- long LL(1) streams and irrelevant/relevant late e-graph updates;
- cyclic PwZ contexts and cyclic e-classes;
- bounded ambiguity and sound `None` fallback;
- explicit `Disjoint` proofs, including nested type constructors;
- incomplete trailing lexemes which never reach `derive`;
- thousands of nested TypeScript expressions in `prefixspace-web`.

## Benchmarks

Run the core streaming and e-graph-delta benchmark with:

```sh
cargo bench --bench live
```

Run the TypeScript construction and deep-prefix benchmark with:

```sh
cargo bench -p prefixspace-web --bench typescript
```

The current benchmarks report:

- monitor construction;
- recognition-only PwZ time per lexeme;
- full monitor time per lexeme when the answer is already represented;
- no-op, irrelevant, and result-changing Egglog update latency;
- deep TypeScript streaming and monitor construction.

Measure focused saturation latency and peak retained memory separately when
reporting them.

Use geometric input sizes. Constant time per lexeme should appear as linear
total time, while a result-changing merge should be reported together with
the number of newly enabled facts. Do not compare a focused saturation case
to recognition-only parsing as if they performed the same work, and do not
preserve reference numbers after the implementation they measured changes.
