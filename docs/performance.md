# Performance validation

The live design has three paths which must be measured separately:

- a positive-only lexeme push, which stays in PwZ and the local matcher;
- a focused lexeme push, which may materialize fixed terms and perform bounded
  managed/free/private egglog rounds;
- an equality-saturation update, where work should depend on the e-graph and
  local deltas rather than on a full prefix replay.

Wall-clock timings alone are too noisy to enforce those properties, so the
repository combines structural regression tests with Criterion benchmarks.
This document deliberately does not reuse measurements from the older frozen
product architecture.

## What a lexeme push does

`LivePrefixMonitor::push_lexeme` performs:

1. one value-producing PwZ step;
2. insertion of newly emitted space and zipper facts into the local matcher;
3. when configured, insertion of new concrete fixed trees, incremental focus
   propagation through new zipper deltas, and (only for an explicit universal
   proof) bounded reconstruction of the current concrete roots;
4. when focused execution is enabled, marking those bindings as relevant followed by
   automatic managed-rewrite, focus-guarded free-disjointness,
   focus-projection, and
   target-projection rounds;
5. capture and local-worklist closure;
6. the positive frontier lookup and conservative disjointness proof.

The positive-only path does not run an egglog ruleset. The focused path does,
but neither path serializes classes, rebuilds a CFG product, or replays an
earlier lexeme. A fixed term is inserted once as a shallow private binding; the
pending AST spine is not copied. Selected `String`/`i64` spellings cost time
proportional to their bytes. Unselected terminal spellings are not retained as
distinct semantic spaces unless an enclosing action makes a concrete result
independent of that token.

The hot path interns action constructors once, packs arena references into
`u32` records, uses `SmallVec<[SpaceId; 4]>` for ordinary arities, reuses parser
fact buffers, and stores each common zero-or-one-value compact-relation row in
an eight-byte cell with shared spill storage for larger rows. A predictive
SELECT analysis enables direct completion on LL(1)-style choices, avoiding a
union-space allocation and alias in the common case. These are implementation
constants, not additional semantic assumptions.

For a fixed grammar/e-graph LL(1) workload, the structural expectation is:

| quantity | expected growth over \(n\) lexemes |
|---|---:|
| PwZ derivatives | \(n\) |
| PwZ events and memo records | \(O(n)\) |
| persistent space/zipper states and facts | \(O(n)\) |
| local production/realizability tuples | \(O(n)\) |
| fixed-term bindings on an LL(1) focused path | \(O(n)\) |
| full product rebuilds | \(0\) |

These are the invariants behind the constant extra work per lexeme claim for a
fixed LL(1) workload. Focused execution additionally requires a bounded number
of new bindings and bounded seminaive work per egglog round. The 64-round limit
prevents unbounded automatic iteration, but one round can still contain many
matches. Ambiguity can expose a constructor cross-product; zipper cycles, open
selected future values, and the 2,048-step output budget cause the negative
answer to remain `None`. The general delta bound is given in
[algorithm.md](algorithm.md#11-complexity).

## What an e-graph update does

`LivePrefixMonitor::run_egglog` first runs the user's update. It then recloses
installed LHS-guarded managed directions in the area marked by the target and
fixed terms, closes private target reachability and free-disjointness rules,
captures newly enabled or newly canonicalized constructor/domain/disjointness
rows, and drains the local matcher.

There is no unconditional loop over lexemes and `full_rebuilds` remains zero.
A no-op run or merge wholly outside the target-reachable constructor graph
should derive no new local tuple. A relevant merge may derive many tuples and
is intentionally output-sensitive: if one union makes \(n\) historical
continuations viable, \(\Omega(n)\) materialized changes are unavoidable.

The local join engine uses posting lists keyed by constructor, argument,
e-value, output demand, sort, space, memo, and context. It checks the shortest
available exact-premise candidate bucket rather than scanning every historical
application of a constructor. Performance reports should still include both
candidate probes and tuple growth, rather than treating “new answers” as the
only work.

## Structural regression tests

`tests/live_performance.rs` enforces the live invariants:

- the longer LL(1) stream (8x in debug and 10x in release) has linear bounds on
  PwZ state, semantic-space and zipper facts, local tuples, delta derivations,
  events, and memo records;
- no-op and target-unreachable e-graph updates add no local pairs and report
  zero delta matches;
- one relevant leaf union changes the answer without a rebuild and adds only a
  small bounded number of tuples in that fixture;
- a newly target-reachable but syntactically unmatched e-node performs bounded
  join probes after both 16 and 1,024 lexemes, detecting history-wide failed
  scans;
- 128 distinct long spellings of an ignored terminal retain exactly the same
  semantic states, facts, and pairs as one repeated spelling;
- after syntactic death, 128 distinct selected spellings add no parser state,
  local tuple, or join-probe work.

Run it in both profiles:

```sh
cargo test --test live_performance
cargo test --release --test live_performance
```

The performance checks are complemented by semantic stress tests:

- `tests/live_differential.rs` compares every bounded prefix in several finite
  languages with hand-written completion/AST oracles. It covers nullable
  selected and ignored holes, projection before and after the current hole,
  ambiguity, exact selected lexemes, and merge timing.
- `tests/live_egraph.rs` covers unchanged-prefix resurrection, nested child
  merges, irrelevant changes, rewrite execution, and exact `String` lexemes.
- `tests/live_semantics.rs` covers projection-sort propagation, nullable left
  recursion, ambiguous tree shapes, and a project unit cycle.
- `tests/live_incremental_regressions.rs` covers recursive and nested late
  e-graph deltas, every selected/ignored sequence-hole position, rejection of
  latent nonmonotone rules, private-namespace isolation, synchronization after
  partial egglog errors, ranked-constructor enforcement, and foreign terminal
  IDs.
- `tests/live_large_matrix.rs` propagates a late leaf union through a retained
  300-constructor product chain, then checks continued streaming and an
  absorbing dead prefix.
- `tests/live_api_contract.rs` covers typed construction/input failures,
  punctuated constructor names, and a six-argument sparse action whose late
  union crosses the inline-storage boundary.
- `tests/chopchop_egraph_port.rs` ports ChopChop's fixed-egraph expression
  cases and ten benchmark headers to complete-lexeme boundaries.
- `tests/chopchop_live_updates.rs` interleaves complete lexemes with unions and
  checks late resurrection and update-order convergence.
- `tests/chopchop_remaining_port.rs` covers the remaining nested-let,
  duplicate-name, and syntax-baseline cases from the same upstream test file.
- `tests/diseq_prover.rs` covers free-constructor mismatch, recursive function
  and array types, primitive constructor fields, explicit unknown results,
  syntax death, disjointness-invariant failure, and an early TypeScript
  annotated-initializer error.
- `tests/unrealizability_performance.rs` checks linear retained-space and
  focused-work growth, the hard snapshot-work limit, binding interning, and a
  large e-graph whose thousands of unfocused terms must not create a
  disjointness cross-product.

The older `tests/performance_contract.rs`, `tests/large_matrix.rs`, and
`benches/streaming.rs` exercise the frozen `PrefixMonitor`. They remain useful
baseline coverage, but their product-compilation results must not be reported
as measurements of `LivePrefixMonitor`.

## Criterion benchmarks

The live benchmark is:

```sh
cargo bench --bench live
```

`benches/live.rs` contains the positive streaming and e-graph-delta baselines,
plus managed-saturation cases. Focused disjointness results should report the
additional fixed-binding and prefix-output counters rather than being compared
to the positive-only layer as though they performed identical work.

### `live_ll1_stream`

For 1,000, 10,000, and 100,000 lexemes it compares:

- `vanilla_pwz`: the same arena PwZ engine without semantic spaces/delta joins;
- `forest_and_indexes`: the value-producing PwZ forest and local indexes with a
  target that has no reachable grammar constructor row, isolating the explicit
  PrefixSpace representation from productive target joins;
- `live`: `LivePrefixMonitor` with a fixed recursive target class.

Monitor/parser construction is supplied through Criterion's batched setup and
is not part of the streamed update body. The benchmark uses
`iter_batched_ref` so dropping the accumulated monitor is not charged to the
lexeme loop. The geometric input sizes make superlinear growth visible rather
than hiding it in a single throughput number.

When recording results, report all three layers at all three sizes.
Near-constant time per lexeme and an approximately linear 10x time increase are
more informative than the 100,000-lexeme point alone.

### `live_egraph_delta`

This group prepares monitors after 1,000, 10,000, and 100,000 lexemes outside
the timed update body, then measures:

- `no_op_run` at every prefix length;
- one `unrelated_union` after 100,000 lexemes;
- one small `relevant_union` which resurrects the current prefix.

The first two cases test the absence of prefix-length-dependent rebuilding.
The relevant case measures the latency of a real target delta; larger
output-producing merge benchmarks should always report the number of newly
derived tuples alongside time.

## Measured reference

A separate whole-process reference ran each 100,000-lexeme layer in five fresh
release processes. The table reports the median of those five runs. Unlike the
Criterion group above, elapsed time includes grammar and monitor construction
as well as the complete token stream; RSS is peak process resident memory.

| 100,000-lexeme layer | median elapsed | median peak RSS |
|---|---:|---:|
| recognition-only `vanilla_pwz` | 9.661 ms | 16,820 KiB |
| `forest_and_indexes` | 41.546 ms | 38,992 KiB |
| full positive-only `live` intersection | 81.182 ms | 46,844 KiB |

A separate 21-process update microbenchmark (seven runs for each case) prepared
a 100,000-lexeme monitor outside the timed operation. A no-op run had a 65.533
us median and an unrelated union had a 121.198 us median; both produced zero
local matches and zero join probes. A result-changing union over the repeated
historical AST had a 31.147 ms median because it derived 599,997 local tuples
and inspected 200,000 indexed candidates. This is the intended distinction
between prefix-independent no-op work and unavoidable output-sensitive
retroactive work.

These measurements exercise a monitor without disjointness or installed
managed rewrites, so lexeme pushes take the positive-only path. They are not a
measurement of fixed-term materialization, automatic focused saturation, or
the bounded negative proof.

These measurements were taken 2026-07-31 on Linux 6.8.0-124-generic,
x86-64, an Intel Core i7-1065G7 (8 logical CPUs), with rustc 1.91.1 and the
checked-in `Cargo.lock`. This workspace had no Git metadata; the SHA-256 of the
sorted per-file hashes for `src/`, `tests/`, `benches/`, `examples/`,
`Cargo.toml`, and `Cargo.lock` was
`630e7af07b31f86bfc99baa9a83a102cbf5d7686ff293a493f53191329dd442d`,
computed by:

```sh
{ find src tests benches examples -type f -print
  printf '%s\n' Cargo.toml Cargo.lock
} | sort | xargs sha256sum | sha256sum
```

The committed profiler reproduces the cases:

```sh
cargo build --release --example profile_live
for mode in vanilla forest live; do
  for run in 1 2 3 4 5; do
    /usr/bin/time -f 'rss_kib=%M' \
      target/release/examples/profile_live 100000 "$mode"
  done
done
for mode in noop unrelated relevant; do
  for run in 1 2 3 4 5 6 7; do
    target/release/examples/profile_live 100000 "$mode"
  done
done
```

These are a measured reference, not a portable guarantee. Absolute elapsed
time and peak RSS depend on the hardware, operating system, compiler,
dependency versions, allocator, and concurrent machine load; compare changes
on the same host and toolchain.

## Interpreting statistics

`LiveMonitorStats` exposes the structural counters used by tests:

- `lexeme_updates` and `egraph_updates` count the two public update kinds;
- `prefix_space_states` counts semantic spaces, PwZ memos, and contexts;
- `prefix_space_facts` counts semantic-space and zipper facts;
- `realizability_facts` counts all materialized `Produces`, `RealizableFor`,
  and `Realizable` facts;
- `fixed_tree_bindings` counts private concrete-term bindings retained for
  focused saturation and disjointness;
- `last_prefix_output_work` and `total_prefix_output_work` count bounded zipper
  states and constructor combinations inspected while reconstructing concrete
  roots for negative proofs;
- `last_prefix_focus_work` and `total_prefix_focus_work` count the separate
  append-only focus deltas; repeated historical zipper paths do not count
  again;
- `last_delta_rule_matches` is local derivations for a lexeme push and the sum
  of private egglog matches plus local derivations for an e-graph update;
- `total_delta_rule_matches` is the corresponding cumulative count;
- `last_delta_join_probes` and `total_delta_join_probes` count candidate
  e-node/product rows actually inspected by the indexed local joins;
- `full_rebuilds` is always zero;
- `pwz` contains ordinary recognizer derivatives, events, and memo records.

Counters are saturating diagnostics, not a stable cost model or serialized API.
In particular, one egglog rule match and one local hash-table insertion need not
take equal time.

## Reproducible reporting checklist

For a performance result intended to compare commits:

1. use a release build on an otherwise idle machine;
2. record CPU, operating system, Rust version, and commit;
3. run the complete correctness suite before benchmarking;
4. report every geometric stream size, not only peak throughput;
5. include `LiveMonitorStats` deltas for e-graph-update cases;
6. distinguish setup, lexeme streaming, no-op updates, and relevant updates;
7. report recognition-only, forest-plus-indexes, and full-live layers
   separately;
8. state whether the live stream is positive-only or enables fixed-term,
   managed, free-disjointness, and prefix-output work, and report their
   counters when enabled;
9. do not compare live numbers with historical frozen-product numbers as if
   they measured the same algorithm.
