# Constructive global successor for one custody transfer

This W09 increment extends `9152ae6285abc98d22a7e892da96bdf0737784e3`.
`AssetTransferGlobalSuccessorV1` constructs the nineteen-field mathematical
`GlobalEconomicStateRefinementV2.Verified` witness for one admitted, accepted
custody-complete transfer. It connects the prior economic construction to
global height, lane-write and replay obligations. Runtime economics, wire
formats, policy constants and publication authority are unchanged.

## Constructed contract

The input contains the actual policy-selection transfer input, an occurrence,
the private-port pre and post commitments, and an opaque global post root.
The economic result is the existing custody completion. The successor advances
height by one, replaces only the asset lane root, inserts one replay mapping,
and retains the remaining metadata from that actual result.

```text
Admitted(input) AND actualLeafVerdict(input) = accepted
  -> Verified(pre(input), actualPlan(input), [occurrence(input)], successor(input))
```

The eighteen admission clauses describe the initial state and supplied input:
state/quantity admission, owned-supply equality, claimant backing, empty reserves,
terminal registry and outbox, one enabled lane, release agreement, occurrence
context, adjacent bounded height, fresh replay key and occurrence identity,
private-port pre-root agreement, a distinct post lane root, unsigned command
bounds, and fee eligibility under the actual policy lookup. No desired output
table, replay mapping or `Verified` field is assumed.

Both replay freshness conditions matter. Key freshness prevents overwriting a
prior consumption; occurrence freshness prevents two keys from naming the same
consumption. The proof transports quantity admission across the constructed
replay registry and bounded height increment. Existing oracle observations
remain within the new height. Exact table/supply effects, conservation,
annotations and claimant backing come from the actual custody-complete result.
Together these establish all nineteen fields of the existing global relation.

The `release`, `terminalEmpty` and `outboxEmpty` clauses restrict the intended
runtime slice. The mathematical proof frames those fields and does not consume
those three premises. They are retained explicitly rather than treated as
proved runtime admission or silently removed from the supported scope.

`step` branches on the actual leaf verdict. It does not execute the `Admitted`
predicate. Its accepted result has the `Verified` guarantee under that predicate;
`acceptedWitness` requires both input admission and actual leaf acceptance.
A rejected leaf returns the exact initial global state, the empty effect plan,
and no consumed occurrence.

Roots remain opaque in Lean. The post lane root is supplied with an explicit
inequality premise; the global post root is a supplied commitment parameter.
The theorem does not compute either hash. The existing global `Verified`
relation does not read the post global root. Computing and authenticating those
commitments remains a separate implementation and publication obligation.

## Evidence and replay

Fable produced the proof and initial harness. Root mathematical review accepted
the frozen theorem subject; an independent static review examined the harness.
Root added a literal proof pin, exact registration check, public coordinator
composition, missing metadata observations and complete refusal-input snapshots.
It also removed an unsupported runtime occurrence-ID unreachability claim.
Independent root replay then passed all eight focused cases in 58.79 seconds.

The harness compiles a fresh Std-only Lean 4.27 closure with warnings as errors,
independently restates all thirty public theorem signatures plus
`acceptedWitness`, checks every theorem's permitted transitive axioms, and pins
the eighteen admission clauses and nineteen witness fields. The placeholder
scanner found zero matches. Ruff and focused MyPy checks passed.

The accepted witness has two assets, custody of 10 atoms, a separately backed
6-atom claimant liability, a prior replay entry and an existing oracle
observation. The actual Python custody module, public lane coordinator and
single-occurrence global projector produce adjacent height 7 to 8 states. The
restricted allocation checker accepts their binding. These are synthetic
contexts with computed runtime roots; no authenticated snapshot is supplied.

Expected tables and metadata are input-derived with explicit supplied root
commitments. Lean receives those same opaque commitments. Observations include
every modeled field: all lane roots/releases/enabled flags, context metadata,
the complete consumed occurrence, economic tables, oracle identity/root/status,
and empty terminal/outbox lists. Replay and oracle functions are observed at
specified present and absent keys. This is finite correspondence evidence,
not equality of arbitrary runtime registries or canonical bytes.

Controls cover exact leaf rejection; stale occurrence context; consumed replay
key; wrong height; wrong private-port pre root; positive fee whose owner is the
sender; malformed occurrence type; and the u64 maximum neighbor and overflow.
Projector refusals preserve canonical pre-state, effect and occurrence inputs.
Fee-mirror refusal preserves its effect input. Constructor refusal remains
distinct from a leaf rejection.

The occurrence-ID alias fixture changes the pre-state root and reaches an
earlier context mismatch. It does not independently reach the runtime
occurrence-ID reuse guard. Lean separately refutes the corresponding admission
clause and demonstrates a noninjective successor without it. That model control
does not prove cryptographic unreachability or close the runtime guard gap.

Two private source mutants omit replay insertion or omit height advancement.
Definitions-only probes execute their incorrect observable result; compiling
the complete mutant fails within `successor_replay`, with syntax and
unknown-identifier failures excluded. This is a bounded constructor mutation
check, not a production mutation score.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_global_successor_v1.py
python3 -m ruff check \
  tests/formal/test_lean_asset_transfer_global_successor_v1.py \
  experiments/v3_transfer_global_successor_v1/render_evidence.py
python3 -m mypy tests/formal/test_lean_asset_transfer_global_successor_v1.py
python3 tools/scan_lean_proof_placeholders_v1.py --json \
  lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean
python3 -B -m experiments.v3_transfer_global_successor_v1.render_evidence
```

The proof SHA-256 is
`8375d3cbd6bf4bd4c911527a03de5d12b7bb21df0b0135cd1dd0d1951e60dc56`.
The renderer pins the declared sources and harness in
`THV1-20260906-transfer-global-successor-v1.json`. Rendering executes no proof
or test and grants no authority.

## Design consequence and remaining obligations

The construction provides a proof-level example of one transition owner with
derived state and effects. This is a useful direction for simplification while
preserving the existing relation. It is not an implemented runtime refactor or
a proof of design minimality. Any such refactor must preserve exact outcomes,
rejection purity, canonical commitments and authority boundaries, with an
implementation-refinement argument. Independent checking remains necessary
where a caller supplies proposed state or effects.

Ledger-held token amounts and claimant liabilities remain separate views.
The lane physical total counts balances plus custody; the global total also
counts reserves. A withdrawal claim describes entitlement to existing holdings.
Adding it as another holding would double-count the backing tokens. These are
digital ledger quantities, not evidence of off-chain physical reserves.

This result does not establish universal Python/Rust/compiler refinement,
canonical decoding and hashing, resource ceilings over all runtime collections,
an executable global admission checker, command-signature authority or current
policy provenance. Nonempty terminal mappings and the other lane lifecycles
remain separate obligations. The V2 mathematical relation's name does not imply
general correspondence to every runtime V1 or V2 path.

The isolated custody receipt-admission and publication adapters already exist;
their fixtures use synthetic RISC0 endpoints. Native Rust custody preparation
also exists, while its RISC0 guest, measured image and genuine receipt remain
unqualified. This theorem supplies no cryptographic receipt, authenticated store
head, writer authority, durability or deployment qualification.

Full Lake/Mathlib, Cargo, guest, GPU and deployment gates were not run. Complete
lane and cross-lane semantics, runtime refinement, release qualification and the
full V3 plan remain open.
