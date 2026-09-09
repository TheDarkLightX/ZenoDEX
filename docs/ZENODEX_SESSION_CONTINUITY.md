# Continuing ZenoDEX V3 work

This is the durable entry point for a resumed session. It selects work and
evidence; it grants no release, migration, or publication authority.

## Recover the subject before editing

1. Locate branch `codex/whole-program-v3-20260904` using `git worktree list`.
   Read its `git status --short` and `git rev-parse HEAD`. Preserve unrelated
   dirty files and active writers. Do not substitute the main checkout's older
   files when an integration file is missing there.
2. Read [the completion plan](ZENODEX_COMPLETION_PLAN.md), its
   [work graph](research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json), and the
   [acceptance index](research/ZENODEX_V3_ACCEPTANCE.json). Run
   `python3 tools/v3_acceptance.py` for its current mapping status. Inspect the
   actual specification, caller and test for the next unmet behavior before
   choosing implementation or proof work.
3. Record one concrete acceptance condition and exclusive file ownership for
   the next patch. Finish its integrated test before expanding adjacent work.
   A blocker should name the missing input or executable condition.

## Semantic precedence

- Plan **V3** governs completion. Its precommit rejection rule supersedes the
  historical nonce/history-consuming rejection rule.
- **GlobalSettlementABI V2** is a separately versioned successor ABI with
  stronger occurrence, asset-origin and liability bindings. A component's
  `_v1` or `_v2` suffix is not a global semantic precedence rule.
- Reuse the [custody transfer contract](specifications/ASSET_TRANSFER_CUSTODY_SEMANTICS_V1.md):
  ordinary transfers preserve complete custody rows and claimant rights;
  physical holdings reconcile with supply; liabilities are not additional
  physical holdings. Preserve that behavior in the successor.
- Historical bytes and verification remain available. Intentional wire or
  semantic changes require an explicit successor, compatibility evidence and
  the applicable migration/activation checks. An existing publisher is not a
  reason to retain superseded economic semantics.

## Acceptance discipline

For each required workflow, connect its specification to concrete tests of the
selected implementation and its consumer. Keep inventory, test mapping, fresh
replay, formal refinement and release qualification as separate observations.
Missing or skipped acceptance evidence keeps the corresponding obligation open.

Check both directions of functional adequacy: required valid states can be
represented and required authorized commands succeed; invalid commands reject
with the specified complete no-effect outcome. A proof about accepted results
alone can hold for an implementation that refuses every required operation.

Carry applicable acceptance cases into successor implementations. Use independent
expected results, stateful histories and requirement-linked mutants. Test the
actual publication path when claiming publication behavior; synthetic receipts
do not qualify measured guests or cryptographic verification.

At handoff, update the acceptance evidence and the concrete next obligation.
Report completed behavior, exact tested subject, remaining gaps and unrun gates.
Do not count new wrappers, documents, tests or proof files as closed capabilities.
Do not recreate a tracker or repeat broad reviews when the next failing
acceptance condition is already known.

## Current implemented behavior and remaining obligations

The explicit `AssetLaneCustodyStateV2` successor represents a valid supply split
across accounts and custody. Its Python and Rust coordinators reuse the existing
V2 transfer, issue and burn leaves, preserve complete custody rows and dormant
asset identities, and bind completed physical totals through a new state root
and receipt. The global consumer checks actual complete tables, unchanged
claimants, occurrence/replay and producer bindings. Historical account-only
state and receipt formats are unchanged. Output authority remains `NONE`.

The Python custody codec now accepts only the exact canonical successor state,
checks all six row arrays before constructing their component tuples, and
turns malformed JSON, excessive nesting, huge integers and lone surrogates into
typed decode failures. Python and Rust expose
`transition_asset_lane_custody_bytes_v2`: an explicit leaf route selects the
existing command shape, then context, state and command decode in that order.
Each input retains its independent 1 MiB limit. Unknown commands retain their
economic no-op outcome, and economic faults are not hidden as parser failures.
The byte path has exact golden controls and reaches the actual global consumer.

The Python and Rust statement producers now execute the custody coordinator and
actual global refiner, preserve typed economic rejection, and emit the exact
module journal plus the refiner's two global roots. The
[statement contract](specifications/ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_V2.md)
also defines the bounded five-component input frame. Python encodes it; Rust
checks its complete structure, decodes all components and prepares the statement.
Five retained economic vectors agree on frame hashes and exact statement bytes.
The flat guest in `zk/asset_lane_custody_global_risc0` uses that same Rust entry,
bounds stdin allocation and requires EOF. Its native binary compiles and its
transport tests run; the actual zkVM image and receipt remain unqualified.

The conditional Python receipt adapter now reconstructs the concrete verifier
configuration before preparing this statement. It preserves economic rejection
without verifier launch, passes only locally prepared bytes to the existing
measured transport, and returns those bytes after verification. The fixed Rust
endpoint statically selects this guest's compiled ELF/image; its executable
requires the actual methods build. Native codec tests have no fallback image.
This connects the source path, while trusted executable selection, actual
rebuilt-image verification and every publication authority remain open.

The Lean `AssetLaneCustodyRefinementV2` lift establishes constructed finite-row
accounting and custody preservation with selected leaf models, plus concrete
legal-state acceptance controls. It does not prove every runtime constructor,
codec, receipt, guest, authentication or publication obligation. The global
consumer currently requires empty reserves and the lane's complete asset
tables. The specified sender-as-fee-owner refusal remains in global admission.

Replay the current bounded implementation before building on it:

```bash
python3 tools/v3_acceptance.py --validate
python3 tools/v3_acceptance.py --replay custody-successor-v2-python
python3 tools/render_asset_lane_custody_v2_golden.py --check
python3 tools/render_asset_lane_custody_statement_v2_golden.py --check
python3 -m pytest -q tests/core/test_asset_lane_custody*_v2.py tests/tools/test_v3_acceptance.py
python3 -m pytest -q tests/integration/test_asset_lane_custody_receipt_verification_v2.py tests/integration/test_global_receipt_verifier_v1.py
cargo +1.87.0 test --locked --manifest-path zk/global_settlement_abi_v2/Cargo.toml
cargo +1.90.0 test --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml -p zenodex-asset-lane-custody-global-guest --lib
cargo +1.90.0 check --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml -p zenodex-asset-lane-custody-global-guest --bin zenodex-asset-lane-custody-global-guest
cargo +1.90.0 test --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml -p zenodex-asset-lane-custody-global-risc0-host --lib
```

The CI workflow declares these Python regressions, the standalone Rust crate
and native guest/host checks; hosted execution is not claimed here. Structural
acceptance validation rejects changed pins, deleted or
duplicated requirements, unsupported evidence reuse, and fabricated claim
states. A successful replay does not fill unrelated capability mappings.

Next, qualify the rebuilt receipt path and complete explicit V2 authentication
and publication admission; prove the resulting store-authority bindings. The
review at `89e817d8` found that existing real module/coordinator/route guests and
durable publication consume ABI V1. The V2 flat guest source now recomputes the
existing custody coordinator and global relation and commits their exact V2
statement. Its conditional Python adapter now uses the existing measured
transport, and its fixed Rust verifier source selects the new compiled image.
Qualify the actual rebuilt image and genuine receipt, then the context
admission and publication consumer. Do not restart statement or framing
design; their defined subject and five-case native evidence are retained.
Define explicit V2 authentication and durable state admission. The existing V1
authentication module signs a different command-hash domain and binds exact V1
profile, intent and occurrence types; those cannot authenticate V2 through
casts. Matching an
occurrence's predecessor root establishes consistency; the publisher must
acquire and revalidate the committed predecessor to establish its authority.
Do not cast V2 states or occurrences into V1 types. Do not count the native
global relation as a mounted publisher. Carry the custody cases through that
integration. Independently,
the acceptance index's first mapping gap is Tau-originated asset registration:
inspect its existing implementation/tests before recording linkage or choosing
a repair. A missing mapping does not mean an implementation is absent.

Full BDD/ATDD linkage, all lane lifecycles, runtime refinement and release gates
remain open. `python3 tools/v3_acceptance.py --check` deliberately exits nonzero
while required mappings remain missing; do not weaken it to report completion.

## Verification limits retained for the next session

The integration run passed 144 selected Python tests (custody, existing V2
leaves/coordinator/global refinement, runtime observations and index tests),
118 standalone Rust tests, and ten exact Python/Rust vectors. Targeted Lean
4.27.0 compilation, typed consumers, eleven axiom audits and four rejected
mutants passed against twenty revalidated cached source/object dependencies.
The full fresh Lean fixture chain and hosted CI execution were not run.

The production-boundary checker passed its scoped checks. Broader qualification
is still blocked: the local critical-quality script lacks `pytest-cov`, raw Rust
clippy reports the existing `too_many_arguments` finding in
`global_refinement.rs`, and the claims registry references missing
`tools/check_derivatives_authorization_matrix.py`. No gate was weakened and no
live publication, migration or authority activation was performed.

The subsequent input-boundary run passed 130 selected Python tests, 125
standalone Rust tests, the ten golden vectors and the existing hygiene gate's
64 selected Python cases. Ruff, focused mypy and scoped clippy passed. No new
Lean, Kani, ESSO, guest build or genuine receipt was run for this decoder patch.

The statement/frame integration passed 145 selected Python tests, 132
standalone Rust tests and five native guest transport tests. Native guest binary
checking, Ruff, focused mypy, formatting and changed-surface clippy passed.
The full standalone `--all-targets` clippy command additionally found the
pre-existing constant-assertion warning at `tests/resource_bounds.rs:568`; that
test was preserved. Existing `too_many_arguments` remains allowed only on the
scoped clippy command line. The statement hygiene packet names a mechanical
global-refinement-bypass mutant, executable with the existing mutation ledger:

```bash
python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260909-custody-statement-v2 --rev HEAD
```

The [retained mutation replay](../tests/evidence/asset_lane_custody_statement_v2_mutation_20260909.json)
against implementation commit `abbade2d0cb3e7f59825fffef94d8e80a41058d5`
passed its unmutated control and killed the global-refinement bypass mutant
(one killed, zero survivors or replay errors). The hygiene runner separately
passed 31 selected Python cases; the production-boundary audit returned
`ok=true`. Temporary mutation copies and the new guest's regeneratable native
build cache were removed after verification; source, locks and evidence remain.

These are native integration results, with independent read-only Astra review.
No new Lean, ESSO, Kani, actual guest image, genuine receipt, host proof service,
authentication, durable store admission or production qualification was run for
this batch. Native transport tests do not execute the guest's zkVM abort/commit
branches. The guest build reuses pinned RISC0 3.0.6 and refuses placeholder
method generation; actual proof qualification still needs suitable compute.

The conditional receipt integration passed 197 selected Python tests, including
the new adapter and existing measured transport, and nine native Rust tests
(five guest transport, four host codec/fake-refusal). Its hygiene gate passed
17 cases covering nine critical paths. Ruff, focused mypy, host Clippy and
formatting passed; the production-boundary audit returned `ok=true`. Independent
read-only Astra review found no blocker in this conditional contract.

The same 52 receipt transport tests also passed with parent
`RISC0_DEV_MODE=1`, while the child environment remained `RISC0_DEV_MODE=0`.
A separate native SDK diagnostic with dev mode enabled panicked because the
required `disable-dev-mode` feature was set; it did not accept the fake receipt.
The default host build cannot produce the verifier binary without the
`compiled-guest` feature and real methods build. Actual fixed-binary execution,
new-image proof verification, V2 authentication and durable admission remain
unrun. No new Lean, Kani or ESSO proof is attributed to this transport patch.

The [receipt-adapter mutation replay](../tests/evidence/asset_lane_custody_receipt_v2_mutation_20260909.json)
archived implementation `c9e1227e23a82596f67f7b25331eae2acde76e57`.
The unavailable-verifier control passed, and removing the verification call
was killed (one killed, zero survivors or errors). Replay it with
`python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260909-custody-receipt-v2 --rev c9e1227e23a82596f67f7b25331eae2acde76e57`.
The temporary mutation copies and 810 MiB native custody build cache were
removed after the checks; the six unrelated dirty files remain unchanged.

Complexity review uses the existing simplification skill and exact outcome
checks. Radon 6.0.1 found high Python hotspots in snapshot decoding (152), the
operation dispatcher (116) and zUSD `step_multi` (83). The new byte entry is 6;
custody binding predicates reach 17. These are source metrics, not measured
overengineering or safety scores. Review retained the custody predicates because
their checks and rejection order have distinct obligations. Do not split
helpers, replace conjunctions with `all()`, or delete guards solely to lower a
score. The finite minimizer proves minima only for its declared guard-deletion
grammar and finite model, not arbitrary source programs.
