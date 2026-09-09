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
python3 -m pytest -q tests/core/test_asset_lane_custody*_v2.py tests/tools/test_v3_acceptance.py
cargo +1.87.0 test --locked --manifest-path zk/global_settlement_abi_v2/Cargo.toml
```

The CI workflow executes these Python regressions and the standalone Rust
crate. Structural acceptance validation rejects changed pins, deleted or
duplicated requirements, unsupported evidence reuse, and fabricated claim
states. A successful replay does not fill unrelated capability mappings.

Next, connect the successor to explicit input decoding and the selected
receipt/verifier and publication path; prove and test the resulting source and
store-authority bindings. Do not count the native global relation as a mounted
publisher. Carry these custody cases through that integration. Independently,
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
