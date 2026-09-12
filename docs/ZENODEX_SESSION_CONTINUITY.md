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
4. Read the [code-value account](research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.md#code-value-account-september-9-2026).
   Before coding, name the existing capability/workstream and the acceptance
   change the batch should deliver. After coding, append its exact commit range,
   before/after behavior, source-bound evidence, and added/removed/net lines split
   into runtime, proof, tests, tooling and data/documentation. Include dependencies
   and generated artifacts; preserve unrelated worktree changes.
5. Compare affected score rows under the same denominator and rubric. Report the
   old/new scores and percentage-point changes only after evidence review and
   calculator validation; retain the previous scored subject. A partial advance
   can earn credit without closing a whole lane. Mark an unreviewed delta
   `NOT_RESCORED`; the last adopted aggregate estimate is unchanged. Do not
   turn missing reassessment into a measured zero gain.
   Record support work and regression repairs separately, with their concrete
   benefit and remaining delivery blocker. Review gates and test counts alone
   do not increase product credit.
6. Use those records when selecting the next batch. If code keeps growing without
   advancing the intended acceptance condition, reconsider the decomposition,
   reuse/simplify existing code, and finish the missing integration before adding
   adjacent machinery. Do not optimize percentages by weakening evidence,
   deleting required checks or changing weights. Use the existing
   [contribution report](research/ZENODEX_V3_PRODUCTIVITY.md) to record known
   runs across all contributing models, including failures and no-change work,
   and pinned resource observations when available. Shared gain counts once;
   missing data stays unknown. Append corrections and check the earlier
   manifest prefix. Report next-step acceptance value and quality alongside LOC.

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

## September 12: custody formal construction checkpoint

The [custody completion evidence](../tests/evidence/custody_recomposition_effect_plan_v2_20260912.json)
records the new finite-model result and its exact verified source. The
recomposition proof connects complete managed/unmanaged row reconstruction to
the existing mixed custody histories, including zero-supply identities. Reuse
the existing partition algebra; do not rebuild it.

The effect-plan proof consumes the actual finite transfer/managed leaf post,
reconstructs the complete modeled state, and establishes full state equality,
conservation and effect-plan admission for accepted transfer, issue and burn.
Rejected leaf outcomes return empty plans. The unchanged plan fields and the
single complete-state lane write are explicit conclusions. The bridge includes
unrelated managed siblings; selected-asset totals alone do not close this link.

These are Lean construction theorems with source-state premises. Complete roots
remain supplied observations, and the model retains origin keys rather than
all runtime origin fields. Python/Rust multiasset lifecycle cases and ten
leaf-to-coordinator completion examples provide bounded runtime evidence.
Universal codec, resource, runtime, journal and root correspondence remain open.
No runtime economics, rounding, wire formats or publication authority changed.

The narrowly reviewed amendment raises only the proof component for generic
transfer, managed issue and managed burn from 0.70 to 0.75. The carried advisory
formal-core estimate moves from 21.038% to 21.081% (+0.043 percentage points);
V3 remains 23.869%. Other scores and uncertainty bands are unchanged. These are
partial planning judgments, with no full lane or value-safety gate closed.

Keep the genuine guest/receipt acceptance condition below. Review full-state
and full-outcome theorem conclusions before the next fresh proof replay; do not
substitute a selected scalar projection for the complete constructor relation.
The claims-registry check still reports the inherited missing
`tools/check_derivatives_authorization_matrix.py`; this batch does not repair it.

## September 12: current isolated publication checkpoint

Source commit `3018ec0f133ea9388153544b45cbe8edfcab66d6` implements the fresh
isolated V2 publisher. Use
[its specification](specifications/ISOLATED_CUSTODY_PUBLICATION_V2.md) and
[pinned delivery evidence](../tests/evidence/isolated_custody_publication_v2_20260912.json).
`IsolatedCustodyPublisherV2` owns one SQLite store, both complete state values,
current authority, profiled signature/receipt admission and the atomic record/head
commit. Do not restart publisher, record, frame or role design. V1 bytes and the
M6 protocol remain unchanged; no live balance migration or activation occurred.

The immutable genesis pair and separately selected configuration determine the
V2 authority. Fresh open revalidates both and refuses a revoked writer.
Publication obtains its predecessor in one transaction, verifies the exact
request, then rechecks source and authority under the write transaction. The
commit closure is local to that verified call. A raw record/token entry point
was rejected after a reproducible development bypass; do not restore one during
refactoring. Exact retries include signature and receipt bytes. Complete
PRE/POST recovery, response-loss classification, competing writers, in-flight
revocation and interrupted genesis installation have retained tests.

The isolated store has no external effect dispatcher. It preserves the existing
outbox and terminal rows for these commands. Economic `history_root` stays fixed;
publication ancestry is the contiguous durable record chain. Recovery replays
complete economics and message bindings. It does not repeat cryptographic
verification or reselect historical authorization registries. Whole-file rollback
can restore old authority without an independent anchor. Honest publisher,
SQLite/filesystem and independently selected genesis/configuration are premises.

The next acceptance condition is a rebuilt custody guest and fixed verifier
accepting one genuine receipt for this exact statement and selected role, followed
by commit/reopen/exact-retry through this publisher. Measure legal-state cycle
fit against the admitted ceiling. Run heavy guest/proof work on suitable compute;
Runpod is currently unavailable. Do not substitute fake receipt fixtures for this
condition. Then discharge concrete store/runtime refinement, historical
verification, rollback resistance, finality, delivery ancestry and migration as
their own obligations. Full W06 and formal-core completion remain open.

This slice passed 209 distinct targeted Python cases and six archived mutation
rows, with no survivors or replay errors. The receipts in the storage tests are
protocol fixtures. The new source adds 1,275 runtime lines and 1,382 test lines;
135 specification lines and 269 hygiene-data lines are accounted separately.
No new proof or dependency is claimed. The reviewed W06-only amendment moves
the carried V3 estimate from 23.369% to 23.869% (+0.500 percentage points). Formal
core stays at 21.038%. Other rows and earlier unrescored work remain carried
forward; these are advisory estimates, not a whole-checkout reassessment. The productivity ledger records Luna implementation, Astra integration
and repairs, Daybreak review, and the refused external Fable launch.

The earlier [Fable sprint](research/ZENODEX_FABLE_SPRINT_20260912.md) delivered
the oracle preflight and native custody prover selector. Its stable-environment
and honest-IPC assumptions remain. Its then-missing V2 publication seam has now
been implemented above; its usage counters are historical observations.

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

The [existing hygiene runner](testing/TEST_HYGIENE_CONTRACT_V1.md) now has
`--replay-mutations` for committed selected evidence. Use it to execute declared
faults and controls; narrative declarations do not satisfy a mutation claim.
The PR template records the smallest alternative and jointly edited oracles.
These checks do not prove baseline-to-candidate equivalence or enforce an
independent reviewer. The source candidate wires the strict runner into the
host-required `test-hygiene` context; deployment and independent host approval
remain separate. This tooling work closes no economic capability.

The enforcement implementation at
`5b317f9a4d5682ed5291e62739f8eaac3db698d3` has a retained
[strict replay report](../tests/evidence/required_mutation_replay_gate_v1_20260909.json):
all six declared mutants were killed after passing unmodified controls, with
no survivors or errors. It selected 39 passing tests. Reproduce on that commit:

```bash
python3 tools/run_test_hygiene_gate_v1.py --base-ref f4239d23b38d65a44a6a5c9bb303e05108388b85 --replay-mutations --json
```

The combined checker/runner/ledger suite passed 58 tests. The full
`tools/run_critical_quality_gate.sh` passed its 433 acceptance and 852 critical
tests using the existing development environment selected through `PYTHON`;
the system interpreter alone lacked `pytest_cov`. These suites overlap.
Astra reviewed the integration and Daybreak independently reviewed the frozen
source and pins. Those model reviews supply no authenticated host approval.
Hosted CI, Lean, ESSO, Kani and RISC0 proof qualification were not run for this
assurance-tooling change. Resume the next economic obligation below.

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
rebuilt-image verification and production publication authority remain open.

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

V2 intent authentication now snapshots the candidate and sequenced occurrence,
checks profile-governed authorization, builds an explicit V2 signing message and
verifies it through an internally acquired sealed BLS verifier. It reuses the
unchanged profile and registry formats with explicitly selected V2 schema
contents. No caller-supplied backend or verifier handle can provide success.
The [authentication contract](specifications/ECONOMIC_COMMAND_AUTHENTICATION_V2.md)
defines the signed fields and the unsigned sequencer coordinates. Checking
returns no reusable authority and consumes no replay state.

The combined isolated consumer now authenticates the actual typed custody
command and conditionally verifies its statement within one owning call.
Candidate, command, context, custody/global disclosures and receipt configuration
are captured before BLS I/O. Valid signatures cannot substitute command bytes
or change claimant rows. The pure profile predicate now requires an ACTIVE
profile, its exact single-ASSET route and module, its authority epoch, and all
twelve predecessor lane release/enabled fields. Structural snapshot and profile
binding errors precede authentication;
signature failure precedes economic execution; authenticated leaf rejection
remains an exact no-effect result without receipt verification.

The selected custody role and fresh isolated publication consumer now exist;
the current checkpoint above selects their next qualification condition. Existing
real module/coordinator/route guests and the older durable publisher still consume
ABI V1. Keep the V2 flat statement and its explicit role separate. Native
relation tests and modeled trace induction do not establish universal runtime
refinement or production publication.

Independently, the acceptance index's first mapping gap is Tau-originated asset
registration. Its V2 core and golden/negative tests exist, with authority `NONE`,
but no integration caller or durable replay consumer was found. Normative UP-11
is `UNRESOLVED_POLICY_NOT_SELECTABLE` pending the stable Tau interface. Existing
tests can support a bounded component observation; they cannot close finality
policy or a mounted lifecycle. Do not recreate the existing core to fill a
mapping gap.

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

The V2 authentication integration passed 175 combined Python regressions;
the three artifact-dependent tests skipped in that default run each passed
in a separate configured run against the measured sealed Rust ELF. Those
include the new V2 message, existing independent BLS vectors and fresh deployed
binding. The unchanged native verifier was rebuilt offline from its verified
locked dependencies with Rust 1.87.0; five native protocol tests passed and the
release ELF reproduced the retained digest. The new Python test-hygiene packet
passed 53 cases across six critical paths. Ruff, focused mypy and the scoped
production-boundary audit passed. Astra and Daybreak reviewed the conditional
contract; Terra implemented its pure types and message preparation.

The combined run initially found duplicate core/integration test basenames;
the integration test is now `test_isolated_economic_command_authentication_v2.py`.
No runtime guard or evidence threshold was weakened. CI declares the Python
regressions, including an explicitly skipped native test when no measured
artifact is configured. The authentication packet declares three mechanical
mutants: ungoverned signer-registry acceptance, foreign message-schema release
acceptance and ignored cryptographic rejection. The
[retained authentication mutation replay](../tests/evidence/economic_command_authentication_v2_mutation_20260909.json)
archived implementation `3d4301c685d42890eb41bfed76c51b0776f940c0`, passed
all three unmutated controls and killed all three mutants, with zero survivors
or replay errors. Replay with
`python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260909-command-authentication-v2 --rev 3d4301c685d42890eb41bfed76c51b0776f940c0`.
The temporary archive and mutation workspaces were removed after verification.

The combined authenticated-custody entry passed 64 selected integration cases;
the two native cases skipped in that default run were executed separately with
the measured BLS artifact. The new native case covered all five custody
lifecycles and a foreign-key rejection for each, with receipt exchanges still
explicitly mocked at the protocol boundary. Its hygiene packet passed 19 cases
across three critical paths. Ruff, focused mypy and the scoped production-boundary
checker passed. Astra reviewed the composition contract and Daybreak reviewed
the exact source/tests, including the independent native BLS transport alias.
No receipt, profile or publication authority was granted.

The combined entry's packet declares mechanical removals of BLS authentication,
economic snapshot use and receipt-configuration snapshot use. Its
[retained composition mutation replay](../tests/evidence/authenticated_asset_lane_custody_v2_mutation_20260909.json)
archived implementation `f8b8dd99836dc1d0f6f30eb8b5166afcdf2687c3`, passed
both distinct unmutated controls and killed all three mutants with zero
survivors or replay errors. Replay with
`python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260909-authenticated-custody-v2 --rev f8b8dd99836dc1d0f6f30eb8b5166afcdf2687c3`.
Temporary mutation workspaces were removed. Full guest proof generation and genuine
receipt qualification still require suitable compute; no new Lean, ESSO or Kani
proof is attributed to these integration changes.

The next isolated increment mounts
`require_asset_lane_custody_profile_binding_v2` before BLS I/O. Its retained
baseline had five valid lifecycle controls pass and three coherent metadata
regressions fail to reject: foreign writer epoch, custody module and another
lane's release ID. After mounting, 77 selected integration cases and nine direct
predicate cases passed; the hygiene gate replayed 29 cases across four critical
paths. The native sealed BLS test separately passed all five economic cases and
foreign signatures, with RISC0 exchanges still protocol fixtures. Ruff, focused
mypy and the scoped production-boundary checker passed. The other optional
native test in the combined default run was not repeated in this increment.
Astra reviewed the predicate contract, Terra implemented its core/tests, and
Daybreak independently reviewed the final source and semantic controls.

The binding admits matching enabled other lanes and unchanged retained disabled
roots. Existing accepted global refinement establishes successor profile and
lane-metadata preservation; no redundant successor predicate or new authority
handle was added. The consumer's inherited long signature and body remain to
keep snapshot capture and verifier order visible in one call. Direct tests were
simplified by removing a redundant profile builder and repeated malformed-input
branches without changing their nine cases. The
[retained profile-binding mutation replay](../tests/evidence/asset_lane_custody_profile_binding_v2_mutation_20260909.json)
archived implementation `c966636ffa6d4ff036fa6d2e27525f577f1fd4d4`, passed all
four unmutated controls, and killed all four declared guard-removal mutants with
zero survivors or errors. Replay with
`python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260909-custody-profile-binding-v2 --rev c966636ffa6d4ff036fa6d2e27525f577f1fd4d4`.
Its temporary archive and mutation copies were removed. Full guest qualification,
publication, Lean/ESSO/Kani/runtime refinement and whole-program completion remain
open.

Complexity review uses the existing simplification skill and exact outcome
checks. Radon 6.0.1 found high Python hotspots in snapshot decoding (152), the
operation dispatcher (116) and zUSD `step_multi` (83). The new byte entry is 6;
custody binding predicates reach 17. These are source metrics, not measured
overengineering or safety scores. Review retained the custody predicates because
their checks and rejection order have distinct obligations. Do not split
helpers, replace conjunctions with `all()`, or delete guards solely to lower a
score. The finite minimizer proves minima only for its declared guard-deletion
grammar and finite model, not arbitrary source programs.


## Custody trace and derived witness increment, September 9

`AssetLaneCustodyTraceV2.lean` now derives full row representability through
arbitrary finite transfer/issue/burn histories from initial row admission plus
static policy-selection and command-width premises. Custody rows,
registration and policy frames are preserved exactly. The fresh Lean suite
passes eight checks, including independent concrete tables, five false-law
refusals and matching Python prefixes. It does not prove actual runtime
authentication, replay, parser, resource-ceiling or publication refinement.

The Python/Rust `derive_asset_lane_custody_global_post_v2` constructs the complete
successor and then requires the existing refiner. The Python
`prepare_asset_lane_custody_global_prover_input_v2` now prepares all five existing
guest frames from predecessor and command alone. It preserves their exact hashes
and returns typed leaf rejection without a proving frame. This is pure witness
preparation; no publisher was mounted.

Opus implemented the constructor twins/tests in four exclusive files. Astra
implemented the trace proof and prover-input composition; independent Astra and
Daybreak reviews accepted the scoped final subjects. The
[verification record](../tests/evidence/asset_lane_custody_trace_successor_v2_20260909.json)
retains source hashes, commands, initial test/type errors and repairs, review
subjects, and CLI-recorded usage. Final hygiene passes 24 new core cases; the
native crate passes 146 tests; combined core/integration passes 53 with one optional
measured-native BLS case skipped. Full Clippy retains an unchanged argument-count
failure. No fixtures, proof claims or admission gates were weakened.

The explicit custody role was implemented in the September 10 increment below.
The current September 12 checkpoint adds store-owned publication; the real
receipt and selected build remain unqualified. The ABI V1 durable publisher
does not automatically accept this V2 statement. Do not treat model trace induction or a constructed witness as
production publication or universal runtime refinement.

### September 10: selected custody role and bounded proof producer

Commit `fe7f60c49bd6e75d65c5f6ed3ea747cc70217531` adds the separate custody role,
same-call authenticated receipt admission and a feature-gated proof producer.
The independent expected role root selects the profile, epoch, schema, image,
endpoint implementation and build commitments. The shell snapshots inputs,
authenticates the actual command, recomputes the statement and uses measured,
sealed receipt verification. It returns ordinary bytes or the existing typed
economic rejection. V1 profile image slots and receipt ports retain their meaning.

The [delivery record](../tests/evidence/profiled_asset_lane_custody_v2_20260910.json)
binds the exact subject, participants, repaired findings and unrun obligations.
Its gate passed 41 Python cases and killed all four archived guard-removal
mutants; Terra's native host run passed nine tests and strict Clippy. Daybreak
reviewed the final source. Luna's manifest-alias defect and the missing prover
session limit were repaired; the native environment test checks construction
only. Root also removed duplicate manifest copying and repaired three test setup
errors. The acceptance index's stale predecessor-constructor hash was refreshed
without changing capability mappings or scores. The task-owned 731 MiB native
build cache was removed after checking ownership and active processes.

No actual guest image, feature-gated producer binary, genuine receipt or new
formal refinement theorem was qualified. The expected role root and active
profile remain trusted isolated configuration. The 16,777,216-cycle work ceiling
has no measured legal-state fit. The subsequent September 12 sprint guards
unsupported SDK selection, and the current checkpoint adds isolated publication.
The genuine rebuilt receipt and remaining production/refinement obligations are
still open. Keep aggregate progress `NOT_RESCORED` until the existing assessment
is deliberately rerun.
