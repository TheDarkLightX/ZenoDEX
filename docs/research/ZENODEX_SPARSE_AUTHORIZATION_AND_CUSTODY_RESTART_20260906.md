# Sparse debit authorization and custody activation restart

This increment records evidence for two reviewed changes on base
`40d6b89ec6037bea7a57316aa84a62c286be2f23`: a Lean authorization and frame
theorem file for the constructed sparse selected-policy transfer, and a
custody fixture repair with a same-process publisher close, reopen, exact
retry and adjacent forward epoch. It adds a Lean proof artifact, a formal
harness, a test-only custody fixture and lifecycle evidence repair, two
append-only hygiene packets, one focused generator and this note. Production
code is unchanged, and no earlier packet is rewritten.

## Sparse debit authorization

`lean-mathlib/Proofs/AssetTransferSparseAuthorizationV1.lean` imports the
existing sparse trace model and proves ten theorems over the actual
constructed step and history. Amounts are observed in finite `amountAt` rows.
The debit conclusion follows from the constructed balance equation and the
leaf's sender/context guard. No output representation, verified result or
principal enumeration is assumed.

```text
CanonicalBalances pre
0 <= command.amountAtoms
0 <= policy.transferFeeAtoms
(step input).verdict = accepted
post(owner, asset, domain) < pre(owner, asset, domain)
=> owner = command.sender = context.subjectId
   and asset = command.asset and domain = accounts
```

`accepted_non_sender_nondecreasing` gives every non-sender owner a
nondecreasing amount at every denomination. `step_outside_frame` fixes foreign
assets, foreign domains and owners outside every transfer role, for accepted
and rejected attempts, without any sign premise. The history theorems lift the
step result through the actual `run`: any endpoint decrease identifies a
request in the executed prefix whose step was accepted, whose declared sender
equals both its context subject and the debited owner, and whose own step
already shows the decrease. Rejected attempts stay in the request list and
contribute nothing. Two demo theorems execute the existing zero-deleting
example and a rejected-then-accepted two-request history.

### Premises and counterexamples

Nonnegative command amount and selected fee are explicit premises. The
abstraction's zero-amount guard excludes only zero, and its fee width guard
admits negative integers, so acceptance alone supplies neither lower bound.
Two retained model examples show both premises are load-bearing: a `-1`
amount reverses a one-atom transfer and debits the recipient, and a `-1` fee
debits a distinct one-atom fee owner. The runtime constructors reject these
values; the harness checks five controls (`-1`, `-2^127`, `True`, `False`,
`2^128`) against the exact constructor messages. These are model-premise
counterexamples and do not establish runtime defects.

Three earlier harness failures (root replay nine passed, three failed) were
test authoring errors: a reserved Lean binder name, a multiline JSON decoder,
and a false expectation that alice decreases under every fee owner. No
theorem statement was weakened. Under the alice fee-owner history, alice
collects every fee and ends above her initial amount, so only bob's key meets
the endpoint premise there.

### Harness and outcomes

`tests/formal/test_lean_asset_transfer_sparse_authorization_v1.py` compiles
the captured twelve-module closure with Lean 4.27.0 and warnings treated as
errors, restates all ten theorem signatures in an independent consumer, and
limits transitive axioms to `propext`, `Classical.choice` and `Quot.sound`.
It checks the `Proofs.lean` import and pins the two Lean and two Python
subjects by SHA-256. A thirteen-case single-step corpus compares the Lean
observer with the actual Python transition at alias, zero-fee, reversed-role,
zero-deletion, u128 holding, i128 effect, overflow, unauthorized, zero-amount
and insufficient-balance boundaries. An independent oracle sums endpoint
amounts per key, requires every decreased key to name the declared sender,
context and denomination, and requires every unrelated key to be unchanged.
Three nine-attempt histories with five accepted transfers each, one per
fee-owner class, compare complete per-step observations and the endpoint
against signed-event sums. Two conserving monkeypatched runtime mutants, a
subject-guard bypass and a reversed debit, preserve totals and are caught by
that oracle.

The root independent replay recorded `12 passed in 47.69s`; the Fable
harness run also recorded 12 passed. Ruff and single-file MyPy passed on the
harness. The proof hash is
`91d41486e814f80a876746a1d8a542daeda77599415792b0915f4a2fccc495fa` and the
harness hash is
`389dc104374baeb483b9f96b543dfa4f8856ab4e7d923c7af165d515496d68d4`.

## Custody activation restart

The custody fixture in
`tests/integration/custody_asset_receipt_pipeline_fixtures_v1.py` now freezes
one `CustodyAssetReceiptActivationV1` context: profile, policy registry,
authorization, signature-verifier and transfer-policy registries, signature
manifest, release and artifact path, the initial-state admission and the
source state. A forward epoch passes that context with a later state and a
new nonce. The forward path refuses semantic-root overrides, rebuilt
signature coordinates, a different artifact, rebound liabilities, mismatched
custody atoms, and a later state supplied without an activation.

The earlier forward path regenerated the GENESIS source manifest and policy
root from the later state instead of reusing the original activation, and the
test rebuilt admission from the candidate's own pre state. A forward epoch
therefore bound itself to a regenerated profile rather than the immutable
activation. The repair is to test construction; no production defect is
claimed and no publisher, journal, allocation or admission source changed.
The forward-fixture test was written first: against the pre-fix fixture it
failed with `AttributeError: '_Fixture' object has no attribute 'activation'`
(one failed, five deselected). This AttributeError demonstrates that the
pre-fix fixture lacked the activation API; it is not a semantic production
failure.

`test_custody_activation_reopens_and_commits_adjacent_forward_epoch` runs one
SQLite path through this history in one process:

```text
create(E1) -> COMMITTED, head == prepared bundle head; close
open       -> head == E1 head; exact E1 retry -> ALREADY_COMMITTED with the
              same head and published epoch, store rows unchanged; close
open(E2)   -> E2 built from the same activation object and the E1 post state
              with nonce 2 and the same admission object;
              COMMITTED with source_publication_id == E1 publication id,
              pre_state_root == E1 post_state_root, height + 1, sequence + 1;
              current head sequence "2" and exactly two exact epoch rows;
              exact E2 retry -> ALREADY_COMMITTED, store unchanged; close
```

Both epochs keep custody `(custodian, USD, vault, 7)` and claimant liability
`(alice, USD, vault, 7)` unchanged from pre to post state.
`test_forward_epoch_fixture_reuses_immutable_activation_context` checks the
forward candidate's pre state, profile, policy and registry identities. The
reopen history uses the Python BLS backend. The sealed standalone BLS binary
remains the existing separate positive case, selected only when
`ZENODEX_BLS_VERIFIER_TEST_BINARY` names the artifact with SHA-256
`597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee`.

The root host replay of the isolated custody pipeline and custody publisher
files with that binary recorded `14 passed in 18.69s`. Daybreak independently
reviewed the fixture at
`70ede1d505f42d3bfbf92c935ffc109a61ce6dae394d9621d4579949fd1b656e` and the
test at `203869aa5c88c5ca934aa52857b5fbe5aeb442137b66457f6bf315d06cc033e4`,
and recorded two focused lifecycle tests passed in 5.73s with no blockers.

## Commands

From the repository root, the sealed case requires a caller-supplied binary.
Use a portable path placeholder whose SHA-256 is
`597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee`:

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_sparse_authorization_v1.py
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/qualified/zenodex-economic-command-bls-verifier-v1 \
python3 -B -m pytest -q -p no:cacheprovider \
  tests/integration/test_isolated_custody_asset_receipt_pipeline_v1.py \
  tests/integration/test_global_economic_custody_pipeline_v1.py
python3 -B -m experiments.v3_authorization_restart_v1.render_evidence
python3 -m ruff check experiments/v3_authorization_restart_v1/render_evidence.py
git diff --check
```

The generator writes
`tests/evidence/test_hygiene/THV1-20260906-sparse-debit-authorization-v1.json`
and
`tests/evidence/test_hygiene/THV1-20260906-custody-activation-restart-v1.json`.
It reuses the existing `_render` helper, pins the changed proof, import,
test and fixture paths together with their runtime, refinement and trace
dependencies, and touches no earlier packet. Rendering records declared
subjects; it runs no proof or test and qualifies no release. A sealed-backend
run without the qualified binary skips and supplies no evidence.

## Remaining obligations

No signature authenticity theorem, selected-policy membership proof, or
metadata, height and replay admission proof exists; equality with a supplied
context subject is not authenticated command authority. Finite corpus and
history comparisons do not prove universal Python, Rust or compiler
refinement. RISC0 receipt replies and release coordinates are synthetic; the
current genuine custody guest chain, the whole formal core, live activation
and production qualification remain open. Close and reopen happen in one
process on one path; killed-process recovery, rollback, migration and writer
fencing are not exercised. Initial claimant test rows do not approve
production claimant or migration policy.
