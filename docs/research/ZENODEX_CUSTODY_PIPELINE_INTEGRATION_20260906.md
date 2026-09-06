# Isolated custody receipt pipeline

This W06 increment connects the reviewed custody successor receipt entry to
the existing isolated publisher through a fixed pipeline factory. It retains
the one-occurrence limit. Genuine guest receipts, qualified releases, initial
claimant policy, migration and production publication remain open.

## Invariant and authority

The two existing factories retain legacy module semantics. The two additive
custody factories fix custody semantics and one of the existing signature
backends: Python BLS with its loaded-code integrity premise, or the measured
standalone BLS executable. No public argument selects transition functions,
receipt callbacks, an opaque witness, or an arbitrary semantics mode.

The private factory registry owns the selected profile, policy, deployment,
signature verifier, measured receipt ports and a closed semantics enum. Each
verification snapshots raw inputs, binds the signed intent to the occurrence,
and checks the custody specification root before recomputation. The module
receipt verifier independently rechecks the exact accepted output and journal.
Coordinator and route verification retain their existing interfaces.

The publisher continues to acquire its predecessor from the journal, compare
the exact mounted policy, run allocation admission, verify the epoch receipt,
and commit the complete bundle with the existing writer capability and CAS.
The native route preparation value is ordinary data and supplies no authority
to this path.

Custody and claimant ownership are separate obligations. Existing allocation
admission derives entitlements from the committed predecessor's liabilities.
It requires exact per-asset and custody-domain coverage and preserves the full
claimant partition. Tests explicitly precommit their claimant liabilities; no
rule assigns ownership merely because a custody balance exists. Missing
coverage must remain an `ENTITLEMENT_COVERAGE_DRIFT` refusal before epoch proof
verification and publication.

## Evidence and scope

Root replay passed seven custody pipeline cases and five publisher cases,
including the measured standalone BLS executable. Thirty-five legacy pipeline
cases and 125 shared publisher, receipt and allocation cases passed; the two
existing sealed-BLS cases also passed on the host. Ruff, focused MyPy,
production-boundary checks and the critical quality gate passed. The latter
replayed 433 acceptance and 834 critical cases, with 89% coverage on its scoped
suite; those counts do not measure V3 completion.

Two disposable-process mutants were killed by the named semantic tests:

- Bypassing the publisher allocation checker let uncovered custody publish;
  `test_missing_or_mismatched_claimant_backing_rejects_before_epoch_and_commit`
  failed because the required refusal disappeared.
- Changing the custody factory's fixed selection to legacy semantics made
  `test_nonzero_custody_uses_exact_global_rows_and_feeds_allocation` fail on the
  independently retained exact module receipt statement.

Focused replay commands, from the repository root:

```bash
python3 -m pytest -q tests/integration/test_isolated_custody_asset_receipt_pipeline_v1.py
python3 -m pytest -q tests/integration/test_global_economic_custody_pipeline_v1.py
python3 -m pytest -q tests/integration/test_isolated_asset_receipt_pipeline_v1.py
python3 -m pytest -q tests/core/test_asset_transfer_custody_receipt_verification_v1.py
python3 -m pytest -q tests/core/test_asset_transfer_epoch_allocation_v1.py
python3 -B -m experiments.v3_custody_pipeline_v1.render_evidence
```

The sealed-backend tests require an explicitly selected checksum-qualified
binary through `ZENODEX_BLS_VERIFIER_TEST_BINARY`; skipped execution supplies no
evidence. A sandbox that prevents executing a sealed descriptor must report
that limitation rather than substitute unmeasured execution.

RISC0 process replies and release coordinates in these tests are synthetic.
The successor fixture retains the base fixture's image IDs; its rebuilt
semantic roots do not attest a newly built guest.
The focused tests exercise real command authentication and deterministic
allocation, receipt transport and persistence on isolated test state. They
establish neither genuine RISC0 execution nor universal runtime refinement.
Existing initial-state admission evidence cannot independently establish the
economic ownership policy asserted by a test's predecessor.

The explicit factory signatures retain the existing parameter lists. Keeping
these narrow compatibility surfaces avoids introducing a caller-configurable
backend interface into the critical adapter. Shared verification and
publication logic remain in their original invariant-owning modules.

The next qualification requires rebuilt and measured custody module,
coordinator and route guests, their exact receipts, a compatible root epoch
receipt, authenticated initial state and release-specific activation evidence.
This increment does not close W06, W09, W10 or whole-program V3.
