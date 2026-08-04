# FCIS M6 Authenticated zUSD Fee Source Binding V2 Report

TASK_ID: M6-ZUSD-FEE-SOURCE-BINDING-V2
BASE_SHA: 7d905908c1448c468102f2144528f4d2ae34918d
SOURCE_HEAD_SHA: 2a275c3c882729fa2960749923b925ab3c6c2a90
SOURCE_HEAD_TREE: 1fc20bb410c26fe130bcbac6ade830df51425e3e
BRANCH: codex/task-m6-managed-asset-policy-20260803

FILES_CHANGED:
- lean-mathlib/Proofs.lean
- lean-mathlib/Proofs/FCISM6FeeSourceBinding.lean
- src/core/fcis_m6_e01_request_identity.py
- src/core/fcis_fee_configuration_state_binding_v2.py
- src/core/zusd_authenticated_borrow_fee_occurrence_kernel_v1.py
- src/core/zusd_authenticated_borrow_fee_occurrence_roots_v1.py
- src/core/zusd_authenticated_borrow_fee_occurrence_v1.py
- src/core/zusd_authenticated_borrow_fee_occurrence_values_v1.py
- src/core/zusd_state_bound_fee_accrual_allocation_roots_v2.py
- src/core/zusd_state_bound_fee_accrual_allocation_v2.py
- src/core/zusd_state_bound_fee_accrual_allocation_values_v2.py
- src/kernels/dex/fcis_fee_configuration_state_binding_v2.yaml
- src/kernels/dex/zusd_authenticated_borrow_fee_occurrence_v1.yaml
- src/kernels/dex/zusd_state_bound_fee_accrual_allocation_v2.yaml
- tests/core/test_fcis_m6_e01_request_identity.py
- tests/core/test_fcis_fee_configuration_state_binding_v2.py
- tests/core/test_zusd_authenticated_borrow_fee_occurrence_v1.py
- tests/core/test_zusd_state_bound_fee_accrual_allocation_v2.py
- tests/formal/test_esso_fcis_fee_source_binding_v1.py
- tests/formal/test_lean_fcis_m6_fee_source_binding.py

CLAIM_IMPLEMENTED: This research slice closes a local composition relation from
an E01-controlled request identity and exact zUSD pre-state through one freshly
replayed positive borrowing-fee occurrence, one configuration bound to an exact
state projection, and one independently verified SRGD allocation transition.
The composite binds the request sequence, deployment configuration, authority
epoch, zUSD state, managed asset, fee custody, scalar claim, role claims,
apportionment state, fee domain, cumulative fee history, and all pre/post roots.
The fee amount and allocation policy are derived from controlled inputs rather
than accepted again from the caller.

INVARIANT_AND_AUTHORITY_BOUNDARY: A B1A-valid configuration gains local
state-relative authority only after the four B1B laws hold: canonical body
root, equality with the exact-state header root, deployment equality, and
activation sequence no later than the state sequence. The request identity,
configuration binding, borrowing-fee occurrence, and final composition each
require controlled construction plus point-of-use revalidation. The exact-state
projection remains public candidate data. It does not prove store currentness,
global-state reconstruction, or external authentication.

COMMANDS_RUN:
- `python3 -m ruff check` over all nine changed core source modules and focused tests
- `python3 -m ruff format` over all changed Python source and focused tests
- `python3 -m mypy --strict` over all nine changed core source modules
- `python3 -m mypy`
- `python3 -m py_compile` over all nine changed core source modules
- `python3 -m pytest -q tests/core/test_fcis_m6_e01_request_identity.py tests/core/test_fcis_fee_configuration_state_binding_v2.py tests/core/test_zusd_authenticated_borrow_fee_occurrence_v1.py tests/core/test_zusd_state_bound_fee_accrual_allocation_v2.py`
- `ESSO_ROOT=external/ESSO PYTHONPATH=. python3 -m pytest -q tests/formal/test_esso_fcis_fee_source_binding_v1.py`
- `PYTHONPATH=. python3 -m pytest -q tests/formal/test_lean_fcis_m6_fee_source_binding.py`
- `PYTHONPATH=external/ESSO python3 -m ESSO verify-multi <each of the three exact model paths> --solvers z3,cvc5 --determinism-trials 2 --timeout-ms 5000`
- `lake env lean Proofs/FCISM6FeeSourceBinding.lean`
- `lake build Proofs` before the final Python-only module split; the Lean sources were unchanged afterward
- `python3 tools/check_production_boundary.py --json`
- `python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py <nine changed core modules>` from the main checkout
- `python3 .claude/skills/zenodex-refactoring/scripts/design_metrics.py <eight new critical modules> --top 20 --coupling` from the main checkout
- `python3 -m pytest -q tests/core/test_fcis_fee_*.py tests/core/test_zusd*.py`
- `git diff --check`

RESULTS:
- Focused deterministic core tests passed: 27 passed.
- The ESSO integration and semantic-mutation gate passed: 26 passed.
- Z3 and CVC5 agreed on all 37 inductive queries across three models; all three verdicts were `VERIFIED`, with two identical determinism fingerprints per model.
- The ESSO mutation matrix killed 23/23 guard or update mutants.
- Focused Lean tests passed: 3 passed.
- Direct Lean typechecking passed. The top composition theorem depends only on Lean's standard `propext` and `Quot.sound`; no `sorry`, `admit`, user axiom, unsafe declaration, or placeholder is present.
- The full `Proofs` aggregate built successfully before a later Python-only module split; the Lean source digest remained `9ee1641ce6bcabe0f6c0304036f7f05236eb86b859cb50bf6988b63d9605526e`.
- Ruff, strict and configured mypy, Python compilation, production-boundary audit, diff hygiene, and the security red-flag scan passed.
- The design scanner found no oversized file or flagged function after the deterministic module split.
- The broad fee/zUSD regression produced 213 passed and one known pre-existing failure: `tests/fixtures/fcis_fee_apportionment_v2_golden.json` is stale relative to its builder. This slice did not modify or regenerate that fixture.

MUTANTS_ADDED: Removed state-projection, configuration validity, configuration
root, deployment, and activation guards; removed request identity, command
family, pre-state, command-root, kernel-accept, and debt-delta guards; removed
free-debt, issued-principal, protocol-fee, and occurrence-total updates; removed
controlled-source, request-context, zUSD-state, component-root,
managed-identity, fee-domain, cumulative-history, and allocation guards. Runtime
negative tests also cross request sequence, deployment root, authority epoch,
zUSD root, scalar/role/apportionment roots, asset, custody, fee domain,
cumulative history, principal, pre-state, configuration, and candidate lineage.

FORMAL_EVIDENCE: Three finite ESSO-IR transition systems were checked
inductively by pinned Z3 4.15.4 and CVC5 1.1.2 through ESSO commit
`7f80c6216be85c827e8d1cc2fa08ee3107a74588`. Lean proves the abstract
configuration-binding exclusions, authenticated debt formula, crossed-state
rejection, request-context exposure, supply-plus-claim identity, and the local
composition implication. These theorems do not prove Python refinement,
cryptographic authentication, or mounted runtime mediation.

REMAINING_NONCLAIMS:
- The exact-state projection is not derived from the mounted Tau or ZenoLedger global state.
- The binding does not prove that the supplied exact state is store-current; expected-head publication must establish currentness.
- E01 authentication soundness and signer/quorum authority remain external premises.
- No Rust, Tau, ZenoLedger, or canonical cross-runtime byte parity is established for this new composite.
- No zUSD transferable-balance issuance, generic-token exclusion, fee-claim realization, or whole-system R13 preservation theorem is established here.
- No candidate, receipt, bundle, history, nullifier, replay, recovery, outbox, or acknowledgment schema consumes this composite yet.
- No atomic publication, concurrency, crash, migration, mounted no-bypass, deployment, or value movement is claimed.
- Fee-bearing borrowing remains unsuitable for production enablement until those obligations close.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The controlled-construction registries are process-local research
provenance and are not a substitute for cryptographic or durable authority.
The global-state projection currently trusts caller-supplied component roots;
a mounted projection must freshly derive them from one authenticated current
state. The pure zUSD replay uses the existing Python kernel and lacks Rust/Tau
refinement. The repository also retains unrelated stale fee-apportionment
golden-fixture debt. Independent review should attack root projection
completeness, configuration activation semantics, state-subroot derivation,
managed-asset identity, and end-to-end publication lineage.
