"""Render the sparse debit authorization and custody activation restart records.

Replay: python3 -B -m experiments.v3_authorization_restart_v1.render_evidence
Rendering pins the declared proof, harness, fixture and dependency sources; it
runs no proof or test and qualifies no release. Earlier packets stay unchanged.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render

OWN = (
    "experiments/v3_authorization_restart_v1/render_evidence.py",
    "docs/research/ZENODEX_SPARSE_AUTHORIZATION_AND_CUSTODY_RESTART_20260906.md",
)
# Captured import closure compiled by the harness, in the harness's build order.
SPARSE_LEAN_CLOSURE = tuple(
    f"lean-mathlib/Proofs/{name}.lean" for name in (
        "AssetTransferSparseAuthorizationV1", "AssetTransferSparseTraceV1",
        "AssetTransferSparseTablesV1", "AssetTransferRefinementV1",
        "AssetTransferCustodyCompletionV1", "AssetTransferCustodyCompositionV1",
        "CheckedSignedDeltaRefinementV1", "CheckedEconomicAggregationV1",
        "GlobalSettlementCoreV2", "GlobalEconomicStateRefinementV2",
        "CheckedEpochEconomicTablesV1", "CanonicalEpochEconomicRowsV1",
    )
) + ("lean-mathlib/Proofs.lean",)
SPARSE_RUNTIME = (
    "src/core/asset_transfer_module_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/global_economic_state_delta_v1.py",
    "src/core/global_economic_state_effect_refinement_v1.py",
)
SPARSE_HARNESS_IMPORTS = (
    "tests/formal/test_lean_asset_transfer_sparse_tables_v1.py",
    "tests/formal/test_lean_asset_transfer_sparse_trace_v1.py",
    "tests/formal/test_lean_checked_epoch_economic_tables_v1.py",
)
CUSTODY_FIXTURE = ("tests/integration/custody_asset_receipt_pipeline_fixtures_v1.py",)
CUSTODY_RUNTIME = (
    "src/integration/global_economic_durable_publisher_v1.py",
    "src/integration/global_economic_epoch_journal_v1.py",
    "src/integration/global_economic_durable_epoch_v1.py",
    "src/integration/global_economic_commit_v1.py",
    "src/integration/isolated_asset_receipt_pipeline_v1.py",
    "src/integration/isolated_profile_receipt_ports_v1.py",
    "src/integration/economic_command_bls_signature_verifier_v1.py",
    "src/integration/sealed_bls_command_verifier_v1.py",
    "src/integration/global_receipt_verifier_v1.py",
    "src/core/economic_initial_state_v1.py",
    "src/core/asset_transfer_lane_module_custody_v1.py",
    "src/core/asset_transfer_custody_semantics_v1.py",
    "src/core/asset_transfer_epoch_allocation_v1.py",
    "src/core/asset_transfer_receipt_admission_v1.py",
    "src/core/lane_module_release_route_binding_v1.py",
    "src/core/lane_module_receipt_verification_v1.py",
    "src/core/global_accounting_lane_producers_v1.py",
)
CUSTODY_HARNESS_IMPORTS = (
    "tests/integration/publisher_receipt_port_fixtures_v1.py",
    "tests/integration/test_global_economic_sealed_bls_pipeline_v1.py",
    "tests/integration/test_sealed_bls_command_verifier_deployment_v1.py",
    "tests/core/test_global_settlement_abi_v1.py",
    "tests/core/test_economic_receipt_verifier_release_v1.py",
    "tests/core/test_asset_transfer_global_allocation_v1.py",
    "tests/core/test_economic_command_authentication_v1.py",
)


def main() -> None:
    _render("sparse-debit-authorization",
            OWN + SPARSE_LEAN_CLOSURE + SPARSE_RUNTIME + SPARSE_HARNESS_IMPORTS,
            ("tests/formal/test_lean_asset_transfer_sparse_authorization_v1.py",),
            claim="Constructed sparse selected-policy debits identify the declared sender and its accepted context; every endpoint decrease in a constructed history witnesses an accepted executed-prefix occurrence under canonical balances and nonnegative amount and fee. Runtime correspondence is finite.",
            invariant="V3-CONSTRUCTED-SPARSE-DEBIT-AUTHORIZATION",
            families=["formal", "differential", "stateful"],
            change_kind="assurance_infrastructure", created_date="2026-09-06",
            rejection_reason="Rejected sparse attempts retain the exact source state and empty plan; the history omits them and continues from the same state. Runtime cases observe the exact rejection code, empty effects, equal pre and post roots and unchanged owned inputs.",
            bounds=["ten checked theorems with independent consumer signatures and transitive axioms limited to propext, Classical.choice and Quot.sound",
                    "13 single-step corpus cases: distinct, sender and recipient fee-owner aliases, zero fee, reversed roles, zero-row deletion, u128 holding and i128 effect neighbors, i128 overflow, unauthorized subject, zero amount and insufficient balance",
                    "three nine-attempt histories with five accepted transfers each, one per fee-owner class, against independent signed-event endpoint sums",
                    "role-specific decreased sets: treasury fee owner debits alice and bob, alice fee owner debits only bob, bob fee owner debits only alice",
                    "five runtime constructor controls for the missing model lower bounds and widths: -1, -2^127, True, False and 2^128",
                    "two retained model-premise counterexamples: a negative amount reverses a one-atom transfer and a negative fee debits a distinct one-atom fee owner",
                    "two conserving unauthorized runtime mutants, subject-guard bypass and reversed debit, detected by the independent debit oracle",
                    "a rejected then accepted two-request demo history reaches the authorized debit"],
            nonclaims=["No signature authenticity, selected-policy membership, profile selection, metadata, height or replay admission theorem is established; context subject equality is not authenticated command authority.",
                       "Nonnegative amount and fee are theorem premises discharged only by runtime constructors; the two negative-Int examples are model-premise counterexamples and not runtime defects.",
                       "The three pre-fix harness failures were test authoring errors (a reserved Lean binder, multiline JSON decoding and a false all-fee-owner alice decrease); no theorem was weakened.",
                       "Finite corpus and history comparisons do not prove universal Python, Rust or compiler refinement, complete effect plans, publication or the whole formal core.",
                       "Histories fix one module release and selected policy; no activation, migration or restart semantics are proved.",
                       "Runtime mutants are monkeypatched process-local controls, not a mutation campaign against a deployed publisher."])
    _render("custody-activation-restart",
            OWN + CUSTODY_FIXTURE + CUSTODY_RUNTIME + CUSTODY_HARNESS_IMPORTS,
            ("tests/integration/test_global_economic_custody_pipeline_v1.py",
             "tests/integration/test_isolated_custody_asset_receipt_pipeline_v1.py"),
            claim="One immutable custody activation context supports a same-process publisher close and reopen: the exact epoch-one retry is ALREADY_COMMITTED with unchanged store rows, and the adjacent epoch-two publication continues from the committed epoch-one head with unchanged custody and claimant liability ownership.",
            invariant="V3-CUSTODY-ACTIVATION-REOPEN-SOURCE-CONTINUITY",
            families=["stateful", "differential"],
            change_kind="assurance_infrastructure", created_date="2026-09-06",
            rejection_reason="An exact retry of a committed epoch returns ALREADY_COMMITTED with the committed head and published epoch while metadata, current head and epoch rows stay identical. The forward fixture refuses rebound semantic roots, signature coordinates, liabilities or custody atoms and a later state without an activation. Retained invalid-signature and uncovered-claimant refusals leave the logical store unchanged.",
            bounds=["one SQLite store/path carries two epochs under one fixed test activation; custody and liability rows hold exactly 7 atoms in the vault domain",
                    "epoch one: create, commit, close, reopen, exact retry ALREADY_COMMITTED with an identical logical store",
                    "epoch two from the same activation object and the committed epoch-one post state with nonce 2: source publication id, pre-state root, height plus one and sequence plus one all bound to epoch one",
                    "current head sequence 2 and exactly two exact epoch rows; the exact epoch-two retry leaves the store unchanged",
                    "forward fixture identity: same activation and initial-state admission objects, same registries, pre state equal to the predecessor post state",
                    "Python BLS backend for the reopen history; the sealed BLS positive case is a separate parametrized run with an explicit checksum-qualified binary",
                    "retained invalid-signature refusal before receipt calls and absent or mismatched (0, 6, 8 atom) claimant backing refusals",
                    "the forward-fixture test failed against the pre-fix fixture before the repair"],
            nonclaims=["RISC0 receipt replies and release coordinates are synthetic; no genuine custody guest chain, image or receipt is qualified.",
                       "Close and reopen happen in one test process on one path; killed-process recovery, crash consistency, rollback, migration and writer fencing are not exercised.",
                       "The Python BLS backend carries its loaded-code integrity premise; the sealed binary case supplies real-execution evidence only when ZENODEX_BLS_VERIFIER_TEST_BINARY names the checksum-qualified artifact, and a skipped run supplies none.",
                       "Initial claimant liability rows in test state do not approve production claimant, initial-ownership or migration policy.",
                       "The pre-fix AttributeError showed an absent activation attribute in the old fixture; it was a test-construction failure, not a production semantic defect. No publisher, journal, allocation or admission source changed.",
                       "No live activation, production qualification or whole-program completeness is established."])


if __name__ == "__main__":
    main()
