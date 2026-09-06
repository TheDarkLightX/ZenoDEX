"""Declare the constructed sparse-state admission proof and its test subject.

Replay: python3 -B -m experiments.v3_sparse_state_admission_v1.render_evidence
Rendering executes no proof or test and grants no release or economic authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

PROOF = "lean-mathlib/Proofs/AssetTransferSparseStateAdmissionV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_sparse_state_admission_v1.py"
PACKET = "tests/evidence/test_hygiene/THV1-20260906-sparse-state-admission-v1.json"
SOURCES = (
    "experiments/v3_sparse_state_admission_v1/render_evidence.py",
    "docs/research/ZENODEX_SPARSE_STATE_ADMISSION_20260906.md",
    "lean-mathlib/Proofs.lean",
    "lean-mathlib/lean-toolchain",
    "src/core/asset_transfer_module_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/global_economic_state_effect_refinement_v1.py",
    "tests/formal/test_lean_asset_transfer_sparse_supply_v1.py",
    "tests/formal/test_lean_asset_transfer_sparse_tables_v1.py",
    "tests/formal/test_lean_checked_epoch_economic_tables_v1.py",
) + tuple(f"lean-mathlib/Proofs/{name}.lean" for name in (
    "CheckedEconomicAggregationV1", "GlobalSettlementCoreV2",
    "GlobalEconomicStateRefinementV2", "CheckedEpochEconomicTablesV1",
    "CanonicalEpochEconomicRowsV1", "AssetTransferRefinementV1",
    "AssetTransferCustodyCompletionV1", "CheckedSignedDeltaRefinementV1",
    "AssetTransferCustodyCompositionV1", "AssetTransferSparseTablesV1",
    "AssetTransferSparseTraceV1", "AssetTransferSparseSupplyV1",
    "AssetTransferSparseStateAdmissionV1",
))


def main() -> None:
    _render(
        "sparse-state-admission", SOURCES, (TEST,),
        claim="The constructed sparse selected-policy transfer and its actual history preserve StateQuantitiesAdmitted from initial canonical balances and admission. Separate theorems preserve physical owned supply and claimant backing from their respective initial predicates.",
        invariant="V3-CONSTRUCTED-SPARSE-STATE-QUANTITY-ADMISSION",
        families=["formal", "stateful", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="The proof's rejected branch uses the actual sparse step's exact state no-op; the constructed history omits rejected plans. The model has no publication or external write port.",
        bounds=[
            "Nine declarations checked through independently restated signatures; only propext, Classical.choice and Quot.sound allowed as transitive axioms.",
            "Nonempty initial balances, custody, liabilities, reserves, open terminal obligation, oracle and replay entries; a rejected request followed by two accepted requests changes Alice's balance from ten atoms to two.",
            "Initial state admission is constructed in the witness, and no post-admission or Verified premise is supplied to the step or history theorem.",
            "An accepted leaf with writer epoch 2^64 retains inadmissible global pre/post states; distinct owners of the same asset retain distinct global keys.",
            "Owner-erasure mutation first exhibits a well-typed key collision, then the unchanged proof rejects the mutated definition in an isolated source copy.",
        ],
        nonclaims=[
            "StateQuantitiesAdmitted is the existing mathematical predicate; this does not establish every runtime constructor, resource ceiling, or command family.",
            "The selected policy and metadata frame are static; policy membership, signature authenticity, height and replay advancement, canonical hashing and full effect/Verified construction remain separate.",
            "Lean terminal obligations carry a liability domain absent from V1 runtime terminal rows; the witness supplies no exact runtime ownership-domain projection.",
            "The source pins and finite witness do not prove universal Python, Rust or compiler refinement, genuine receipt composition, deployment recovery or whole-program completion.",
            "Mutation execution is confined to private source copies; no production code, wire, policy, balance or publication authority changes.",
        ],
    )
    path = ROOT / PACKET
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: erase the owner coordinate from the sparse-to-global state key, merging two legitimate owners of the same asset and domain.",
        "killed_by": TEST + "::test_state_key_owner_erasure_mutant_rejected_by_unchanged_proof",
        "mutant": {
            "path": PROOF,
            "needle_lines": ["(row.asset, row.owner, row.custodyDomain)"],
            "replacement_lines": ['(row.asset, "", row.custodyDomain)'],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
