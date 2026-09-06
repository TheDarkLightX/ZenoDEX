"""Declare the multi-asset pre-state policy-selection proof subject.

Replay: python3 -B -m experiments.v3_transfer_policy_selection_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

PROOF = "lean-mathlib/Proofs/AssetTransferPolicySelectionV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_policy_selection_v1.py"
PACKET = "tests/evidence/test_hygiene/THV1-20260906-transfer-policy-selection-v1.json"
SOURCES = (
    "experiments/v3_transfer_policy_selection_v1/render_evidence.py",
    "docs/research/ZENODEX_TRANSFER_POLICY_SELECTION_20260906.md",
    "lean-mathlib/Proofs.lean",
    "lean-mathlib/lean-toolchain",
    "src/core/asset_transfer_module_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/global_economic_state_effect_refinement_v1.py",
    "tests/formal/test_lean_asset_transfer_sparse_state_admission_v1.py",
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
    "AssetTransferSparseStateAdmissionV1", "AssetTransferSparseAuthorizationV1",
    "AssetTransferPolicySelectionV1",
))


def main() -> None:
    _render(
        "transfer-policy-selection", SOURCES, (TEST,),
        claim="The constructed sparse transfer selects a matching policy from its pre-state, derives selected-state widths from admitted tables, and preserves quantitative local admission across multi-asset histories. Accepted-decrease authorization also uses command constructor bounds.",
        invariant="V3-PRESTATE-POLICY-SELECTION-AND-CONSTRUCTOR-PREMISES",
        families=["formal", "differential", "stateful", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="The constructed front door returns the exact pre-state and empty plan on rejection; its history excludes rejected plans. Runtime finite cases check equal rejection roots, empty effects and unchanged owned input bytes.",
        bounds=[
            "Independently restated public theorem signatures; fresh Lean 4.27 source closure; only propext, Classical.choice and Quot.sound allowed as transitive axioms.",
            "First-match pre-state policy lookup, unique matching member, and release-before-command-before-unknown-asset rejection precedence.",
            "All-asset coverage is equivalent to registered balance assets plus per-supply coverage under positive balances, unique supply keys and u128 supplies; zero local supply remains permitted.",
            "Selected balances, supply and fee widths derive from admitted pre-state rows; initial admission is preserved through a rejected request and transfers of two distinct assets.",
            "Public Python transition comparisons cover different fees and owners, absent and disabled assets, combined guard failures, fee limits, role aliases and signed-delta width neighbors.",
            "Stateful endpoint accounting is independently computed from submitted commands and initial policies.",
            "A source-copy mutant selects the first row regardless of asset; a well-typed positive observation exposes the wrong row before the unchanged lookup proof rejects it.",
        ],
        nonclaims=[
            "Quantitative constructor premises do not cover exact runtime classes, token/root syntax, malformed-input exception outcomes or canonical byte encoding.",
            "Local policy membership is separate from governed registry/profile membership, signature authenticity, grants and current-store authority.",
            "Module release and policies are static across the modeled history; full effects, journals, occurrence consumption, metadata advancement and Verified construction remain separate.",
            "Finite comparisons and source pins do not establish universal Python, Rust or compiler refinement, genuine receipt composition, deployment qualification or whole-program completion.",
            "The model has no publication port. No runtime economic code, wire format, policy value or live authority is changed.",
        ],
    )
    path = ROOT / PACKET
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: first-row selection ignores the requested asset and returns an unrelated policy's fee and owner.",
        "killed_by": TEST + "::test_first_row_lookup_mutant_is_well_typed_then_killed_by_lookup_theorem",
        "mutant": {
            "path": PROOF,
            "needle_lines": ["  policies.find? fun policy => policy.asset == asset"],
            "replacement_lines": ["  policies.find? fun policy => (policy.asset == asset || true)"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
