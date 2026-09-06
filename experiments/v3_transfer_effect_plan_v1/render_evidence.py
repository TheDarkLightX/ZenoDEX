"""Declare the constructed transfer effect-plan proof subject.

Replay: python3 -B -m experiments.v3_transfer_effect_plan_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_policy_selection_v1.render_evidence import SOURCES as POLICY_SOURCES

PROOF = "lean-mathlib/Proofs/AssetTransferEffectPlanV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_effect_plan_v1.py"
PACKET = "tests/evidence/test_hygiene/THV1-20260906-transfer-effect-plan-v1.json"
SOURCES = POLICY_SOURCES + (
    "experiments/v3_transfer_effect_plan_v1/render_evidence.py",
    "docs/research/ZENODEX_TRANSFER_EFFECT_PLAN_20260906.md",
    "tests/formal/test_lean_asset_transfer_policy_selection_v1.py",
    "src/core/global_economic_state_delta_v1.py",
    PROOF,
)


def main() -> None:
    _render(
        "transfer-effect-plan", SOURCES, (TEST,),
        claim="The constructed pre-state-policy transfer emits a complete six-field structural effect plan admitted from quantitative input constructor premises, retaining the existing verdict, post-state and exact economic-table and supply-effect relations.",
        invariant="V3-CONSTRUCTED-TRANSFER-EFFECT-PLAN-ADMISSION",
        families=["formal", "differential", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="Rejected completion preserves the exact modeled input state and complete empty plan; finite public runtime comparisons check rejection codes, equal roots, all six empty effect fields and unchanged owned input bytes.",
        bounds=[
            "Fresh Std-only Lean 4.27 source closure; independent public theorem signatures and axiom checks.",
            "Admitted pre-state tables imply structural EffectPlanAdmitted without a supplied postcondition or supplied post-state; command constructor bounds and authorization are separate obligations.",
            "Alias aggregation and zero elision yield at most three movement rows and one fee allocation, with complete-key uniqueness and canonical row order.",
            "Asset conservation derives actual account and supply totals; independent issue, burn and fee projections bind declared rows to constructed effects.",
            "Finite Python comparisons cover all six effect fields; opaque roots and occurrence IDs are transported observations only.",
            "A well-typed paired issue-and-burn source mutant preserves net-zero quantities while the unchanged separate-projection proof rejects it.",
        ],
        nonclaims=[
            "Structural plan admission does not authenticate lane roots, occurrence IDs, governed profiles, commands or current-store state.",
            "V1 conservation counts accounts. Global owned amounts include custody and reserves and require separate conservation-state refinement.",
            "Positive sender-fee transfers remain subject to the rejecting global fee-mirror guard; full AnnotationMirrors is not established here.",
            "Lane-root state updates, replay registry and height advancement, journals, receipt cryptography and full GlobalEconomicStateRefinementV2.Verified remain separate.",
            "Finite replay and source pins do not establish universal Python, Rust or compiler refinement, release qualification or whole-program completion.",
            "No runtime economics, wire formats, policy constants, publication port or live authority change.",
        ],
    )
    path = ROOT / PACKET
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: equal fabricated authorized issuance and burn preserve net conservation but disagree with the transfer's separate issue and burn effects.",
        "killed_by": TEST + "::test_paired_issue_burn_preserves_net_but_fails_projection",
        "mutant": {
            "path": PROOF,
            "needle_lines": ["    authorizedIssueAtoms := 0", "    authorizedBurnAtoms := 0 }"],
            "replacement_lines": ["    authorizedIssueAtoms := 1", "    authorizedBurnAtoms := 1 }"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
