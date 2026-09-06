"""Declare the custody-complete transfer conservation proof subject.

Replay: python3 -B -m experiments.v3_transfer_custody_effect_plan_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_annotation_mirrors_v1.render_evidence import (
    SOURCES as ANNOTATION_SOURCES,
)

PROOF = "lean-mathlib/Proofs/AssetTransferCustodyEffectPlanV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_custody_effect_plan_v1.py"
SOURCES = tuple(dict.fromkeys(ANNOTATION_SOURCES + (
    "experiments/v3_transfer_custody_effect_plan_v1/render_evidence.py",
    "docs/research/ZENODEX_TRANSFER_CUSTODY_EFFECT_PLAN_20260906.md",
    "tests/formal/test_lean_asset_transfer_annotation_mirrors_v1.py",
    "src/core/asset_transfer_lane_module_custody_v1.py",
    "src/core/asset_transfer_lane_module_v1.py",
    "src/core/asset_lane_projection_v1.py",
    "src/core/asset_transfer_global_allocation_v1.py",
    PROOF,
)))


def main() -> None:
    _render(
        "transfer-custody-effect-plan", SOURCES, (TEST,),
        claim="The constructed custody successor derives physical conservation totals from actual balance and custody tables, proves exact table/supply effects and conservation coverage/row correspondence under its input premises, and retains the prior annotation eligibility and rejection contracts.",
        invariant="V3-CONSTRUCTED-CUSTODY-TRANSFER-CONSERVATION",
        families=["formal", "differential", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="Rejected completion retains the exact modeled input state and empty plan. Runtime controls check exact rejection codes, unchanged canonical inputs, equal roots and all six empty effect fields. Invalid input-constructor exceptions are classified separately.",
        bounds=[
            "Fresh Std-only Lean 4.27 source closure with independent public theorem consumers and permitted transitive axioms only.",
            "Selected policy, constructed post-state, custody frame and account-total preservation are derived from the actual transition; no desired output relation is assumed.",
            "Physical totals count balances plus custody. Liabilities are separate claims. Empty initial reserves is explicit where the broader global ownedFor is used.",
            "Command constructor bounds and actual acceptance imply nonzero sender movement; a negative-command model control demonstrates why acceptance alone is insufficient.",
            "Input quantity admission establishes u128 physical bounds; initial owned-supply equality separately implies post equality for every asset.",
            "Finite input-derived runtime vectors and nonempty Lean witnesses cover multiple assets, custody, claimant liabilities, fee-owner aliases, exact rejection and width boundaries.",
            "Direct runtime conservation controls detect omitted custody, counted liabilities, missing or unrelated conservation rows, and an untouched-asset supply mismatch.",
            "A definitions-only source mutation omits custody from physicalFor; paired mathematical witnesses distinguish the original correct total from the mutant's incorrect conservation row.",
        ],
        nonclaims=[
            "No full global Verified construction, root/height/replay progression, canonical encoding/decoding or lifecycle closure.",
            "The global model and runtime use different general touched-asset definitions; correspondence here is confined to the constructed well-formed transfer family.",
            "Command and reserve premise-removal examples describe mathematical model boundaries; they do not establish runtime acceptance of invalid inputs.",
            "The mutation checks the actual physical projection definition and a fixed conservation-row obligation, not a complete mutated upstream proof or a production mutation score.",
            "Finite replay and source pins do not prove universal Python/Rust/compiler refinement, receipt validity, authentication, store provenance, publisher qualification or whole-program completion.",
            "No runtime economics, wire formats, policy constants, release images or live authority change.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260906-transfer-custody-effect-plan-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: omit custody from the actual physical projection definition; the paired fixed conservation-row obligation distinguishes 57 from the required global total of 100.",
        "killed_by": TEST + "::test_paired_balances_only_source_mutant_is_killed_at_conservation_obligation",
        "mutant": {
            "path": PROOF,
            "needle_lines": [
                "  G.amountForAsset state.balances asset + G.amountForAsset state.custody asset",
            ],
            "replacement_lines": ["  G.amountForAsset state.balances asset"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
