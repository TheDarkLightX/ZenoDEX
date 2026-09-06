"""Declare the completed transfer's full annotation-refinement proof subject.

Replay: python3 -B -m experiments.v3_transfer_annotation_mirrors_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render
from experiments.v3_transfer_effect_plan_v1.render_evidence import SOURCES as EFFECT_SOURCES

PROOF = "lean-mathlib/Proofs/AssetTransferAnnotationMirrorsV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_annotation_mirrors_v1.py"
SOURCES = EFFECT_SOURCES + (
    "experiments/v3_transfer_annotation_mirrors_v1/render_evidence.py",
    "docs/research/ZENODEX_TRANSFER_ANNOTATION_MIRRORS_20260906.md",
    "tests/formal/test_lean_asset_transfer_effect_plan_v1.py",
    "lean-mathlib/Proofs/AssetTransferFeeMirrorEligibilityV1.lean",
    "tools/scan_lean_proof_placeholders_v1.py",
    PROOF,
)


def main() -> None:
    _render(
        "transfer-annotation-mirrors", SOURCES, (TEST,),
        claim="The actual completed pre-state-policy transfer satisfies all five global AnnotationMirrors clauses exactly when its selected fee is zero or its fee owner differs from the sender, under quantitative pre-state admission, command bounds and actual acceptance.",
        invariant="V3-CONSTRUCTED-TRANSFER-ANNOTATION-REFINEMENT",
        families=["formal", "differential"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="Rejected completion retains the exact empty plan. Runtime controls check exact leaf rejection codes, unchanged owned inputs, equal roots, all six empty effect fields and unchanged plans after global guard refusals.",
        bounds=[
            "Fresh Std-only Lean 4.27 source closure; eight independently restated public signatures; allowed transitive axioms propext, Classical.choice and Quot.sound.",
            "Actual policy selection and structural plan admission are derived from the input premises; no caller-selected policy or desired output relation is a public premise.",
            "Unique effect keys and actual account/fee kinds imply at most one nonzero state-bearing contribution at each full physical key, establishing every ordered i128 prefix.",
            "Exact fee-owner alias arithmetic determines fee-credit eligibility; reward/slash absence, positive fee rows and zero residue are derived separately.",
            "Eighteen input-derived public runtime vectors cover role aliases, distinct asset policies and signed-width neighbors; fourteen constructed plans check key coordinates, credit, residue and intermediate overflow.",
            "Nonempty admitted witnesses apply the actual front-door, sender-refusal and rejected-empty-plan theorems.",
            "Model-only final-total and unconditional-eligibility counterfactuals are refuted; they are not production-source mutations.",
            "An orphan reward label passes the standalone fee observer but fails the actual full-runtime supported-effect guard and the formal full annotation relation.",
        ],
        nonclaims=[
            "No full global Verified construction, arbitrary custody conservation, lane-root advancement, replay/height progression or lifecycle closure.",
            "Opaque commitments, governed profile admission, signatures and current-store authority remain separate obligations.",
            "Finite comparisons and source pins do not establish universal Python/Rust/compiler refinement, cryptographic receipt validity, publisher qualification or whole-program completion.",
            "The standalone executable fee observer is not the complete AnnotationMirrors predicate for arbitrary effect plans.",
            "No new source-level mutation score, runtime economic change, wire change, policy exemption or live authority.",
        ],
    )


if __name__ == "__main__":
    main()
