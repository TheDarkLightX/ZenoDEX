"""Declare additive registered-supply support evidence without promotion.

Replay: python3 -B -m experiments.v3_registered_supply_support_v1.render_evidence
Rendering writes only the new THV1 declaration. It executes no Lean or Python
test, runtime transition, proof, publication, or release qualification.
Historical evidence packets remain unchanged.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render

PROOF = "lean-mathlib/Proofs/RegisteredSupplySupportV1.lean"
TEST = "tests/formal/test_lean_registered_supply_support_v1.py"
SOURCES = (
    PROOF,
    "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean",
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
    "lean-mathlib/lean-toolchain",
    "lean-mathlib/Proofs.lean",
    "src/core/global_settlement_types_v1.py",
    "src/core/managed_asset_lifecycle_module_v1.py",
    "src/core/managed_asset_lifecycle_types_v1.py",
    "tests/core/test_managed_asset_lifecycle_boundaries_v1.py",
    "experiments/v3_registered_supply_support_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)


def main() -> None:
    _render(
        "registered-supply-support",
        SOURCES,
        (TEST,),
        claim=(
            "An additive Std-only Lean bridge provides 24 checked theorem "
            "signatures covering general registered-supply support, unique-key "
            "roundtrip and filtered numeric-order laws, plus concrete identity "
            "countermodels; "
            "finite Python observations compare actual managed-asset "
            "issue-from-zero and full-burn rows with its raw and numeric views."
        ),
        invariant="V3-REGISTERED-SUPPLY-SUPPORT-IDENTITY-AND-ORDER",
        families=["formal", "differential"],
        change_kind="assurance_infrastructure",
        created_date="2026-09-07",
        rejection_reason=(
            "Lean negative controls establish propositions for negative and "
            "u128-overflow source/support rows and identity-loss countermodels; "
            "the existing Python issue and burn transitions preserve their "
            "complete pre-state snapshots. No publication or external write is "
            "modeled by this subject."
        ),
        bounds=[
            "Twenty-four independently consumed theorem signatures cover exact registered-key preservation, unique-key decode/encode roundtrip, numeric lookup, filtered support, u128 admission, numeric-key Sublist, and generic Pairwise order transfer.",
            "Explicit zero rows remain in the ordered registered-key view while absent from numeric support; a separated two-positive-row fixture checks that filtering retains support order across the zero row.",
            "Duplicate source keys and a removed registered zero key provide concrete identity-loss controls: numeric lookup can agree while uniqueness, decoded rows, or key lists differ.",
            "Empty, all-zero, mixed, unsorted, maximum-u128, negative, and maxU128-plus-one controls exercise the finite representation and support-admission boundary without introducing new policy constants.",
            "The Python observations use the existing managed-asset issue-from-zero and exact full-burn fixtures, preserving the explicit zero supply row/key and comparing complete raw rows with filtered numeric rows.",
            "The Lean subject is copied into a fresh three-module source/library closure and checked under the repository's pinned Lean 4.27.0 toolchain; the formal test independently scans theorem declarations and transitive axioms.",
        ],
        nonclaims=[
            "registeredAssetKeys are representation data only and confer no registration, policy, authorization, custody, issuance, or other authority.",
            "The bridge does not change V1 wire fields, canonical bytes, state roots, hash domains, resource policy, or managed-asset lifecycle behavior.",
            "Finite Python observations do not establish V1 runtime-to-V2 admission, canonical-byte/root refinement, universal Python/Lean/compiler refinement, or a complete runtime lifecycle.",
            "No receipt, cryptographic proof, measured deployment, verifier image, publication, finality, migration, release, settlement, or production authority is created or qualified.",
            "The existing managed-asset fixtures establish finite row/key correspondence for issue-from-zero and full-burn paths; they do not prove reissue, registry admission, policy equivalence, or every zero-supply lifecycle.",
            "Source pins and independent theorem consumers are evidence of this bounded subject only. They do not promote formal-core completion, whole-program completeness, or product readiness.",
            "Rendering executes no test or proof and writes no historical packet; any generated packet is a new declaration for this subject only.",
        ],
    )


if __name__ == "__main__":
    main()
