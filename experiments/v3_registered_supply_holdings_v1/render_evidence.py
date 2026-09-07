"""Declare the scoped supply-to-holdings connector evidence.

Replay: python3 -B -m experiments.v3_registered_supply_holdings_v1.render_evidence
Rendering writes one new declaration; it executes no proof or test and grants
no authority. Historical packets remain unchanged.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render

PROOF = "lean-mathlib/Proofs/RegisteredSupplyHoldingsV1.lean"
TEST = "tests/formal/test_lean_registered_supply_holdings_v1.py"
SOURCES = (
    PROOF,
    "lean-mathlib/Proofs/RegisteredSupplySupportV1.lean",
    "lean-mathlib/Proofs/AssetTransferPolicySelectionV1.lean",
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
    "lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean",
    "lean-mathlib/Proofs/AssetTransferGlobalStateClosureV1.lean",
    "lean-mathlib/lean-toolchain",
    "lean-mathlib/Proofs.lean",
    "src/core/asset_lane_projection_v1.py",
    "src/core/asset_lane_coordinator_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/managed_asset_lifecycle_module_v1.py",
    "src/core/managed_asset_lifecycle_types_v1.py",
    "src/core/global_settlement_types_v1.py",
    "tests/core/test_managed_asset_lifecycle_boundaries_v1.py",
    "tests/formal/test_lean_asset_transfer_global_state_closure_v1.py",
    "tests/formal/test_lean_asset_transfer_global_successor_v1.py",
    "experiments/v3_registered_supply_holdings_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)


def main() -> None:
    _render(
        "registered-supply-holdings",
        SOURCES,
        (TEST,),
        claim=(
            "Seven Lean theorems connect actual V1 policy-selection supply rows "
            "to complete registered keys, sparse numeric support and per-asset "
            "owned quantities, with explicit reserve-empty physical and actual "
            "global continuation corollaries. Runtime observations remain finite."
        ),
        invariant="V3-REGISTERED-SUPPLY-HOLDINGS-RELATION",
        families=["formal", "differential", "stateful"],
        change_kind="assurance_infrastructure",
        created_date="2026-09-07",
        rejection_reason=(
            "The formal rejected continuation consumes the actual zero-amount "
            "leaf verdict and returns the exact predecessor. Finite runtime "
            "controls retain complete source snapshots and inspect typed "
            "constructor or transition rejections. No publication is modeled."
        ),
        bounds=[
            "The primitive theorem takes StateAdmitted and OwnedMatchesSupply separately and retains explicit zero supply rows without assuming global nonzero quantity admission.",
            "The relation includes complete source-key order even when every numeric row is filtered, unique-key roundtrip, exact policy keys, numeric Sublist/order and per-asset lookup.",
            "A two-asset zero/positive witness, removed or duplicate keys and reversed complete keys distinguish registered identity from equal numeric totals.",
            "Balances plus custody 9 and supply 10 fail full ownership with empty reserves; reserve 1 restores full ownedFor equality and does not satisfy the reserve-empty corollary premise.",
            "Existing accepted and rejected continuation subjects consume continuedState_invariant and the actual transition result, without a desired post-state or support relation as a premise.",
            "Independent public theorem consumers inspect permitted transitive axioms in a fresh source-pinned 23-module Std-only Lean 4.27.0 closure.",
            "Existing managed-asset V1 issue-from-zero and full-burn transitions retain exact source supply keys through the actual asset-lane projection; finite runtime controls compare complete rows and physical holdings.",
        ],
        nonclaims=[
            "The primitive relation does not establish full StateQuantitiesAdmitted or custody/reserve quantity validity; the stronger global invariant supplies those premises independently.",
            "The primitive zero-supply domain is separate from the positive sparse global invariant and continuation domain.",
            "Registered keys and prepared representations confer no policy, registry, issuance, custody or publication authority.",
            "No V1 wire field, canonical encoding, hash domain, runtime policy, rounding rule or economic transition changes.",
            "Finite Python observations do not prove universal Python/Rust/Lean/compiler correspondence, canonical decoding, authenticated state roots or complete lane lifecycles.",
            "ESSO, Kani, Rust/RISC0, real receipt proving and production qualification are separate evidence lanes; this renderer executes none of them.",
            "No formal-core completion, whole-program value-safety, product completion, finality, deployment or release promotion follows from this subject.",
        ],
    )


if __name__ == "__main__":
    main()
