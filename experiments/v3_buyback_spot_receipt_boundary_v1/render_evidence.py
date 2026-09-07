"""Declare the bounded SHADOW buyback Spot receipt execution boundary.

Replay: python3 -B -m experiments.v3_buyback_spot_receipt_boundary_v1.render_evidence
Rendering writes one new declaration. Test and mutation execution are separate;
historical packets, economic state and publication authority remain unchanged.
"""

from __future__ import annotations

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

CORE = "src/core/zdex_buyback_spot_safety_receipt_v1.py"
PREPARATION = "src/core/zdex_buyback_spot_safety_receipt_preparation_v1.py"
SHELL = "src/integration/zdex_buyback_spot_safety_receipt_v1.py"
TEST = "tests/integration/test_zdex_buyback_spot_safety_verifier_boundary_v1.py"
RENDERER = "experiments/v3_buyback_spot_receipt_boundary_v1/render_evidence.py"
PACKET = "tests/evidence/test_hygiene/THV1-20260907-buyback-spot-receipt-boundary-v1.json"
TESTS = (
    TEST,
    "tests/core/test_zdex_buyback_spot_safety_receipt_v1.py",
    "tests/integration/test_economic_epoch_verifier_boundary_v1.py",
)
SOURCES = (
    CORE,
    PREPARATION,
    SHELL,
    "src/core/global_economic_authority_head_v1.py",
    "src/core/global_economic_profile_snapshot_v1.py",
    "src/core/global_economic_refinement_snapshot_v1.py",
    "src/core/global_economic_proof_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/economic_receipt_verifier_deployment_v1.py",
    "src/core/economic_receipt_verifier_registry_v1.py",
    "src/core/zdex_atomic_buyback_state_v1.py",
    "src/core/zdex_atomic_buyback_v1.py",
    "src/core/zdex_buyback_price_authority_v1.py",
    "src/core/zdex_buyback_price_safety_v1.py",
    "src/core/zdex_buyback_spend_v1.py",
    "src/core/zdex_fee_allocation_receipt_verification_v1.py",
    "src/core/zdex_fee_allocation_types_v1.py",
    "src/core/zdex_purchase_burn_route_types_v1.py",
    "src/core/zdex_verified_buyback_spend_v1.py",
    "src/core/zdex_verified_fee_ingress_slice_v1.py",
    RENDERER,
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)

BOUNDS = [
    "One public verification API moves to integration. Exact envelope, candidate, journal and marker types remain in core; both preparation phases take data and invoke no verifier.",
    "All fourteen final marker fields and eight nested fee-ingress fields retain their existing domains and canonical values for the baseline positive subject.",
    "The former ordering remains candidate ownership, governed selection, head/Bound admission, deployment binding, policy, occurrence, state/Oracle, Succinct/nonempty receipt, minimum route/Spot journal ceiling, one callback and fee-ingress derivation.",
    "The exact Bound verifier alone is accepted; normal non-None backend returns and exceptions retain RECEIPT_VERIFICATION_FAILED with fixed detail. Bound authority-source revalidation remains active.",
    "Both journal ceilings have independent equality and one-byte-over controls, including a receipt longer than the journal ceiling and empty-receipt precedence.",
    "The prepared execution copy owns the complete twelve-coordinate authority head, profile, journal, fee state, policies and both nested price witnesses. Retained callback aliases cannot relabel the returned marker or cause a post-callback ownership rejection.",
    "Prepared request and marker sources are rebound to the exact journal. An independent one-field authority-root substitution or verifier-root substitution rejects before callback and fee-ingress derivation.",
    "The authority root binds the retained owned head; the verifier root binds the executing Bound identity read by the shell. Coherent replacement of the whole head plus its root is outside this private prepared-executor contract.",
    "Owning a malformed exact head with a valid Bound now rejects before I/O. The malformed-head plus invalid-Bound type precedence remains unchanged; this is a named strengthening over the baseline.",
    "The private completion factory derives fee ingress only when the shell calls it after successful verification. Preparation, detachment and a failed callback derive no fee-ingress witness.",
    "Five mechanical source mutations below name ordinary runtime laws for exact request bytes, exactly one callback, the minimum ceiling, head ownership and post-callback fee-ingress order. Explicit mutation-constructor tests remain separate evidence.",
]
NONCLAIMS = [
    "Synthetic SHADOW receipts and recorder backends do not qualify a real cryptographic receipt, measured guest, deployed verifier or release.",
    "Prepared records and private data factories are not verification witnesses or publication gates. The completed marker remains a reference SHADOW value with no settlement authority.",
    "Complete owned-head data does not authenticate the current authority store. Current-head revalidation, durable publication and destination enforcement remain separate obligations.",
    "The shared purchase/burn authority helper, three atomic-buyback callback rows and the Bound registry/backend row remain open. Direct AST checks do not establish transitive whole-core FCIS.",
    "The tests assume an intact Python process and operating system; arbitrary private imports, process compromise and cloud/operator compromise are outside these ownership laws.",
    "SHADOW_PROFILE_REQUIRED and GOVERNED_SPOT_RELEASE_MISMATCH retain their implementation but lack reachable positive-fixture negative controls in this suite.",
    "No economic policy, rounding, journal or wire field, hash domain, Rust guest, existing Lean theorem or live authority changes.",
    "ESSO, Kani, randomized property campaigns, full Rust/Lean/RISC0 builds, production gates and real proof generation are not executed by this declaration. Whole V3, formal-core completeness and production value safety remain open.",
]

CALL_BLOCK = [
    "        receipt_verifier.verify_profile_lane_receipt(",
    "            owned.receipt_bytes,",
    "            profile=owned.profile,",
    "            lane_id=LaneIdV1.SPOT_LIQUIDITY,",
    "            expected_module_release_id=owned.expected_module_release_id,",
    "            expected_image_id=owned.expected_image_id,",
    "            expected_journal_bytes=owned.expected_journal_bytes,",
    "        )",
]
POSITIVE_LAW = TEST + "::test_shell_executes_exactly_the_prepared_request_once_and_mints_the_pinned_marker"
MUTATIONS = [
    {
        "description": "Tier 1: send journal bytes as receipt bytes; the ordinary positive law observes a different recorder request.",
        "killed_by": POSITIVE_LAW,
        "mutant": {
            "path": SHELL,
            "needle_lines": ["            owned.receipt_bytes,"],
            "replacement_lines": ["            owned.expected_journal_bytes,"],
        },
    },
    {
        "description": "Tier 1: execute the same Bound callback twice; the ordinary positive law observes two requests instead of one.",
        "killed_by": POSITIVE_LAW,
        "mutant": {
            "path": SHELL,
            "needle_lines": CALL_BLOCK,
            "replacement_lines": CALL_BLOCK + CALL_BLOCK,
        },
    },
    {
        "description": "Tier 1: use the larger journal ceiling; the ordinary boundary law observes missing JOURNAL_TOO_LARGE rejection in pure preparation.",
        "killed_by": TEST + "::test_journal_ceiling_is_the_route_spot_minimum_with_equality_admitted",
        "mutant": {
            "path": PREPARATION,
            "needle_lines": ["    if len(journal_bytes) > min(route.max_journal_bytes, spot_release.max_journal_bytes):"],
            "replacement_lines": ["    if len(journal_bytes) > max(route.max_journal_bytes, spot_release.max_journal_bytes):"],
        },
    },
    {
        "description": "Tier 1: retain the input head alias in prepared data; the ordinary ownership law observes a typed authority-root rejection after caller mutation where a detached snapshot must succeed.",
        "killed_by": TEST + "::test_prepared_subject_is_detached_from_candidate_head_and_selection_graphs",
        "mutant": {
            "path": PREPARATION,
            "needle_lines": ["        authority_head=head,"],
            "replacement_lines": ["        authority_head=authority_head,"],
        },
    },
    {
        "description": "Tier 1: derive fee ingress before the callback; the ordinary lifecycle law observes derivation before any backend call.",
        "killed_by": TEST + "::test_fee_ingress_witness_is_derived_only_after_callback_success",
        "mutant": {
            "path": SHELL,
            "needle_lines": ["    try:", "        receipt_verifier.verify_profile_lane_receipt("],
            "replacement_lines": [
                "    try:",
                "        _build_verified_zdex_buyback_spot_safety_purchase_v2(owned)",
                "        receipt_verifier.verify_profile_lane_receipt(",
            ],
        },
    },
]


def main() -> None:
    _render(
        "buyback-spot-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "Two pure preparation phases bind the complete governed SHADOW Spot "
            "receipt subject; integration executes its exact request once and "
            "constructs the existing marker from the detached executed copy. "
            "Finite controls observe baseline compatibility and authority, "
            "price-witness and fee-ingress ownership and sequencing."
        ),
        invariant="V3-BUYBACK-SPOT-SHADOW-OWNED-EXECUTION-SUBJECT",
        families=["differential", "stateful", "mutation"],
        bounds=BOUNDS,
        nonclaims=NONCLAIMS,
        rejection_reason=(
            "Invalid admission rejects before the callback with no marker or "
            "fee-ingress derivation. Callback failure derives no fee ingress; "
            "a later successful verification derives it exactly once after the "
            "backend. No economic state write or publication is modeled."
        ),
        created_date="2026-09-07",
    )
    path = ROOT / PACKET
    packet = json.loads(path.read_text(encoding="ascii"))
    packet["mutations"] = MUTATIONS
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
