"""Declare the SHADOW tokenomics lane receipt preparation boundary.

Replay: ``python3 -B -m experiments.v3_tokenomics_lane_receipt_boundary_v1.render_evidence``
Rendering writes only the declared THV1 packet. It executes no test, receipt
verifier, release activation, publication, or production settlement action.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

BOUNDARY_TEST = "tests/integration/test_zdex_tokenomics_lane_verifier_boundary_v1.py"
SHELL = "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py"
COMMON = "src/core/zdex_tokenomics_lane_receipt_common_v1.py"

TESTS = (
    BOUNDARY_TEST,
    "tests/core/test_zdex_tokenomics_lane_coordinator_v1.py",
    "tests/core/test_zdex_tokenomics_hostile_boundaries_v1.py",
    "tests/core/test_zdex_purchase_burn_route_v1.py",
    "tests/integration/test_economic_epoch_verifier_boundary_v1.py",
)

SOURCES = (
    # Four source files changed by the extraction.
    COMMON,
    "src/core/zdex_tokenomics_lane_receipt_verification_v1.py",
    "src/core/zdex_tokenomics_fee_lane_receipt_verification_v1.py",
    SHELL,
    # Unchanged leaf, coordinator, profile, and callback dependencies.
    "src/core/zdex_tokenomics_lane_v1.py",
    "src/core/zdex_tokenomics_fee_lane_v1.py",
    "src/core/zdex_tokenomics_lane_coordinator_v1.py",
    "src/core/zdex_tokenomics_fee_lane_coordinator_v1.py",
    "src/core/global_economic_profile_snapshot_v1.py",
    "src/core/zdex_fee_allocation_profile_binding_v1.py",
    "src/core/zdex_purchase_burn_receipt_verification_v1.py",
    "src/core/zdex_fee_allocation_receipt_verification_v1.py",
    "experiments/v3_tokenomics_lane_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)


def main() -> None:
    _render(
        "tokenomics-lane-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "The burn-lane and fee-lane SHADOW receipt paths prepare exact detached "
            "subjects in core, then the integration shell executes the supplied "
            "reference callback and mints the existing process-local marker from "
            "the detached executed subject. The bounded corpus observes all 16 "
            "marker fields, the exact receipt/image/journal request, callback "
            "return-value compatibility, preparation ordering, and alias safety."
        ),
        invariant="V3-TOKENOMICS-SHADOW-RECEIPT-OWNED-EXECUTION-SUBJECT",
        families=["stateful", "mutation"],
        change_kind="behavior_change",
        created_date="2026-09-07",
        rejection_reason=(
            "Exact candidate, governed-profile, composition, journal, receipt-kind, "
            "and byte-ceiling failures occur before callback I/O. A callback error "
            "propagates without a marker. The shell snapshots the prepared subject "
            "before I/O, ignores a non-None callback result as before, and mints only "
            "from the detached subject; the SHADOW marker creates no publication or "
            "settlement effect."
        ),
        bounds=[
            "The four changed source files preserve the burn and fee candidate APIs, exact first-rejection order, existing composition and profile bindings, and the existing 16-field VerifiedZDEXTokenomicsLaneV1 marker shape.",
            "PreparedZDEXTokenomicsLaneReceiptV1 carries the exact 16 marker fields plus receipt bytes and canonical lane-journal bytes; expected image identity remains derived from the governed coordinator release.",
            "Burn and fee leaf modules, coordinators, profile binders, and the existing receipt Protocol remain pinned dependencies. The extraction moves callback execution into the integration shell while core performs data preparation only.",
            "Core preparation performs no callback invocation. The shell performs exactly one supplied callback invocation with the prepared receipt bytes, expected image ID, and expected journal bytes.",
            "Invalid context, receipt kind, empty bytes, journal ceiling, candidate type, and composition cases preserve their prior exception classes/messages and record no callback call.",
            "The reference callback's non-None return value remains ignored, preserving the historical generic callback contract while the separate measured Bound contract retains its own success rule.",
            "A detached snapshot is fixed before I/O, so callback-side mutation of candidate or prepared aliases cannot relabel the returned SHADOW marker or its 16 fields.",
            "The new boundary test supplies independent field/request expectations for both burn and fee lanes, plus exact binding-root pins retained from the pre-extraction fixtures.",
            "The four mechanical mutation rows below correspond to the executed in-test mutants and their ordinary no-call, alias, exact-request, and digest-binding killer laws.",
            "AST checks establish direct module declarations and call placement only. They do not establish transitive core purity, runtime qualification, or whole-program completion.",
        ],
        nonclaims=[
            "The marker is a reference SHADOW marker with no publication, settlement, finality, migration, withdrawal, or production authority.",
            "Receipt verifiers in the corpus are deterministic recorders. No cryptographic receipt, measured deployment, guest/image qualification, or native Rust/Lean parity is claimed.",
            "The Bound verifier registry, the leaf fee callback, and the purchase-burn receipt Protocol remain separate open obligations; this boundary declaration does not close them.",
            "The two lane preparations and their shell wrappers do not establish full FCIS closure, universal runtime/compiler refinement, complete caller migration, or production value safety.",
            "Private marker construction and callback ports assume intact interpreter, process, operating system, and publisher environments.",
            "Rendering writes this new evidence declaration only; it changes no wire field, policy constant, release value, or historical packet, and does not execute tests or mutation evidence.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-tokenomics-lane-receipt-boundary-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": (
                "Tier 1: invoke the burn preparation callback before the core preparation; "
                "the ordinary no-call law observes the forbidden callback on a conditional "
                "receipt before the expected rejection."
            ),
            "killed_by": BOUNDARY_TEST + "::test_invalid_context_kind_journal_and_shape_reject_before_callback",
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "    prepared = prepare_zdex_tokenomics_lane_receipt_v1(candidate, governed)"
                ],
                "replacement_lines": [
                    "    receipt_verifier.verify_succinct_receipt(",
                    "        candidate.receipt.receipt_bytes,",
                    "        expected_image_id=governed._fields.coordinator_release.guest_image_id,",
                    "        expected_journal_bytes=b'',",
                    "    )",
                    "    prepared = prepare_zdex_tokenomics_lane_receipt_v1(candidate, governed)",
                ],
            },
        },
        {
            "description": (
                "Tier 1: mint from the caller-held prepared alias after callback I/O; "
                "the ordinary alias mutation law observes the forged coordinator field."
            ),
            "killed_by": BOUNDARY_TEST + "::test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker",
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "    return _build_verified_zdex_tokenomics_lane_v1(owned)"
                ],
                "replacement_lines": [
                    "    return _build_verified_zdex_tokenomics_lane_v1(prepared)"
                ],
            },
        },
        {
            "description": (
                "Tier 1: send the module image instead of the governed coordinator image; "
                "the ordinary exact-request law observes the changed callback request."
            ),
            "killed_by": BOUNDARY_TEST + "::test_shell_executes_exactly_the_prepared_receipt_image_and_journal",
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "        expected_image_id=owned.expected_image_id,"
                ],
                "replacement_lines": [
                    "        expected_image_id=owned.verified_fields.module_image_id,"
                ],
            },
        },
        {
            "description": (
                "Tier 1: omit the prepared digest-to-request check; the ordinary digest "
                "binding law observes an unbound receipt subject before callback I/O."
            ),
            "killed_by": BOUNDARY_TEST + "::test_prepared_record_requires_exact_types_and_field_to_request_binding",
            "mutant": {
                "path": COMMON,
                "needle_lines": [
                    "    _require_prepared_zdex_tokenomics_lane_digests_v1(prepared)"
                ],
                "replacement_lines": ["    pass"],
            },
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
