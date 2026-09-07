"""Declare the bounded SHADOW fee-allocation receipt boundary.

Replay: ``python3 -B -m experiments.v3_fee_allocation_receipt_boundary_v1.render_evidence``
Rendering writes only this new THV1 packet.  It executes no receipt verifier,
cryptographic proof, publication, release activation, or production settlement.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

BOUNDARY_TEST = "tests/integration/test_zdex_fee_allocation_verifier_boundary_v1.py"
CORE = "src/core/zdex_fee_allocation_receipt_verification_v1.py"
SHELL = "src/integration/zdex_fee_allocation_receipt_verification_v1.py"

TESTS = (
    BOUNDARY_TEST,
    "tests/core/test_zdex_purchase_burn_route_v1.py",
    "tests/integration/test_economic_epoch_verifier_boundary_v1.py",
)

SOURCES = (
    CORE,
    SHELL,
    # Direct typed, profile, transition, journal, and receipt dependencies.
    "src/core/global_economic_proof_v1.py",
    "src/core/global_economic_refinement_snapshot_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/zdex_fee_allocation_profile_binding_v1.py",
    "src/core/zdex_fee_allocation_types_v1.py",
    "src/core/zdex_fee_allocation_v1.py",
    "src/core/zdex_purchase_burn_receipt_verification_v1.py",
    "src/core/zdex_purchase_burn_route_types_v1.py",
    "experiments/v3_fee_allocation_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)


def main() -> None:
    _render(
        "fee-allocation-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "The governed ZDEX fee-allocation leaf prepares an exact detached "
            "SHADOW receipt subject in core, then the integration shell executes "
            "the supplied reference callback once and mints the existing marker "
            "from the detached executed copy.  The bounded corpus observes all "
            "18 marker fields and the binding root, the exact receipt/module-image/"
            "canonical-journal request, pre-state fee ingress, buyback journal "
            "amount, callback compatibility, rejection order, and alias safety."
        ),
        invariant="V3-FEE-ALLOCATION-SHADOW-RECEIPT-OWNED-EXECUTION-SUBJECT",
        families=["stateful", "mutation"],
        change_kind="behavior_change",
        created_date="2026-09-07",
        rejection_reason=(
            "Candidate, governed-profile, binding, transition, receipt-kind, "
            "nonempty-byte, digest, and journal-ceiling failures occur before "
            "callback I/O.  Callback exceptions propagate without a marker.  "
            "The shell snapshots the prepared subject before I/O and mints only "
            "from that detached copy; the generic callback's non-None return "
            "value remains ignored, while the separate Bound contract keeps its "
            "own exact-None success rule."
        ),
        bounds=[
            "The core preparation keeps the existing candidate and governed-profile APIs, all 18 fields, binding-root domain, canonical allocation journal, receipt bytes, and first-error order.",
            "PreparedZDEXFeeAllocationReceiptV1 carries the complete 18-field marker subject plus receipt bytes and canonical journal bytes; expected_image_id is the selected module release image.",
            "Fee ingress is read from the owned predecessor fee state and buyback_quote_atoms from the recomputed allocation journal.  The journal ceiling remains min(module_release.max_journal_bytes, allocation_route.max_journal_bytes).",
            "The integration shell owns the former verification entry point, detaches the prepared subject before I/O, makes exactly one callback request with receipt bytes, module image, and journal bytes, and constructs the marker from the executed copy.",
            "Invalid candidate/profile/occurrence/allocation, receipt-kind, empty-byte, and below-ceiling cases preserve their prior exception classes/messages and make zero callback calls; paired empty-receipt and ceiling failures retain the earlier rejection. The new prepared-subject boundary also rejects unsupported types and unbound digests before callback execution.",
            "The reference recorder tests include callback rejection and True/object/bytes/zero return values, preserving the historical ignored-result behavior without promoting it to measured verifier evidence.",
            "The detached subject prevents callback-side mutation of the candidate, governed release graph, or caller-held prepared alias from relabeling any marker field or binding root.",
            "The three pinned test files cover the new focused boundary, relocated route call sites, and the epoch inventory that records the closed fee leaf together with remaining core callback owners.",
            "The four mechanical mutation rows below use structure-preserving substitutions and retained ordinary no-call, alias, exact-request, and digest-binding laws; they do not rely on mutant-generator test names.",
            "AST and source pins establish direct declaration and call placement only.  They do not establish transitive core purity, cryptographic validity, runtime qualification, or whole-program completion.",
        ],
        nonclaims=[
            "The marker and prepared subject remain process-local SHADOW/reference data with no publication, settlement, finality, migration, withdrawal, or production authority.",
            "Recorder callbacks and fixed roots qualify no real receipt, cryptographic proof, measured deployment, guest image, release capability, or Rust/Lean parity.",
            "The remaining purchase/burn callbacks and governed wrappers, atomic buyback module/coordinator/route receipt callbacks, buyback Spot safety verification, and the Bound deployment registry/backend execution boundary remain separate FCIS obligations.",
            "This leaf extraction does not establish full FCIS closure, universal runtime/compiler refinement, complete caller migration, or production value safety.  The fee callback's surrounding coordinator and publication path remain separate surfaces.",
            "The generic callback retains its historical ignored return value; the separate Bound verifier's exact-None rule is unchanged and outside this boundary.",
            "Private marker construction and callback ports assume an intact interpreter, process, operating system, and publisher environment and do not protect a compromised host.",
            "Rendering writes this new evidence declaration only; it changes no wire field, policy constant, release value, historical packet, or production artifact, and it does not execute tests or evidence.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-fee-allocation-receipt-boundary-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": (
                "Tier 1: invoke the callback before core preparation; the ordinary "
                "reference-order no-call law observes a callback on a conditional "
                "receipt before the expected rejection."
            ),
            "killed_by": (
                BOUNDARY_TEST
                + "::test_invalid_input_rejects_before_callback_in_the_reference_order"
            ),
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "    prepared = prepare_zdex_fee_allocation_receipt_v1(candidate, governed)"
                ],
                "replacement_lines": [
                    "    receipt_verifier.verify_succinct_receipt(",
                    "        candidate.receipt.receipt_bytes,",
                    "        expected_image_id=governed._fields.module_release.guest_image_id,",
                    "        expected_journal_bytes=b'',",
                    "    )",
                    "    prepared = prepare_zdex_fee_allocation_receipt_v1(candidate, governed)",
                ],
            },
        },
        {
            "description": (
                "Tier 1: mint from the caller-held prepared alias after callback I/O; "
                "the ordinary alias law observes the forged module-release field."
            ),
            "killed_by": (
                BOUNDARY_TEST
                + "::test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker"
            ),
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "    return _build_verified_zdex_fee_allocation_v1(owned)"
                ],
                "replacement_lines": [
                    "    return _build_verified_zdex_fee_allocation_v1(prepared)"
                ],
            },
        },
        {
            "description": (
                "Tier 1: bind the coordinator image instead of the selected module "
                "image; the ordinary exact-request law observes the changed image "
                "and marker binding root."
            ),
            "killed_by": BOUNDARY_TEST + "::test_shell_executes_exactly_the_prepared_receipt_image_and_journal",
            "mutant": {
                "path": CORE,
                "needle_lines": [
                    "        fields.module_release.guest_image_id,"
                ],
                "replacement_lines": [
                    "        fields.coordinator_release.guest_image_id,"
                ],
            },
        },
        {
            "description": (
                "Tier 1: omit the prepared digest-to-request check; the ordinary "
                "prepared-record law observes receipt bytes whose digest is not "
                "bound before callback execution."
            ),
            "killed_by": BOUNDARY_TEST + "::test_prepared_record_requires_exact_types_and_field_to_request_binding",
            "mutant": {
                "path": CORE,
                "needle_lines": [
                    "    _require_prepared_zdex_fee_allocation_digests_v1(prepared)"
                ],
                "replacement_lines": ["    pass"],
            },
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
