"""Declare the bounded SHADOW purchase/burn receipt execution boundary.

Replay only after the frozen extraction is copied into the integration checkout:
``python3 -B -m experiments.v3_purchase_burn_receipt_boundary_v1.render_evidence``.
Rendering writes the new THV1 packet and executes no callback, receipt verifier,
proof, publication, release activation, or production settlement action.
"""

from __future__ import annotations

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

BOUNDARY_TEST = "tests/integration/test_zdex_purchase_burn_verifier_boundary_v1.py"
LEGACY_CORE = "src/core/zdex_purchase_burn_receipt_verification_v1.py"
PREPARATION = "src/core/zdex_purchase_burn_receipt_preparation_v1.py"
SHELL = "src/integration/zdex_purchase_burn_receipt_verification_v1.py"

# These are the six changed test paths: the new 135-case boundary, four
# import-only caller migrations, and the epoch callback-debt inventory.
TESTS = (
    BOUNDARY_TEST,
    "tests/core/test_zdex_purchase_burn_route_v1.py",
    "tests/core/test_zdex_purchase_burn_route_v2.py",
    "tests/core/test_zdex_tokenomics_lane_coordinator_v1.py",
    "tests/core/test_zdex_atomic_buyback_v1.py",
    "tests/integration/test_economic_epoch_verifier_boundary_v1.py",
)

SOURCES = (
    # Five changed production paths in the extraction.
    LEGACY_CORE,
    PREPARATION,
    SHELL,
    "src/integration/zdex_fee_allocation_receipt_verification_v1.py",
    "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py",
    # Direct authority, profile, receipt, journal, and price dependencies.
    "src/core/economic_receipt_verifier_deployment_v1.py",
    "src/core/economic_receipt_verifier_registry_v1.py",
    "src/core/global_economic_authority_head_v1.py",
    "src/core/global_economic_capability_profile_binding_v1.py",
    "src/core/global_economic_profile_snapshot_v1.py",
    "src/core/global_economic_proof_v1.py",
    "src/core/global_economic_refinement_snapshot_v1.py",
    "src/core/global_settlement_types_v1.py",
    "src/core/zdex_atomic_buyback_receipt_verification_v2.py",
    "src/core/zdex_buyback_price_authority_v1.py",
    "src/core/zdex_buyback_price_safety_v1.py",
    "src/core/zdex_fee_allocation_types_v1.py",
    "src/core/zdex_purchase_burn_effects_v1.py",
    "src/core/zdex_purchase_burn_route_types_v1.py",
    "experiments/v3_purchase_burn_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)

EARLY_CALLBACK_LAW = (
    BOUNDARY_TEST + "::test_invalid_v1_leaf_rejects_before_callback_in_the_reference_order"
)
EXACT_REQUEST_LAW = (
    BOUNDARY_TEST + "::test_shell_executes_exactly_the_prepared_receipt_image_and_journal"
)
CALLER_ALIAS_LAW = (
    BOUNDARY_TEST
    + "::test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker"
)
DIGEST_LAW = (
    BOUNDARY_TEST + "::test_prepared_record_requires_exact_types_and_field_to_request_binding"
)
GOVERNED_HEAD_ALIAS_LAW = (
    BOUNDARY_TEST
    + "::test_governed_head_profile_and_registry_alias_mutation_during_callback_cannot_relabel"
)


def main() -> None:
    _render(
        "purchase-burn-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "Six legacy purchase/burn receipt APIs prepare one exact detached "
            "SHADOW subject in core, then the integration shell executes that "
            "subject once and mints the existing reference marker from the "
            "executed copy. The bounded corpus observes all 15 leaf fields, "
            "the V2 zero-authority inner leaf plus existing four-field outer "
            "governed marker, exact receipt/module-image/canonical-journal "
            "requests, callback contracts, rejection order, and alias safety."
        ),
        invariant="V3-PURCHASE-BURN-SHADOW-RECEIPT-OWNED-EXECUTION-SUBJECT",
        families=["stateful", "mutation"],
        change_kind="behavior_change",
        created_date="2026-09-07",
        rejection_reason=(
            "Candidate, route/release/occurrence, journal/effect, price-authority, "
            "receipt-kind, nonempty-byte, digest, policy/epoch, and existing "
            "module-journal-ceiling failures reject before generic callback I/O. "
            "Callback exceptions return no marker. The shell snapshots the complete "
            "prepared subject before I/O and mints only from that executed copy."
        ),
        bounds=[
            "The retained marker identities, schemas, binding-root domains, and all 15 leaf fields remain unchanged: route/release/occurrence/profile, writer epoch, journal root/digest, effect-plan root, image, receipt digest/kind, authority/verifier roots, and V2 price-authority/policy roots.",
            "The six moved APIs are generic purchase V1, generic purchase V2, generic burn V1, governed purchase V1, governed purchase V2, and governed burn V1. Candidate, envelope, and final marker types remain core identities while the generic Protocol and execution wrappers live in integration.",
            "Plain V1 purchase and burn retain zero authority and verifier roots. Governed V2 retains a zero-authority inner V2 leaf and the existing outer four fields: verified leaf, authority-head root, verifier-binding root, and policy-registry root.",
            "Each generic preparation owns the candidate, preserves release/binding/effect and V2 price-authority checks, derives canonical journal bytes and SHA-256 digest fields, and retains only module_release.max_journal_bytes as the pre-callback journal ceiling. Equality accepts; this extraction adds no route or receipt ceiling.",
            "The shell snapshots the prepared request immediately before its one callback with exact receipt bytes, derived module image, and canonical journal bytes; all marker construction consumes that executed snapshot.",
            "Generic callback normal returns, including False and 0, remain ignored. The separate Bound verifier continues to require exact None and retains its own post-callback authority-source recheck.",
            "Governed ordering is candidate snapshot, exact head type, exact Bound type, complete owned-head reconstruction, retained authority helper, captured checked binding root, governed preparation, one Bound profile-lane call, and mint from the owned execution subject.",
            "The owned-head repair prevents callback-retained caller head, profile, registry, candidate, and prepared aliases from relabeling a returned marker. An exact malformed head with a valid Bound now rejects during owned-head reconstruction before I/O; the malformed-head plus invalid-Bound type precedence remains preserved.",
            "The six test pins cover the 135-case new boundary, four import-only caller migrations, and the epoch inventory that names the retained shared helper and other callback debt. Test pins are separate from source pins.",
            "The five Tier 1 rows below are mechanical source substitutions with unique frozen-source needles. Their killers are ordinary no-call, exact-request, alias, digest-binding, and governed-head-alias laws rather than mutation-constructor tests.",
            "AST/source placement and finite synthetic observations are drift controls. They do not establish transitive core purity, cryptographic validity, runtime qualification, or whole-program completion.",
        ],
        nonclaims=[
            "Prepared subjects and existing markers are process-local SHADOW/reference data. They grant no publication, settlement, finality, migration, withdrawal, or production authority.",
            "The corpus uses synthetic receipt fixtures and recorder callbacks. It qualifies no real cryptographic receipt, measured deployment, guest image, release capability, or live verifier backend.",
            "The retained _require_current_shadow_authority_v1 helper and the Bound verifier registry/backend remain OPEN core obligations. Other Bound callbacks and their consuming paths are outside this leaf extraction.",
            "This packet does not establish full FCIS closure, a whole-core or whole-path purity result, complete caller migration, runtime/compiler refinement, or production value safety.",
            "No Rust, Lean, RISC0, wire, hash-domain, policy, economics, release-selection, or publication authority claim follows from this declaration or its tests.",
            "Private factories, process-local tokens, recorder ports, and callback alias controls assume an intact interpreter, process, operating system, and publisher environment.",
            "Rendering writes only the new evidence declaration. It does not execute tests or mutations, alter a historical packet, or change source, policy, wire, release, or production artifacts.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-purchase-burn-receipt-boundary-v1.json"
    packet = json.loads(path.read_text(encoding="ascii"))
    packet["mutations"] = [
        {
            "description": (
                "Tier 1: invoke the generic callback before V1 preparation; the ordinary "
                "reference-order no-call law observes a conditional receipt callback before "
                "the expected pre-callback rejection."
            ),
            "killed_by": EARLY_CALLBACK_LAW,
            "mutant": {
                "path": SHELL,
                "needle_lines": ["    prepared = prepare_zdex_amm_purchase_receipt_v1(candidate)"],
                "replacement_lines": [
                    "    receipt_verifier.verify_succinct_receipt(",
                    "        candidate.receipt.receipt_bytes,",
                    "        expected_image_id=candidate.module_release.guest_image_id,",
                    "        expected_journal_bytes=b'',",
                    "    )",
                    "    prepared = prepare_zdex_amm_purchase_receipt_v1(candidate)",
                ],
            },
        },
        {
            "description": (
                "Tier 1: bind the V2 route image instead of the selected module image; "
                "the ordinary exact-request law observes the changed image."
            ),
            "killed_by": EXACT_REQUEST_LAW,
            "mutant": {
                "path": PREPARATION,
                "needle_lines": [
                    "            expected_image_id=owned.module_release.guest_image_id,"
                ],
                "replacement_lines": [
                    "            expected_image_id=owned.route_release.guest_image_id,"
                ],
            },
        },
        {
            "description": (
                "Tier 1: mint V1 purchase from the caller-held prepared alias after I/O; "
                "the ordinary alias law observes the forged release field."
            ),
            "killed_by": CALLER_ALIAS_LAW,
            "mutant": {
                "path": SHELL,
                "needle_lines": ["    return _build_verified_zdex_amm_purchase_v1(owned)"],
                "replacement_lines": ["    return _build_verified_zdex_amm_purchase_v1(prepared)"],
            },
        },
        {
            "description": (
                "Tier 1: omit prepared digest-to-request validation; the ordinary digest "
                "law admits a receipt subject whose field digest no longer names its bytes."
            ),
            "killed_by": DIGEST_LAW,
            "mutant": {
                "path": PREPARATION,
                "needle_lines": ["    _require_prepared_digests_v1(prepared, name=name)"],
                "replacement_lines": ["    pass"],
            },
        },
        {
            "description": (
                "Tier 1: restore a post-I/O governed burn read of the caller-held head; "
                "the ordinary governed-head alias law observes the relabeled marker root."
            ),
            "killed_by": GOVERNED_HEAD_ALIAS_LAW,
            "mutant": {
                "path": SHELL,
                "needle_lines": [
                    "    return _execute_prepared_zdex_burn_receipt_v1(",
                    "        prepared,",
                    "        _ProfileLaneReceiptVerifierV1(",
                    "            receipt_verifier,",
                    "            owned_profile,",
                    "            LaneIdV1.ZDEX_TOKENOMICS,",
                    "            prepared.verified_fields.module_release_id,",
                    "        ),",
                    "    )",
                ],
                "replacement_lines": [
                    "    verified = _execute_prepared_zdex_burn_receipt_v1(",
                    "        prepared,",
                    "        _ProfileLaneReceiptVerifierV1(",
                    "            receipt_verifier,",
                    "            owned_profile,",
                    "            LaneIdV1.ZDEX_TOKENOMICS,",
                    "            prepared.verified_fields.module_release_id,",
                    "        ),",
                    "    )",
                    "    object.__setattr__(",
                    '        verified._fields, "authority_head_root", authority_head.authority_root',
                    "    )",
                    "    return verified",
                ],
            },
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
