"""Declare the exact composition receipt preparation/execution/binding subject.

Replay: python3 -B -m experiments.v3_composition_receipt_boundary_v1.render_evidence
Rendering executes no test, verifier, proof, publication or release activation.
Historical evidence packets remain unchanged.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

SOURCES = (
    "src/core/lane_composition_receipt_verification_v1.py",
    "src/core/route_composition_receipt_verification_v1.py",
    "src/integration/lane_composition_receipt_verification_v1.py",
    "src/integration/route_composition_receipt_verification_v1.py",
    "src/integration/isolated_profile_receipt_ports_v1.py",
    "src/integration/isolated_asset_receipt_pipeline_v1.py",
    "tests/core/receipt_composition_fixtures_v1.py",
    "experiments/v3_composition_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
    "docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md",
)
BOUNDARY_TEST = "tests/integration/test_receipt_composition_boundary_v1.py"
TESTS = (
    "tests/core/test_lane_module_release_route_binding_v1.py",
    "tests/core/test_asset_transfer_epoch_allocation_v1.py",
    "tests/core/test_receipt_backed_perps_margin_lane_composition_v1.py",
    "tests/core/test_global_settlement_abi_v1.py",
    "tests/core/test_global_settlement_fcis_exact_ownership_v1.py",
    "tests/integration/test_lane_module_receipt_boundary_v1.py",
    "tests/integration/test_isolated_asset_receipt_pipeline_v1.py",
    BOUNDARY_TEST,
    "tests/integration/test_isolated_profile_receipt_ports_v1.py",
)
PORT_PATH = "src/integration/isolated_profile_receipt_ports_v1.py"
SNAPSHOT_ORDINARY_LAW = (
    BOUNDARY_TEST
    + "::test_prepared_alias_mutation_during_io_cannot_relabel_execution"
)


def main() -> None:
    _render(
        "composition-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "Asset and perps-margin coordinator plus route receipt phases prepare "
            "immutable exact subjects in core; measured isolated role ports execute "
            "those subjects and pure binders accept only matching opaque execution "
            "evidence. The declared tests exercise preserved witness fields and "
            "wire identities on a bounded corpus."
        ),
        invariant="V3-COMPOSITION-RECEIPT-OWNED-EXECUTION-SUBJECT",
        families=["stateful", "mutation"],
        change_kind="behavior_change",
        created_date="2026-09-07",
        rejection_reason=(
            "Wrong coordinator or route role/context, retained authority drift, "
            "backend refusal or non-None result, and mismatched complete execution "
            "subjects reject before final witness mint. Tests retain the relevant "
            "input/state bytes and verifier-call observations; epoch and publisher "
            "contracts remain separate surfaces."
        ),
        bounds=[
            "Asset and perps-margin coordinator and route candidate/final witness fields, schemas and binding-root identities remain unchanged.",
            "Core preparation takes only a candidate; pure binding consumes exact opaque execution evidence over every final witness coordinate plus receipt and journal bytes.",
            "The shell accepts only the exact measured factory port, snapshots the prepared subject before I/O, checks role/profile/lane/release coordinates and retained authority, and requires exact None backend success.",
            "Existing guard order, transition recomputation, canonical journal bytes and release ceilings remain bounded; route receipts admit one through eight paired distinct lanes.",
            "The nine pinned test files include positive coordinator variants, route controls, exact subject substitutions, retained aliases, failure propagation and deterministic rebinding.",
            "Two executable Tier 1 records cover coordinator and route omission of the pre-I/O snapshot; the ordinary alias law observes the relabeled execution subject.",
            "Selective synthetic hash-function substitutions exercise the old entry-point domains of receipt and journal digests, structural and journal roots, and ordered lane binding roots; later consumers retain their original nonzero constraints.",
        ],
        nonclaims=[
            "Packet rendering does not execute tests or establish completeness, source refinement or production authority.",
            "The process replies and unit evidence are synthetic. No genuine receipt, cryptographic validity, measured deployment, release qualification or production value-safety claim follows.",
            "Moving coordinator and route callback invocation to integration does not establish purity for BoundEconomicReceiptVerifierV1, epoch verification or other transitive callback owners; those FCIS obligations remain open.",
            "The measured role-port contract supplies execution capability for the bounded tests only. Pure preparation and binding establish no store, deployment, current-head, publication, finality, migration or withdrawal authority.",
            "No wire field, policy constant, canonical identity, historical packet or native proof artifact is changed by this renderer.",
            "Synthetic hash substitution establishes no hash preimage or genuine cryptographic receipt claim.",
            "Source pins are computed when root later renders the append-only packet; no final source hash is hardcoded in this declaration.",
            "Private token and measured-port controls assume interpreter and process integrity and do not protect a compromised publisher, operating system or infrastructure.",
            "The declared corpus and two named mutations are finite evidence; they do not establish universal refinement or whole-program completeness.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-composition-receipt-boundary-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: omit the coordinator prepared-subject snapshot before I/O; the ordinary alias law observes the forbidden relabeled execution acceptance.",
        "killed_by": SNAPSHOT_ORDINARY_LAW,
        "mutant": {
            "path": PORT_PATH,
            "needle_lines": [
                "        owned = snapshot_prepared_lane_composition_receipt_v1(prepared)"
            ],
            "replacement_lines": ["        owned = prepared"],
        },
    }, {
        "description": "Tier 1: omit the route prepared-subject snapshot before I/O; the ordinary alias law observes the forbidden relabeled execution acceptance.",
        "killed_by": SNAPSHOT_ORDINARY_LAW,
        "mutant": {
            "path": PORT_PATH,
            "needle_lines": [
                "        owned = snapshot_prepared_route_composition_receipt_v1(prepared)"
            ],
            "replacement_lines": ["        owned = prepared"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
