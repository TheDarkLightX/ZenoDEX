"""Declare the exact module receipt preparation/execution/binding subject.

Replay: python3 -B -m experiments.v3_module_receipt_boundary_v1.render_evidence
Rendering executes no test, verifier, proof, publication or release activation.
Historical evidence packets remain unchanged.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

SOURCES = (
    "src/core/lane_module_receipt_verification_v1.py",
    "src/core/asset_transfer_receipt_admission_v1.py",
    "src/integration/lane_module_receipt_verification_v1.py",
    "src/integration/isolated_profile_receipt_ports_v1.py",
    "src/integration/isolated_asset_receipt_pipeline_v1.py",
    "tests/core/lane_module_receipt_fixtures_v1.py",
    "tests/integration/asset_receipt_pipeline_fixtures_v1.py",
    "tests/integration/publisher_receipt_port_fixtures_v1.py",
    "tests/data/asset_transfer_global_allocation_v1_golden.json",
    "tools/render_asset_transfer_global_allocation_v1_golden.py",
    "tests/data/asset_transfer_epoch_position_v1_golden.json",
    "tools/render_asset_transfer_epoch_position_v1_golden.py",
    "experiments/v3_module_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
)
BOUNDARY_TEST = "tests/integration/test_lane_module_receipt_boundary_v1.py"
TESTS = (
    BOUNDARY_TEST,
    "tests/core/test_asset_transfer_custody_receipt_verification_v1.py",
    "tests/core/test_asset_transfer_policy_membership_v1.py",
    "tests/core/test_global_settlement_abi_v1.py",
    "tests/core/test_lane_module_release_route_binding_v1.py",
    "tests/core/test_managed_asset_policy_membership_v1.py",
    "tests/core/test_perps_margin_release_receipt_binding_v1.py",
    "tests/core/test_receipt_backed_perps_margin_lane_composition_v1.py",
    "tests/core/test_global_settlement_fcis_exact_ownership_v1.py",
    "tests/core/test_global_settlement_abi_v1_resource_bounds.py",
    "tests/core/test_asset_transfer_global_allocation_v1.py",
    "tests/core/test_asset_transfer_receipt_admission_v1.py",
    "tests/core/test_asset_transfer_epoch_position_v1.py",
    "tests/integration/test_isolated_profile_receipt_ports_v1.py",
    "tests/integration/test_isolated_asset_receipt_pipeline_v1.py",
    "tests/integration/test_isolated_custody_asset_receipt_pipeline_v1.py",
    "tests/integration/test_global_economic_durable_publisher_v1.py",
    "tests/integration/test_global_economic_publication_outcomes_v1.py",
    "tests/integration/test_global_economic_known_outcomes_v1.py",
)


def main() -> None:
    _render(
        "module-receipt-boundary", SOURCES, TESTS,
        claim="Four module receipt families prepare exact immutable requests in the core; measured isolated shell ports execute them and the pure binder accepts only matching execution evidence. Global allocation lifting consumes exact closed witness or rejection types.",
        invariant="V3-MODULE-RECEIPT-OWNED-EXECUTION-SUBJECT",
        families=["stateful", "mutation"],
        change_kind="behavior_change", created_date="2026-09-07",
        rejection_reason="Invalid module context rejects before verifier I/O. Verifier failures, changed authority and mismatched execution cannot mint a final witness; tests retain exact input state and verifier-call observations. Existing isolated publisher tests separately preserve complete PRE, exact retry and committed-but-indeterminate outcomes.",
        bounds=[
            "Legacy transfer, custody transfer, managed-asset lifecycle and perps margin keep their existing candidate and nine-field final witness formats.",
            "The four core preparations take candidate values only; named direct receipt callbacks and integration imports are mechanically forbidden in this module.",
            "The shell admits exact factory ports; ordinary callbacks and caller-created success values cannot supply execution evidence.",
            "Role, profile, lane and module release mismatches reject before the simulated verifier endpoint.",
            "Execution evidence binds all six request fields, all nine final witness fields and the measured verifier binding root; changed complete bytes with consistent digests reject against old evidence.",
            "A caller-retained preparation is detached before I/O; later alias changes cannot relabel the owned execution subject.",
            "Changed role, release, lane or callable during I/O and non-None backend success prevent issuing execution evidence.",
            "Exact re-binding is deterministic and performs no additional receipt execution.",
            "The snapshot-omission mutant is executed in memory; the ordinary alias law reveals its incorrect acceptance.",
            "Retained scenario tests cover canonical input, policy and release guards, ordered rejection, custody and resource boundaries.",
            "Global allocation lifting propagates the exact closed rejection types and refuses unexpected or subclass results before reading their fragment.",
            "The admission inventory pins the reviewed exact-type guards and the complete transitive core module list; it is a drift detector, not a whole-program proof.",
        ],
        nonclaims=[
            "The test oracle for new subject-substitution cases is a fixed field/role decision table (grade 2); the baseline comparison is a finite synthetic observation, not universal refinement.",
            "RISC0 process replies are explicitly synthetic. No genuine proof, custody guest, image ID, receipt ABI, wire field, policy constant or production release is changed or qualified.",
            "The four effectful verify APIs deliberately move from src.core to src.integration and require measured isolated ports. Unit-only helpers mint explicitly synthetic evidence and are not production adapters.",
            "BoundEconomicReceiptVerifierV1 and the coordinator, route, epoch and other core receipt callbacks remain separate FCIS obligations. Direct AST checks do not prove transitive purity.",
            "Private Python constructors and retained measured ports assume interpreter integrity; they do not protect against a compromised publisher, process, operating system or infrastructure.",
            "These functions grant no initialization ownership, current-head, publication, finality, migration or withdrawal authority. Full lane lifecycles, implementation refinement and deployment mediation remain open.",
            "No formal-core, whole-program, product-completion percentage or production value-safety claim follows from the packet or passing test counts.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-module-receipt-boundary-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: retain the caller preparation across I/O; the executed alias-change observation then incorrectly accepts relabeled execution evidence.",
        "killed_by": BOUNDARY_TEST + "::test_prepared_alias_mutation_during_io_cannot_relabel_execution",
        "mutant": {
            "path": "src/integration/isolated_profile_receipt_ports_v1.py",
            "needle_lines": ["        owned = snapshot_prepared_lane_module_receipt_v1(prepared)"],
            "replacement_lines": ["        owned = prepared"],
        },
    }, {
        "description": "Tier 1: weaken exact positive allocation-result admission to isinstance; the retained subclass law observes the forbidden fragment read.",
        "killed_by": "tests/core/test_asset_transfer_global_allocation_v1.py::test_positive_fragment_subclass_rejects_before_property_reads",
        "mutant": {
            "path": "src/core/asset_transfer_receipt_admission_v1.py",
            "needle_lines": ["    if type(module_fragment) is not VerifiedLaneAllocationFragmentV1:"],
            "replacement_lines": ["    if not isinstance(module_fragment, VerifiedLaneAllocationFragmentV1):"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
