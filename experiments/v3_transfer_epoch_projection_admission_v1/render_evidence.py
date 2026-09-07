"""Declare consumed transfer-epoch projection and isolated publication evidence.

Replay: python3 -B -m experiments.v3_transfer_epoch_projection_admission_v1.render_evidence
Rendering pins the reviewed subject; it does not run Python, Lean or Rust tests.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_epoch_runtime_projection_v1.render_evidence import (
    SOURCES as PREDECESSOR_SOURCES,
)

TESTS = (
    "tests/core/test_asset_transfer_epoch_projection_admission_v1.py",
    "tests/core/test_asset_transfer_receipt_admission_v1.py",
    "tests/core/test_asset_transfer_global_allocation_v1.py",
    "tests/core/test_asset_transfer_epoch_allocation_v1.py",
    "tests/core/test_asset_transfer_epoch_position_v1.py",
    "tests/core/test_asset_transfer_epoch_projection_v1.py",
    "tests/core/test_asset_transfer_epoch_economic_tables_v1.py",
    "tests/formal/test_lean_asset_transfer_epoch_economic_tables_v1.py",
    "tests/integration/test_asset_transfer_epoch_projection_publication_v1.py",
    "tests/integration/test_isolated_asset_publication_v1.py",
    "tests/integration/test_global_economic_custody_pipeline_v1.py",
)
SOURCES = tuple(path for path in dict.fromkeys(PREDECESSOR_SOURCES + (
    "src/core/asset_transfer_epoch_allocation_v1.py",
    "src/core/asset_transfer_receipt_admission_v1.py",
    "src/integration/isolated_asset_receipt_pipeline_v1.py",
    "src/integration/global_economic_durable_publisher_v1.py",
    "src/integration/global_economic_durable_epoch_v1.py",
    "src/integration/global_economic_epoch_journal_v1.py",
    "src/integration/economic_command_bls_signature_verifier_v1.py",
    "src/integration/isolated_profile_receipt_ports_v1.py",
    "src/integration/global_receipt_verifier_v1.py",
    "tests/integration/custody_asset_receipt_pipeline_fixtures_v1.py",
    "tests/integration/asset_receipt_pipeline_fixtures_v1.py",
    "tests/integration/publisher_receipt_port_fixtures_v1.py",
    "tests/integration/test_global_economic_sealed_bls_pipeline_v1.py",
    "tests/core/test_economic_receipt_verifier_release_v1.py",
    "zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs",
    "zk/global_settlement_abi_v1/tests/asset_transfer_epoch_projection_admission.rs",
    "zk/global_settlement_abi_v1/tests/asset_transfer_custody_release_route_binding.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_lane_module_custody.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_custody_semantics.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_policy_registry.rs",
    "zk/global_settlement_abi_v1/src/economic_command_authentication.rs",
    "zk/global_settlement_abi_v1/src/economic_command_authentication/types.rs",
    "zk/global_settlement_abi_v1/src/economic_command_authentication/witness.rs",
    "zk/global_settlement_abi_v1/src/economic_command_authorization_registry.rs",
    "zk/global_settlement_abi_v1/src/economic_command_signature_verifier_registry.rs",
    "zk/global_settlement_abi_v1/src/economic_command_signature_verifier_deployment.rs",
    "zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs",
    "zk/global_settlement_abi_v1/src/release.rs",
    "tools/render_asset_transfer_global_allocation_v1_golden.py",
    "tools/render_asset_transfer_epoch_position_v1_golden.py",
    "tests/data/asset_transfer_global_allocation_v1_golden.json",
    "tests/data/global_accounting_allocation_projection_v1_golden.json",
    "tests/data/asset_transfer_epoch_position_v1_golden.json",
    "experiments/v3_transfer_epoch_projection_admission_v1/render_evidence.py",
)) if path not in TESTS)


def main() -> None:
    _render(
        "transfer-epoch-projection-admission", SOURCES, TESTS,
        created_date="2026-09-07",
        claim=(
            "Python and Rust epoch fragment admission consume the owned pure runtime "
            "projection after the existing full allocation relation accepts, compare the "
            "complete derived state with the advertised current state, and pass the derived "
            "values to fragment admission. The Python isolated custody publisher exercises "
            "this path with real command signatures and synthetic receipt processes."
        ),
        invariant="V3-ASSET-EPOCH-CHECKED-PROJECTION-ADMISSION",
        families=["stateful", "differential", "formal", "mutation"],
        rejection_reason=(
            "Relation failure precedes projection construction. Derived state drift precedes "
            "fragment minting. Isolated allocation rejection preserves the complete logical "
            "ledger and head, with no later root receipt or commit. Module, coordinator and "
            "route receipt verification already occurred. Exact retries reverify and preserve "
            "the original committed record."
        ),
        bounds=[
            "The existing allocation relation and closed rejection family retain their order. Source position, context, private projection, claimant continuity, full frame and exact replay insertion remain mandatory.",
            "Given structurally valid candidate states, successful replay continuity requires both identities fresh and post.replay_state equal to the canonical predecessor plus one row. The existing 4096-row post bound therefore establishes room for construction.",
            "The focused Python suite consumes derived owned values at first and second epoch positions and checks complete input preservation. A structurally valid full 4096-row predecessor with omitted insertion returns GLOBAL_REPLAY_CONTINUITY_DRIFT before construction.",
            "The isolated history actually commits a backed custody transfer, reopens its ledger, rejects reuse of the committed nonce before construction, then commits a fresh nonce through the same fixed pipeline. Its exact retry reverifies without appending another bundle.",
            "A controlled runtime projection fault changes the history root after a valid relation. The full equality guard returns GLOBAL_PROJECTION_ROWS_DRIFT before fragment minting, root receipt verification or commit; a subsequent unmodified submission succeeds.",
            "The retained formal consumer reruns the existing fresh 23-module Std-only Lean closure with 19 unchanged theorem signatures. Its source pins bind the new Python admission while historical formal declarations remain intact.",
            "Rust replay is a separate command: cargo test --offline --locked --manifest-path zk/global_settlement_abi_v1/Cargo.toml --test asset_transfer_epoch_projection_admission --test asset_transfer_epoch_projection --test asset_transfer_epoch_position. Shared fixture metadata is regenerated by its recorded renderer commands; case data must remain unchanged.",
            "The native admission test includes ten existing release-binding fixture tests and adds three admission tests. Its command signatures and succinct receipts both use explicit synthetic backends; only the Python publisher history exercises real BLS.",
        ],
        nonclaims=[
            "Generic proposal construction retains structural TypeError/ValueError or AbiErrorV1 failures. This qualification applies to the consumed epoch path after its existing typed snapshot boundary, not every malformed public call or every possible consumer.",
            "The fresh replay-capacity implication is a reviewed property of existing guards plus bounded tests; no new Lean theorem proves the Python or Rust constructor universally.",
            "The 4096-row rejection is bounded core evidence. The isolated publisher history commits two epochs; it does not authenticate or execute a 4096-epoch capacity history.",
            "Leaf receipt verifiers are shell effects preceding allocation checks. Rejection here means no economic publication, replay consumption, history entry or outbox effect by this attempt; it does not mean zero verifier work or unchanged physical database files.",
            "Real BLS signatures do not qualify synthetic RISC0 receipts, fixture release coordinates, any rebuilt guest or production verifier. Rust ABI changes require selected consumer rebuild and release-specific requalification.",
            "The single-occurrence isolated mount is unchanged. Source authenticity, complete external custody finality, multi-command publication, universal runtime/compiler refinement, full functional-core completion and production value safety remain outside this checkpoint.",
            "The intact runtime, process and host remain assumptions. Projection ownership grants no independent source, finality, receipt or publication authority.",
            "No existing wire commitment, rounding direction, policy constant, guest image ID, publisher implementation, historical packet or live authority changes.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-transfer-epoch-projection-admission-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": (
            "Narrative controlled result fault: change the prospective history root after "
            "valid allocation binding. The existing equality gate rejects before minting "
            "or publication. This is not an external mechanical mutation score."
        ),
        "killed_by": (
            "tests/integration/test_asset_transfer_epoch_projection_publication_v1.py::"
            "test_projection_drift_rejects_before_fragment_root_receipt_and_commit"
        ),
        "narrative": True,
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
