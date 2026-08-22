from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import LaneIdV1
from tools.check_m6_writer_inventory import (
    M6_LANE_IDS,
    REQUIRED_ASSURANCE_STATUSES,
    REQUIRED_COVERAGE_BINDINGS,
    CommandCoverageV1,
    CoverageBindingV1,
    WriterSpec,
    _release_gap,
    check_m6_writer_inventory,
    load_writer_inventory_manifest,
    main,
    scan_unregistered_value_writers,
    scan_writer_spec,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_m6_writer_inventory_is_explicit_and_unmounted() -> None:
    report = check_m6_writer_inventory(ROOT)

    assert report["ok"] is True
    assert report["m6_production_mounted"] is False
    assert report["production_authority"] is False
    assert report["findings"] == []
    assert report["entrypoint_count"] == 27
    assert report["coverage_row_count"] == 27
    assert report["writers_without_coverage"] == []
    assert report["release_ready"] is False
    assert report["release_gate_status"] == "BLOCKED_OPEN_COVERAGE"
    assert report["open_coverage_count"] == 27
    assert report["release_gaps"]
    entries = {entry["entrypoint_id"]: entry for entry in report["entrypoints"]}
    assert entries["legacy_tau_apply_app_tx"]["m6_mount_status"] == "UNMOUNTED_LEGACY"
    assert entries["legacy_tau_apply_app_tx"]["commit_port_route"] == "none"
    assert entries["legacy_tau_typed_proposal"]["kind"] == "legacy_typed_proposal_adapter"
    assert entries["m6_research_commit_direct"]["commit_port_route"] == (
        "M6CommitPortV1._publish_proposal"
    )
    assert entries["m6_research_commit_direct_batch"]["symbol"] == "publish_direct_batch"
    assert entries["m6_research_durable_direct_batch"]["commit_port_route"] == (
        "M6CommitPortV1.publish_direct_batch"
    )
    assert entries["separate_global_economic_durable_publisher"][
        "m6_mount_status"
    ] == "SEPARATE_RESEARCH_NOT_M6"
    assert entries["separate_global_economic_epoch_journal_commit"][
        "commit_port_route"
    ] == "none"
    coverage = {row["entrypoint_id"]: row for row in report["coverage_rows"]}
    assert set(coverage) == set(entries)
    assert coverage["legacy_tau_apply_app_tx"]["command_kind"] == (
        "legacy/tau-application-multiplex/v1"
    )
    assert coverage["legacy_tau_apply_app_tx"]["lane_ids"] == [
        "ASSET_TRANSFER",
        "SPOT_LIQUIDITY",
        "ZDEX_TOKENOMICS",
        "ZUSD_MONETARY",
        "PERPS_MARKET",
        "ORACLE_MARKET",
        "PROOF_REWARDS",
    ]
    assert set(coverage["legacy_tau_apply_app_tx"]["bindings"]) == set(
        REQUIRED_COVERAGE_BINDINGS
    )
    assert coverage["legacy_tau_apply_app_tx"]["bindings"]["route"] == {
        "reference": None,
        "status": "GAP",
    }
    assert coverage["legacy_tau_apply_app_tx"]["bindings"]["adapter"] == {
        "reference": "src/integration/tau_testnet_dex_plugin.py::apply_app_tx",
        "status": "LEGACY_ONLY",
    }
    assert coverage["separate_global_economic_durable_publisher"][
        "bindings"
    ]["route"] == {"reference": None, "status": "GAP"}


def test_inventory_lane_registry_matches_global_settlement_abi_v1() -> None:
    assert M6_LANE_IDS == tuple(lane.value for lane in LaneIdV1)


def test_release_readiness_mode_fails_closed_for_open_coverage(
    capsys: pytest.CaptureFixture[str],
) -> None:
    exit_code = main(["--root", str(ROOT), "--json", "--require-release-ready"])
    report = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert report["ok"] is True
    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert report["required_assurance_statuses"] == list(REQUIRED_ASSURANCE_STATUSES)


def test_gap_derivation_does_not_block_a_complete_future_schema_row() -> None:
    row = CommandCoverageV1(
        coverage_id="future-release-backed-row",
        entrypoint_id="future-writer",
        command_kind="future/command/v1",
        lane_ids=("ASSET_TRANSFER",),
        workflow_ids=("WF-01",),
        bindings=tuple(
            (name, CoverageBindingV1("release://exact", "RELEASE_BACKED"))
            for name in REQUIRED_COVERAGE_BINDINGS
        ),
        assurance_statuses=REQUIRED_ASSURANCE_STATUSES,
        release_status="RELEASE_BACKED",
    )

    assert _release_gap(row) is None


def test_inventory_rejects_missing_command_coverage_row(tmp_path: Path) -> None:
    inventory = load_writer_inventory_manifest(ROOT / "tools/m6_writer_inventory_manifest_v1.json")
    payload = json.loads(
        (ROOT / "tools/m6_writer_inventory_manifest_v1.json").read_text(encoding="utf-8")
    )
    payload["coverage_contract"]["rows"] = [
        row
        for row in payload["coverage_contract"]["rows"]
        if row["entrypoint_id"] != inventory.entries[0].entrypoint_id
    ]
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="writer lacks command coverage"):
        load_writer_inventory_manifest(path)


def test_inventory_rejects_surplus_binding_dimension(tmp_path: Path) -> None:
    payload = json.loads(
        (ROOT / "tools/m6_writer_inventory_manifest_v1.json").read_text(encoding="utf-8")
    )
    payload["coverage_contract"]["rows"][0]["bindings"]["opaque_extension"] = {
        "reference": "research://unauthorized",
        "status": "RESEARCH_ONLY",
    }
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="binding keys mismatch"):
        load_writer_inventory_manifest(path)


def test_research_schema_rejects_metadata_only_release_promotion(tmp_path: Path) -> None:
    payload = json.loads(
        (ROOT / "tools/m6_writer_inventory_manifest_v1.json").read_text(encoding="utf-8")
    )
    row = payload["coverage_contract"]["rows"][0]
    row["release_status"] = "RELEASE_BACKED"
    row["bindings"]["route"] = {
        "reference": "registry://self-declared-route",
        "status": "RELEASE_BACKED",
    }
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="release_status must remain OPEN"):
        load_writer_inventory_manifest(path)


def test_inventory_rejects_duplicate_json_keys(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_text(
        '{"schema":"zenodex/m6-writer-inventory/v1","schema":"duplicate"}',
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="duplicate JSON key: schema"):
        load_writer_inventory_manifest(path)


def test_inventory_rejects_a_new_unregistered_apply_app_tx(tmp_path: Path) -> None:
    source = tmp_path / "src" / "rogue_writer.py"
    source.parent.mkdir(parents=True)
    source.write_text("def apply_app_tx():\n    return True\n", encoding="utf-8")

    findings = scan_unregistered_value_writers(tmp_path)

    assert [finding.rule_id for finding in findings] == ["unregistered_value_writer"]
    assert findings[0].evidence == "apply_app_tx"


def test_inventory_rejects_a_m6_port_without_the_commit_call(tmp_path: Path) -> None:
    source = tmp_path / "src" / "integration" / "m6_commit_port_v1.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "class M6CommitPortV1:\n"
        "    def publish(self):\n"
        "        return None\n",
        encoding="utf-8",
    )
    spec = WriterSpec(
        entrypoint_id="m6-test",
        path="src/integration/m6_commit_port_v1.py",
        symbol="publish",
        class_name="M6CommitPortV1",
        kind="m6_unique_commit_port",
        m6_mount_status="M6_RESEARCH_ONLY",
        commit_port_route="M6CommitPortV1._publish_proposal",
        requires_unique_commit_port=True,
        evidence_markers=("_publish_proposal",),
    )

    findings = scan_writer_spec(spec, root=tmp_path)

    assert [finding.rule_id for finding in findings] == ["writer_evidence_marker_missing"]
