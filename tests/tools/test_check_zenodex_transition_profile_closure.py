from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_zenodex_transition_profile_closure import (
    DEFAULT_MANIFEST,
    main,
    validate_transition_profile_closure_v0,
)


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _group(manifest: dict[str, object], group_id: str) -> dict[str, object]:
    groups = manifest["admitted_transition_families"]
    assert isinstance(groups, list)
    for group in groups:
        assert isinstance(group, dict)
        if group.get("id") == group_id:
            return group
    raise AssertionError(f"missing group {group_id}")


def _unsupported(manifest: dict[str, object], entry_id: str) -> dict[str, object]:
    entries = manifest["unsupported_proof_required_families"]
    assert isinstance(entries, list)
    for entry in entries:
        assert isinstance(entry, dict)
        if entry.get("id") == entry_id:
            return entry
    raise AssertionError(f"missing unsupported entry {entry_id}")


def test_transition_profile_closure_accepts_default_manifest() -> None:
    report = validate_transition_profile_closure_v0(_manifest())

    assert report["ok"] is True
    assert report["admitted_group_count"] == 7
    assert report["transition_surface_count"] == 7
    assert report["mapped_transition_surface_count"] == 7
    assert report["unsupported_proof_required_count"] == 5
    assert report["value_moving_family_count"] >= 20


def test_transition_profile_closure_rejects_missing_required_family() -> None:
    manifest = _manifest()
    group = copy.deepcopy(_group(manifest, "zusd_lifecycle_full_node_replay_v1"))
    group["families"] = [family for family in group["families"] if family != "zusd_liquidation"]  # type: ignore[index]
    group["value_moving_families"] = [
        family for family in group["value_moving_families"] if family != "zusd_liquidation"  # type: ignore[index]
    ]
    groups = list(manifest["admitted_transition_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(groups) if item["id"] == group["id"])  # type: ignore[index]
    groups[index] = group
    manifest["admitted_transition_families"] = groups

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("zusd_lifecycle_microgate_surface missing required families: zusd_liquidation" in err for err in report["errors"])


def test_transition_profile_closure_rejects_metadata_only_admission() -> None:
    manifest = _manifest()
    group = copy.deepcopy(_group(manifest, "spot_intent_full_node_replay_v1"))
    group["public_data_availability"] = "metadata_only_non_transition"
    groups = list(manifest["admitted_transition_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(groups) if item["id"] == group["id"])  # type: ignore[index]
    groups[index] = group
    manifest["admitted_transition_families"] = groups

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("deterministic_replay requires public_inputs_and_replay_artifacts" in err for err in report["errors"])


def test_transition_profile_closure_rejects_uncovered_spot_zk_family() -> None:
    manifest = _manifest()
    group = copy.deepcopy(_group(manifest, "spot_v1_risc0_supported_transition_proof_v1"))
    group["families"] = list(group["families"]) + ["swap_exact_out"]  # type: ignore[arg-type]
    group["value_moving_families"] = list(group["value_moving_families"]) + ["swap_exact_out"]  # type: ignore[arg-type]
    groups = list(manifest["admitted_transition_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(groups) if item["id"] == group["id"])  # type: ignore[index]
    groups[index] = group
    manifest["admitted_transition_families"] = groups

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("spot v1 zk families not covered by host Risc0 operations: swap_exact_out" in err for err in report["errors"])
    assert any("spot v1 zk families conflict with not_covered_operations: swap_exact_out" in err for err in report["errors"])


def test_transition_profile_closure_rejects_missing_unsupported_proof_required_entry() -> None:
    manifest = _manifest()
    entries = list(manifest["unsupported_proof_required_families"])  # type: ignore[arg-type]
    manifest["unsupported_proof_required_families"] = [
        entry for entry in entries if entry["id"] != "spot_v1_swap_exact_out_proof_rejected"  # type: ignore[index]
    ]

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert "missing unsupported proof-required entry: spot_v1_single_pool_success:swap_exact_out" in report["errors"]


def test_transition_profile_closure_rejects_missing_governed_profile_id() -> None:
    manifest = _manifest()
    group = copy.deepcopy(_group(manifest, "perps_bounded_full_node_replay_v1"))
    group["governed_profile_id"] = ""
    groups = list(manifest["admitted_transition_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(groups) if item["id"] == group["id"])  # type: ignore[index]
    groups[index] = group
    manifest["admitted_transition_families"] = groups

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("governed_profile_id must be a non-empty string" in err for err in report["errors"])


def test_transition_profile_closure_rejects_non_transition_surface_admission() -> None:
    manifest = _manifest()
    group = copy.deepcopy(_group(manifest, "proof_mining_reward_full_node_replay_v1"))
    group["surface_id"] = "proof_required_profile_metadata_and_report_replay"
    groups = list(manifest["admitted_transition_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(groups) if item["id"] == group["id"])  # type: ignore[index]
    groups[index] = group
    manifest["admitted_transition_families"] = groups

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("admitted family must reference a transition-coverage host surface" in err for err in report["errors"])


def test_transition_profile_closure_rejects_weak_proof_required_behavior() -> None:
    manifest = _manifest()
    behavior = copy.deepcopy(manifest["proof_required_behavior"])
    assert isinstance(behavior, dict)
    behavior["rejects_unsupported_transition_family"] = False
    manifest["proof_required_behavior"] = behavior

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert "proof_required_behavior.rejects_unsupported_transition_family must be true" in report["errors"]


def test_transition_profile_closure_rejects_missing_fail_closed_check() -> None:
    manifest = _manifest()
    entry = copy.deepcopy(_unsupported(manifest, "spot_v1_native_asset_sync_proof_rejected"))
    entry["fail_closed_checks"] = ["reject_missing_proof", "reject_wrong_profile_id"]
    entries = list(manifest["unsupported_proof_required_families"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(entries) if item["id"] == entry["id"])  # type: ignore[index]
    entries[index] = entry
    manifest["unsupported_proof_required_families"] = entries

    report = validate_transition_profile_closure_v0(manifest)

    assert report["ok"] is False
    assert any("fail_closed_checks missing: reject_unsupported_transition_family" in err for err in report["errors"])


def test_transition_profile_closure_cli_outputs_report(tmp_path: Path, capsys) -> None:
    manifest_path = tmp_path / "transition_profile_closure.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--manifest", str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.transition_profile_closure_report.v0"
