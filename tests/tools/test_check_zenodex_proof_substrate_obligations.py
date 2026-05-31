from __future__ import annotations

import copy
import json

from tools.check_zenodex_proof_substrate_obligations import (
    DEFAULT_MANIFEST,
    main,
    validate_proof_substrate_obligations_v0,
)


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _proof_gap_obligation(manifest: dict[str, object], proof_gap_id: str) -> dict[str, object]:
    obligations = manifest["proof_gap_obligations"]
    assert isinstance(obligations, list)
    for obligation in obligations:
        assert isinstance(obligation, dict)
        if obligation.get("proof_gap_id") == proof_gap_id:
            return obligation
    raise AssertionError(f"missing proof gap obligation {proof_gap_id}")


def _unsupported_obligation(manifest: dict[str, object], unsupported_id: str) -> dict[str, object]:
    obligations = manifest["unsupported_proof_required_family_obligations"]
    assert isinstance(obligations, list)
    for obligation in obligations:
        assert isinstance(obligation, dict)
        if obligation.get("unsupported_family_id") == unsupported_id:
            return obligation
    raise AssertionError(f"missing unsupported-family obligation {unsupported_id}")


def _replace_proof_gap_obligation(
    manifest: dict[str, object],
    replacement: dict[str, object],
) -> None:
    obligations = list(manifest["proof_gap_obligations"])  # type: ignore[arg-type]
    index = next(
        i
        for i, item in enumerate(obligations)
        if item["proof_gap_id"] == replacement["proof_gap_id"]  # type: ignore[index]
    )
    obligations[index] = replacement
    manifest["proof_gap_obligations"] = obligations


def _replace_unsupported_obligation(
    manifest: dict[str, object],
    replacement: dict[str, object],
) -> None:
    obligations = list(manifest["unsupported_proof_required_family_obligations"])  # type: ignore[arg-type]
    index = next(
        i
        for i, item in enumerate(obligations)
        if item["unsupported_family_id"] == replacement["unsupported_family_id"]  # type: ignore[index]
    )
    obligations[index] = replacement
    manifest["unsupported_proof_required_family_obligations"] = obligations


def test_proof_substrate_obligations_accepts_default_manifest() -> None:
    report = validate_proof_substrate_obligations_v0(_manifest())

    assert report["ok"] is True
    assert report["proof_gap_obligation_count"] == 7
    assert report["unsupported_family_obligation_count"] == 5
    assert report["tau_guard_gap_count"] == 5
    assert report["tau_closed_real_proof_gap_count"] == 0
    assert report["missing_proof_gap_obligations"] == []
    assert report["missing_unsupported_family_obligations"] == []


def test_proof_substrate_obligations_rejects_missing_proof_gap_obligation() -> None:
    manifest = _manifest()
    obligations = list(manifest["proof_gap_obligations"])  # type: ignore[arg-type]
    manifest["proof_gap_obligations"] = [
        item
        for item in obligations
        if item["proof_gap_id"] != "perps_settlement_real_proof"  # type: ignore[index]
    ]

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert "perps_settlement_real_proof" in report["missing_proof_gap_obligations"]
    assert any("missing proof_gap_obligations" in err for err in report["errors"])


def test_proof_substrate_obligations_rejects_tau_execution_overclaim() -> None:
    manifest = _manifest()
    obligation = copy.deepcopy(_proof_gap_obligation(manifest, "zusd_lifecycle_real_proof"))
    obligation["tau_can_close_gap"] = True
    _replace_proof_gap_obligation(manifest, obligation)

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert any("tau_can_close_gap must be false" in err for err in report["errors"])


def test_proof_substrate_obligations_rejects_tau_as_value_moving_substrate() -> None:
    manifest = _manifest()
    obligation = copy.deepcopy(_proof_gap_obligation(manifest, "proof_market_reward_real_proof"))
    obligation["required_non_tau_substrate"] = "tau_guard"
    _replace_proof_gap_obligation(manifest, obligation)

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert any("value-moving real-proof gaps require zkvm_execution" in err for err in report["errors"])


def test_proof_substrate_obligations_rejects_missing_tau_evidence_path() -> None:
    manifest = _manifest()
    obligation = copy.deepcopy(_proof_gap_obligation(manifest, "oracle_critical_action_real_proof"))
    obligation["tau_evidence_paths"] = ["tests/tau/does_not_exist.py"]
    _replace_proof_gap_obligation(manifest, obligation)

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert any("tau_evidence_paths missing: tests/tau/does_not_exist.py" in err for err in report["errors"])


def test_proof_substrate_obligations_rejects_unsupported_family_tau_admission() -> None:
    manifest = _manifest()
    obligation = copy.deepcopy(_unsupported_obligation(manifest, "spot_v1_multi_hop_proof_rejected"))
    obligation["tau_can_admit_proof_required_profile"] = True
    _replace_unsupported_obligation(manifest, obligation)

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert any("tau_can_admit_proof_required_profile must be false" in err for err in report["errors"])


def test_proof_substrate_obligations_rejects_missing_spot_not_covered_family() -> None:
    manifest = _manifest()
    obligations = list(manifest["unsupported_proof_required_family_obligations"])  # type: ignore[arg-type]
    manifest["unsupported_proof_required_family_obligations"] = [
        item
        for item in obligations
        if item["unsupported_family_id"] != "spot_v1_native_asset_sync_proof_rejected"  # type: ignore[index]
    ]

    report = validate_proof_substrate_obligations_v0(manifest)

    assert report["ok"] is False
    assert "spot_v1_native_asset_sync_proof_rejected" in report["missing_unsupported_family_obligations"]
    assert any("spot not_covered_operations missing" in err for err in report["errors"])


def test_proof_substrate_obligations_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "proof_substrate_obligations.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--manifest", str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["schema"] == "zenodex.proof_substrate_obligations_report.v0"
    assert report["ok"] is True
