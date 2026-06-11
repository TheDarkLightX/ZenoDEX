from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, cast

from src.integration.live_proof_wrapper import LIVE_PROOF_WRAPPER_STATUS_SCHEMA
from src.integration.production_promotion_evidence import (
    evaluate_production_zk_wrapping_evidence_v1,
)
from tests.test_check_zeno_ledger_risc0_real_proof_smoke_report import (
    _artifact_report as _spot_artifact_report,
)
from tools import build_zk_wrapping_evidence_from_risc0_bundle as builder
from tools.check_zeno_ledger_risc0_surface_bundle import BUNDLE_SCHEMA
from tools.check_zeno_ledger_scoped_risc0_smoke_report import (
    PERPS_PROOF_TYPE,
    PERPS_REQUIRED_TAMPERS,
    ZUSD_PROOF_TYPE,
    ZUSD_REQUIRED_TAMPERS,
)

NOW = 1747878000


def _hex(label: str) -> str:
    raw = label.encode("utf-8").hex()
    return (raw + "0" * 64)[:64]


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _zusd_report(tmp_path: Path) -> dict[str, object]:
    proof = tmp_path / "mint_zusd_risc0_proof.json"
    proof.write_text(json.dumps({"proof": "receipt"}), encoding="utf-8")
    return {
        "schema": "zenodex.zusd_risc0_real_proof_smoke_report.v1",
        "ok": True,
        "case_count": 1,
        "positive": 1,
        "negative": 0,
        "production_security_claim": False,
        "proof_type": ZUSD_PROOF_TYPE,
        "cases": [
            {
                "case": "mint",
                "kind": "positive",
                "ok": True,
                "proof_type": ZUSD_PROOF_TYPE,
                "risc0_image_id": _hex("zusd-image"),
                "proof_base64_len": 128,
                "proof_path": str(proof),
                "strict_verify": True,
                "tamper_rejections": sorted(ZUSD_REQUIRED_TAMPERS),
                "minted_zusd_e8": "100000000000",
                "collateral_value_e8": "200000000000",
                "mcr_bps": 11000,
            }
        ],
    }


def _perps_report(tmp_path: Path) -> dict[str, object]:
    proof = tmp_path / "four_wallet_perps_np_risc0_proof.json"
    proof.write_text(json.dumps({"proof": "receipt"}), encoding="utf-8")
    return {
        "schema": "zenodex.perps_np_risc0_real_proof_smoke.v1",
        "ok": True,
        "case_count": 1,
        "positive": 1,
        "negative": 0,
        "production_security_claim": False,
        "proof_surface": PERPS_PROOF_TYPE,
        "dynamic_membership_floor": 4,
        "cases": [
            {
                "case": "four_wallet",
                "kind": "positive",
                "ok": True,
                "proof_type": PERPS_PROOF_TYPE,
                "risc0_image_id": _hex("perps-image"),
                "proof_base64_len": 128,
                "proof_path": str(proof),
                "strict_verify": True,
                "tamper_rejections": sorted(PERPS_REQUIRED_TAMPERS),
                "current_surface_binding_check": True,
                "participant_count": 4,
                "intent_count": 4,
                "net_position_base": "0",
                "matched_base_volume": "5",
            }
        ],
    }


def _bundle_path(tmp_path: Path, *, broken: bool = False) -> Path:
    spot_path = tmp_path / "spot_report.json"
    zusd_path = tmp_path / "zusd_report.json"
    perps_path = tmp_path / "perps_report.json"
    _write_json(spot_path, _spot_artifact_report(tmp_path))
    _write_json(zusd_path, _zusd_report(tmp_path))
    perps = _perps_report(tmp_path)
    if broken:
        perps["cases"][0]["tamper_rejections"] = ["chain_id"]  # type: ignore[index]
    _write_json(perps_path, perps)
    bundle = {
        "schema": BUNDLE_SCHEMA,
        "surfaces": {
            "spot": {"report_path": str(spot_path), "required_cases": ["empty"]},
            "zusd": {"report_path": str(zusd_path), "required_cases": ["mint"]},
            "perps_np": {"report_path": str(perps_path), "required_cases": ["four_wallet"]},
        },
    }
    path = tmp_path / "risc0_bundle.json"
    _write_json(path, bundle)
    return path


def _live_status_for_evidence(evidence: dict[str, object]) -> dict[str, object]:
    verifier_binding = cast(Mapping[str, Any], evidence["verifier_binding"])
    sample = cast(Mapping[str, Any], evidence["sample_proof_acceptance"])
    verifier_hash = str(verifier_binding["verifier_cmd_hash"])
    return {
        "schema": LIVE_PROOF_WRAPPER_STATUS_SCHEMA,
        "surface": "risc0.zenodex_public_surfaces.v1",
        "required": True,
        "proof_provided": True,
        "verifier_configured": True,
        "zk_proof_verified": True,
        "proof_intent_receipt_hash": str(sample["proof_intent_receipt_hash"]),
        "verifier_request_hash": str(sample["verifier_request_hash"]),
        "artifact_binding_configured": True,
        "artifact_binding_complete": True,
        "artifact_binding": {"verifier_cmd_hash": "0x" + verifier_hash},
        "proof_verifier": {"kind": "subprocess", "cmd_hash": "0x" + verifier_hash},
        "error": None,
    }


def _base_builder_args(tmp_path: Path, out: Path, source_dir: Path) -> list[str]:
    return [
        "--risc0-surface-bundle",
        str(_bundle_path(tmp_path)),
        "--out",
        str(out),
        "--surface",
        "risc0.zenodex_public_surfaces.v1",
        "--verifier-cmd-json",
        json.dumps(["r0vm", "verify"]),
        "--audit-id",
        "audit-risc0-surfaces-1",
        "--audit-report-hash",
        "55" * 32,
        "--auditor",
        "auditor-a",
        "--audited-at",
        str(NOW - 3600),
        "--accepted-at",
        str(NOW - 60),
        "--issued-at",
        str(NOW),
        "--check-now",
        str(NOW),
        "--circuit-source",
        str(source_dir),
    ]


def test_zk_wrapping_builder_writes_lane_ready_evidence(capsys, tmp_path: Path) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"
    live_in = tmp_path / "captured_live_wrapper.json"
    live_copy = tmp_path / "live_wrapper_copy.json"

    candidate_code = builder.main([*_base_builder_args(tmp_path, out, source_dir), "--candidate-only"])
    assert candidate_code == 0
    capsys.readouterr()
    candidate = json.loads(out.read_text(encoding="utf-8"))
    _write_json(live_in, _live_status_for_evidence(candidate))

    code = builder.main(
        [
            *_base_builder_args(tmp_path, out, source_dir),
            "--live-wrapper-status",
            str(live_in),
            "--live-wrapper-out",
            str(live_copy),
            "--check",
        ]
    )

    assert code == 0
    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    live_status = json.loads(live_copy.read_text(encoding="utf-8"))
    assert live_status["artifact_binding"]["verifier_cmd_hash"].startswith("0x")
    lane = evaluate_production_zk_wrapping_evidence_v1(
        evidence,
        live_proof_wrapper_status=live_status,
        expected_surface="risc0.zenodex_public_surfaces.v1",
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []


def test_zk_wrapping_evaluator_rejects_unconfigured_live_artifact_binding(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    assert builder.main([*_base_builder_args(tmp_path, out, source_dir), "--candidate-only"]) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    live_status = _live_status_for_evidence(evidence)
    live_status["artifact_binding_configured"] = False

    lane = evaluate_production_zk_wrapping_evidence_v1(
        evidence,
        live_proof_wrapper_status=live_status,
        expected_surface="risc0.zenodex_public_surfaces.v1",
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "live proof wrapper must show artifact_binding_configured=true" in lane["gaps"]


def test_zk_wrapping_evaluator_rejects_live_wrapper_error(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    assert builder.main([*_base_builder_args(tmp_path, out, source_dir), "--candidate-only"]) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    live_status = _live_status_for_evidence(evidence)
    live_status["error"] = "post-submit binding failed"

    lane = evaluate_production_zk_wrapping_evidence_v1(
        evidence,
        live_proof_wrapper_status=live_status,
        expected_surface="risc0.zenodex_public_surfaces.v1",
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "live proof wrapper error must be null for production evidence" in lane["gaps"]


def test_zk_wrapping_builder_check_requires_external_live_wrapper_status(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    code = builder.main([*_base_builder_args(tmp_path, out, source_dir), "--check"])

    assert code == 2
    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "zk_wrapping_evidence_build_failed"
    assert "--live-wrapper-status" in payload["detail"]
    assert not out.exists()


def test_zk_wrapping_builder_requires_live_status_unless_candidate_only(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    code = builder.main(_base_builder_args(tmp_path, out, source_dir))

    assert code == 2
    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "zk_wrapping_evidence_build_failed"
    assert "--live-wrapper-status is required" in payload["detail"]
    assert not out.exists()


def test_zk_wrapping_builder_rejects_candidate_only_with_check(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    code = builder.main([*_base_builder_args(tmp_path, out, source_dir), "--candidate-only", "--check"])

    assert code == 2
    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "zk_wrapping_evidence_build_failed"
    assert "--candidate-only cannot be combined" in payload["detail"]
    assert not out.exists()


def test_zk_wrapping_builder_check_rejects_stale_issued_at(capsys, tmp_path: Path) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    stale_issued = NOW - 31 * 24 * 3600
    candidate_out = tmp_path / "candidate_zk_wrapping.json"
    checked_out = tmp_path / "checked_zk_wrapping.json"
    live_in = tmp_path / "captured_live_wrapper.json"
    args = _base_builder_args(tmp_path, candidate_out, source_dir)
    args[args.index("--issued-at") + 1] = str(stale_issued)
    args[args.index("--accepted-at") + 1] = str(stale_issued)
    args[args.index("--audited-at") + 1] = str(stale_issued - 3600)

    assert builder.main([*args, "--candidate-only"]) == 0
    capsys.readouterr()
    candidate = json.loads(candidate_out.read_text(encoding="utf-8"))
    _write_json(live_in, _live_status_for_evidence(candidate))
    args[args.index(str(candidate_out))] = str(checked_out)

    code = builder.main([*args, "--live-wrapper-status", str(live_in), "--check"])

    assert code == 1
    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("freshness" in gap for gap in err["gaps"])
    assert not checked_out.exists()


def test_zk_wrapping_builder_rejects_non_positive_sample_time_before_write(
    capsys,
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"
    args = _base_builder_args(tmp_path, out, source_dir)
    args[args.index("--accepted-at") + 1] = "0"

    code = builder.main([*args, "--candidate-only"])

    assert code == 2
    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "zk_wrapping_evidence_build_failed"
    assert "accepted_at must be a positive integer" in payload["detail"]
    assert not out.exists()


def test_zk_wrapping_builder_rejects_bad_risc0_bundle_before_write(capsys, tmp_path: Path) -> None:
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    (source_dir / "lib.rs").write_text("pub fn checked() {}\n", encoding="utf-8")
    out = tmp_path / "zk_wrapping.json"

    code = builder.main(
        [
            "--risc0-surface-bundle",
            str(_bundle_path(tmp_path, broken=True)),
            "--out",
            str(out),
            "--surface",
            "risc0.zenodex_public_surfaces.v1",
            "--verifier-cmd-json",
            json.dumps(["r0vm", "verify"]),
            "--audit-id",
            "audit-risc0-surfaces-1",
            "--audit-report-hash",
            "55" * 32,
            "--auditor",
            "auditor-a",
            "--audited-at",
            str(NOW - 3600),
            "--issued-at",
            str(NOW),
            "--circuit-source",
            str(source_dir),
            "--candidate-only",
        ]
    )

    assert code == 2
    out_json = json.loads(capsys.readouterr().out)
    assert out_json["error"] == "zk_wrapping_evidence_build_failed"
    assert "tamper_rejections missing" in out_json["detail"]
    assert not out.exists()
