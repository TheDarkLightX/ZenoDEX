from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    attach_production_autotrader_hash_v1,
    evaluate_production_autotrader_evidence_v1,
    production_autotrader_run_approval_hash_v1,
    production_autotrader_run_approval_message_v1,
)
from tools import build_autotrader_evidence as builder

NOW = 1747878000
DURATION = 25 * 3600
STARTED = NOW - DURATION - 60
LAST_HEARTBEAT = STARTED + DURATION
SIGNER_PRIVATE_KEYS = (
    Ed25519PrivateKey.from_private_bytes(bytes([11]) * 32),
    Ed25519PrivateKey.from_private_bytes(bytes([21]) * 32),
)
SIGNER_PUBKEYS = tuple(
    key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()
    for key in SIGNER_PRIVATE_KEYS
)


def _sign_approval(index: int, approval_hash: str) -> str:
    return SIGNER_PRIVATE_KEYS[index].sign(
        production_autotrader_run_approval_message_v1(approval_hash)
    ).hex()


def _heartbeats() -> list[int]:
    values = list(range(STARTED, LAST_HEARTBEAT + 1, 5 * 60))
    if values[-1] != LAST_HEARTBEAT:
        values.append(LAST_HEARTBEAT)
    return values


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _crashes() -> list[dict[str, int | str]]:
    return [
        {
            "crash_at": STARTED + 3600,
            "recovery_at": STARTED + 3620,
            "checkpoint_hash": "aa" * 32,
        },
        {
            "crash_at": STARTED + 7200,
            "recovery_at": STARTED + 7250,
            "checkpoint_hash": "bb" * 32,
        },
    ]


def _budget() -> dict[str, int]:
    return {
        "max_actions_per_tick_observed": 3,
        "max_runs_per_process_observed": 100,
        "config_max_actions_per_tick": 4,
        "config_max_runs_per_process": 200,
    }


def _expected_approval_hash(*, chain_id: str = "tau-test-prod") -> str:
    return production_autotrader_run_approval_hash_v1(
        {
            "schema": "zenodex/production-autotrader-evidence/v1",
            "supervisor_id": "autotrader-prod-1",
            "chain_id": chain_id,
            "profile_supervisor_hash": "sup-hash",
            "run_window": {
                "started_at": STARTED,
                "last_heartbeat_at": LAST_HEARTBEAT,
                "duration_seconds": DURATION,
                "ticks_executed": 500,
                "ticks_failed": 3,
                "ticks_throttled": 20,
                "heartbeat_timestamps": _heartbeats(),
            },
            "crash_recovery": _crashes(),
            "budget_compliance": _budget(),
        }
    )


def _approval_file(tmp_path: Path, *, approval_hash: str | None = None) -> Path:
    run_approval_hash = _expected_approval_hash() if approval_hash is None else approval_hash
    path = tmp_path / "approvals.json"
    _write_json(
        path,
        [
            {
                "signer_pubkey": SIGNER_PUBKEYS[0],
                "approval_hash": run_approval_hash,
                "signature": _sign_approval(0, run_approval_hash),
            },
            {
                "signer_pubkey": SIGNER_PUBKEYS[1],
                "approval_hash": run_approval_hash,
                "signature": _sign_approval(1, run_approval_hash),
            },
        ],
    )
    return path


def _expected_approvers_file(tmp_path: Path, *, pubkeys: tuple[str, ...] = SIGNER_PUBKEYS) -> Path:
    path = tmp_path / "expected-approvers.json"
    _write_json(path, list(pubkeys))
    return path


def _crash_file(tmp_path: Path) -> Path:
    path = tmp_path / "crashes.json"
    _write_json(
        path,
        _crashes(),
    )
    return path


def _base_args(
    tmp_path: Path,
    out: Path,
    *,
    heartbeat_values: list[int] | None = None,
) -> list[str]:
    return [
        "--out",
        str(out),
        "--supervisor-id",
        "autotrader-prod-1",
        "--chain-id",
        "tau-test-prod",
        "--profile-supervisor-hash",
        "sup-hash",
        "--started-at",
        str(STARTED),
        "--last-heartbeat-at",
        str(LAST_HEARTBEAT),
        "--duration-seconds",
        str(DURATION),
        "--ticks-executed",
        "500",
        "--ticks-failed",
        "3",
        "--ticks-throttled",
        "20",
        "--heartbeat-timestamps-json",
        json.dumps(_heartbeats() if heartbeat_values is None else heartbeat_values),
        "--crash-recovery-file",
        str(_crash_file(tmp_path)),
        "--multi-signer-approvals-file",
        str(_approval_file(tmp_path)),
        "--expected-approval-signer-pubkeys-file",
        str(_expected_approvers_file(tmp_path)),
        "--max-actions-per-tick-observed",
        "3",
        "--max-runs-per-process-observed",
        "100",
        "--config-max-actions-per-tick",
        "4",
        "--config-max-runs-per-process",
        "200",
        "--issued-at",
        str(NOW),
        "--check-now",
        str(NOW),
        "--expected-chain-id",
        "tau-test-prod",
    ]


def test_autotrader_builder_writes_lane_ready_evidence(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"

    assert builder.main([*_base_args(tmp_path, out), "--check"]) == 0

    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    lane = evaluate_production_autotrader_evidence_v1(
        evidence,
        supervisor_profile_hash="sup-hash",
        config_max_actions_per_tick=4,
        config_max_runs_per_process=200,
        expected_chain_id="tau-test-prod",
        expected_approval_signer_pubkeys=list(SIGNER_PUBKEYS),
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []
    assert lane["distinct_signer_count"] == 2
    assert len(evidence["evidence_hash"]) == 64


def test_autotrader_builder_check_rejects_template_chain_id_before_write(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("tau-test-prod")] = "EXPECTED_CHAIN_ID"
    args[args.index("tau-test-prod")] = "EXPECTED_CHAIN_ID"
    approvals = _approval_file(
        tmp_path,
        approval_hash=_expected_approval_hash(chain_id="EXPECTED_CHAIN_ID"),
    )
    args[args.index("--multi-signer-approvals-file") + 1] = str(approvals)

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("placeholder value 'EXPECTED_CHAIN_ID'" in gap for gap in err["gaps"])
    assert not out.exists()


def test_autotrader_builder_check_rejects_heartbeat_gap(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    heartbeats = _heartbeats()
    heartbeats[1] = heartbeats[0] + 301

    assert builder.main(_base_args(tmp_path, out, heartbeat_values=heartbeats)) == 2

    err = json.loads(capsys.readouterr().out)
    assert err["error"] == "autotrader_evidence_build_failed"
    assert "max gap" in err["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_malformed_heartbeats(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--heartbeat-timestamps-json") + 1] = json.dumps([STARTED, "bad"])

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "heartbeat timestamps[1]" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_duration_mismatch_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--duration-seconds") + 1] = str(DURATION + 1)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "duration_seconds must equal" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_budget_overrun_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--max-actions-per-tick-observed") + 1] = "5"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "observed actions_per_tick exceeds" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_missing_expected_chain_id_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    index = args.index("--expected-chain-id")
    del args[index : index + 2]

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "expected chain_id is required for autotrader binding" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_expected_chain_id_mismatch_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--expected-chain-id") + 1] = "wrong-chain"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "chain_id does not match expected_chain_id" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_duplicate_signer_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    approvals = tmp_path / "approvals-duplicate.json"
    approval_hash = _expected_approval_hash()
    _write_json(
        approvals,
        [
            {
                "signer_pubkey": SIGNER_PUBKEYS[0],
                "approval_hash": approval_hash,
                "signature": _sign_approval(0, approval_hash),
            },
            {
                "signer_pubkey": SIGNER_PUBKEYS[0],
                "approval_hash": approval_hash,
                "signature": _sign_approval(0, approval_hash),
            },
        ],
    )
    args = _base_args(tmp_path, out)
    args[args.index("--multi-signer-approvals-file") + 1] = str(approvals)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "duplicates an earlier approval" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_unapproved_signer_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    expected = tmp_path / "expected-other-approvers.json"
    _write_json(expected, ["ab" * 32, "cd" * 32])
    args = _base_args(tmp_path, out)
    args[args.index("--expected-approval-signer-pubkeys-file") + 1] = str(expected)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "not in expected approver set" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_approval_hash_for_different_run(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    approvals = Path(args[args.index("--multi-signer-approvals-file") + 1])
    _write_json(
        approvals,
        [
            {
                "signer_pubkey": SIGNER_PUBKEYS[0],
                "approval_hash": "ff" * 32,
                "signature": _sign_approval(0, "ff" * 32),
            },
            {
                "signer_pubkey": SIGNER_PUBKEYS[1],
                "approval_hash": "ff" * 32,
                "signature": _sign_approval(1, "ff" * 32),
            },
        ],
    )
    args[args.index("--multi-signer-approvals-file") + 1] = str(approvals)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "canonical run approval hash" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_rejects_fake_approval_signature_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    approvals = Path(args[args.index("--multi-signer-approvals-file") + 1])
    data = json.loads(approvals.read_text(encoding="utf-8"))
    data[0]["signature"] = "13" * 64
    _write_json(approvals, data)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "multi-signer approvals[0].signature is invalid" in payload["detail"]
    assert not out.exists()


def test_autotrader_evaluator_rejects_approval_hash_for_mutated_run_report(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    assert builder.main(_base_args(tmp_path, out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["run_window"]["ticks_executed"] = int(evidence["run_window"]["ticks_executed"]) + 1
    evidence = attach_production_autotrader_hash_v1(evidence)

    lane = evaluate_production_autotrader_evidence_v1(
        evidence,
        supervisor_profile_hash="sup-hash",
        config_max_actions_per_tick=4,
        config_max_runs_per_process=200,
        expected_chain_id="tau-test-prod",
        expected_approval_signer_pubkeys=list(SIGNER_PUBKEYS),
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "multi_signer_approvals approval_hash must equal canonical run approval hash" in lane["gaps"]


def test_autotrader_evaluator_rejects_rehashed_fake_approval_signature(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    assert builder.main(_base_args(tmp_path, out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["multi_signer_approvals"][0]["signature"] = "13" * 64
    evidence = attach_production_autotrader_hash_v1(evidence)

    lane = evaluate_production_autotrader_evidence_v1(
        evidence,
        supervisor_profile_hash="sup-hash",
        config_max_actions_per_tick=4,
        config_max_runs_per_process=200,
        expected_chain_id="tau-test-prod",
        expected_approval_signer_pubkeys=list(SIGNER_PUBKEYS),
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "multi_signer_approvals[0].signature is invalid" in lane["gaps"]


def test_autotrader_evaluator_requires_external_binding_config(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    assert builder.main(_base_args(tmp_path, out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))

    lane = evaluate_production_autotrader_evidence_v1(
        evidence,
        supervisor_profile_hash="sup-hash",
        config_max_actions_per_tick=None,
        config_max_runs_per_process=None,
        expected_chain_id=None,
        expected_approval_signer_pubkeys=None,
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "expected chain_id is required for autotrader binding" in lane["gaps"]
    assert "config_max_actions_per_tick is required for autotrader binding" in lane["gaps"]
    assert "config_max_runs_per_process is required for autotrader binding" in lane["gaps"]
    assert "expected autotrader approval signer pubkeys are required for binding" in lane["gaps"]


def test_autotrader_builder_rejects_overlapping_crash_recovery_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    crashes = tmp_path / "crashes-overlap.json"
    _write_json(
        crashes,
        [
            {"crash_at": STARTED + 3600, "recovery_at": STARTED + 3700, "checkpoint_hash": "aa" * 32},
            {"crash_at": STARTED + 3650, "recovery_at": STARTED + 3750, "checkpoint_hash": "bb" * 32},
        ],
    )
    args = _base_args(tmp_path, out)
    args[args.index("--crash-recovery-file") + 1] = str(crashes)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "overlaps" in payload["detail"]
    assert not out.exists()


def test_autotrader_builder_check_rejects_stale_issued_at(capsys, tmp_path: Path) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--issued-at") + 1] = str(NOW - 31 * 24 * 3600)

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("freshness" in gap for gap in err["gaps"])
    assert not out.exists()


def test_autotrader_evaluator_rejects_rehashed_stale_run_window(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"

    assert builder.main(_base_args(tmp_path, out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    stale_last_heartbeat = NOW - 7 * 24 * 3600
    shift = stale_last_heartbeat - int(evidence["run_window"]["last_heartbeat_at"])
    for key in ("started_at", "last_heartbeat_at"):
        evidence["run_window"][key] = int(evidence["run_window"][key]) + shift
    evidence["run_window"]["heartbeat_timestamps"] = [
        int(value) + shift for value in evidence["run_window"]["heartbeat_timestamps"]
    ]
    for entry in evidence["crash_recovery"]:
        entry["crash_at"] = int(entry["crash_at"]) + shift
        entry["recovery_at"] = int(entry["recovery_at"]) + shift
    tampered = attach_production_autotrader_hash_v1(evidence)

    lane = evaluate_production_autotrader_evidence_v1(
        tampered,
        supervisor_profile_hash="sup-hash",
        config_max_actions_per_tick=4,
        config_max_runs_per_process=200,
        expected_chain_id="tau-test-prod",
        expected_approval_signer_pubkeys=list(SIGNER_PUBKEYS),
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "run_window.last_heartbeat_at is too old for evidence issued_at" in lane["gaps"]


def test_autotrader_builder_rejects_non_positive_issued_at_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "autotrader.json"
    args = _base_args(tmp_path, out)
    args[args.index("--issued-at") + 1] = "0"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "autotrader_evidence_build_failed"
    assert "issued_at must be a positive integer" in payload["detail"]
    assert not out.exists()
