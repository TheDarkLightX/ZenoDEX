from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def _h(tag: str) -> str:
    return "sha256:" + tag.encode("utf-8").hex().ljust(64, "0")[:64]


def _trace(events: list[dict], **overrides: object) -> dict:
    obj = {
        "schema": "zenodex.oracle.reporter_lifecycle.v1",
        "reporter_id": "reporter.sample",
        "reporter_pubkey": "0x" + ("11" * 48),
        "required_bond": 100,
        "events": events,
    }
    obj.update(overrides)
    return obj


def _sample_events() -> list[dict]:
    report_id = _h("report")
    dispute_id = _h("dispute")
    return [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 100},
        {
            "type": "submit_report",
            "epoch": 3,
            "report_id": report_id,
            "query_id": _h("query"),
            "value_hash": _h("value"),
        },
        {
            "type": "open_dispute",
            "epoch": 4,
            "report_id": report_id,
            "dispute_id": dispute_id,
            "dispute_bond": 20,
        },
        {"type": "slash", "epoch": 5, "dispute_id": dispute_id, "amount": 10},
        {"type": "resolve_dispute", "epoch": 6, "dispute_id": dispute_id, "outcome": "upheld"},
        {"type": "unregister", "epoch": 7},
        {"type": "withdraw_bond", "epoch": 8, "amount": 90},
    ]


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "lifecycle.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_lifecycle.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_reporter_lifecycle_accepts_sample_trace(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _trace(_sample_events()))
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["active"] is False
    assert result["bond_available"] == 0
    assert result["reports_submitted"] == 1
    assert result["disputes_open"] == 0
    assert result["disputes_resolved"] == 1
    assert result["total_slashed"] == 10
    assert result["total_withdrawn"] == 90
    assert result["last_epoch"] == 8
    assert result["errors"] == []


def test_reporter_lifecycle_rejects_report_before_register(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _trace(
            [
                {
                    "type": "submit_report",
                    "epoch": 1,
                    "report_id": _h("report"),
                    "query_id": _h("query"),
                    "value_hash": _h("value"),
                }
            ]
        ),
    )
    assert code == 2
    assert "report_submitted_by_inactive_reporter" in result["errors"]
    assert "report_submitted_under_required_bond" in result["errors"]


def test_reporter_lifecycle_rejects_underbonded_report(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 99},
        {
            "type": "submit_report",
            "epoch": 3,
            "report_id": _h("report"),
            "query_id": _h("query"),
            "value_hash": _h("value"),
        },
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "report_submitted_under_required_bond" in result["errors"]


def test_reporter_lifecycle_rejects_dispute_for_unknown_report(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 100},
        {
            "type": "open_dispute",
            "epoch": 3,
            "report_id": _h("missing-report"),
            "dispute_id": _h("dispute"),
            "dispute_bond": 20,
        },
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "dispute_for_unknown_report" in result["errors"]


def test_reporter_lifecycle_rejects_slash_without_open_dispute(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 100},
        {"type": "slash", "epoch": 3, "dispute_id": _h("missing-dispute"), "amount": 10},
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "slash_without_open_dispute" in result["errors"]


def test_reporter_lifecycle_rejects_unregister_with_open_dispute(tmp_path: Path) -> None:
    events = _sample_events()[:4] + [{"type": "unregister", "epoch": 5}]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "unregister_with_open_dispute" in result["errors"]


def test_reporter_lifecycle_rejects_withdraw_while_active(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 100},
        {"type": "withdraw_bond", "epoch": 3, "amount": 1},
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "withdraw_while_reporter_active" in result["errors"]


def test_reporter_lifecycle_rejects_withdraw_over_bond(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 1},
        {"type": "deposit_bond", "epoch": 2, "amount": 100},
        {"type": "unregister", "epoch": 3},
        {"type": "withdraw_bond", "epoch": 4, "amount": 101},
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "withdraw_exceeds_bond" in result["errors"]


def test_reporter_lifecycle_rejects_epoch_regression(tmp_path: Path) -> None:
    events = [
        {"type": "register", "epoch": 2},
        {"type": "deposit_bond", "epoch": 1, "amount": 100},
    ]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "event_epoch_regression:1" in result["errors"]


def test_reporter_lifecycle_rejects_unknown_event_field(tmp_path: Path) -> None:
    events = [{"type": "register", "epoch": 1, "admin_override": True}]
    code, result = _run_verify(tmp_path, _trace(events))
    assert code == 2
    assert "unknown_event_register_field:admin_override" in result["errors"]


def test_reporter_lifecycle_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-lifecycle.json"
    path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_lifecycle.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("lifecycle_load_failed:lifecycle_file_too_large:") for error in result["errors"])


def test_reporter_lifecycle_sample_cli_emits_verifiable_trace(tmp_path: Path) -> None:
    path = tmp_path / "sample-lifecycle.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_lifecycle.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_lifecycle.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["total_slashed"] == 10
