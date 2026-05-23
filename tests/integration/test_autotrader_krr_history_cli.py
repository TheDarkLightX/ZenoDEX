from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_krr_history.py"


def test_autotrader_krr_history_cli_merges_reports_and_history(tmp_path: Path) -> None:
    compile_report = tmp_path / "compile.json"
    compile_report.write_text(
        json.dumps(
            {
                "schema": "zenodex/autotrader-policy-compile/v1",
                "ok": True,
                "krr_advice": {
                    "phase": "compile",
                    "candidate_checks": ["policy::compile_guard", "policy::template_bounds"],
                    "preferred_checks": ["policy::compile_guard"],
                },
            }
        ),
        encoding="utf-8",
    )
    live_report = tmp_path / "live.json"
    live_report.write_text(
        json.dumps(
            {
                "schema": "zenodex/autotrader-live-report/v1",
                "mode": "live_prepare",
                "decision": {
                    "tag": "reject",
                    "reason": "signer_pubkey_mismatch",
                    "tau_policy_receipt": None,
                },
                "krr_advice": {
                    "phase": "live",
                    "candidate_checks": ["live::signer_match", "live::nonce_guard"],
                    "preferred_checks": ["live::signer_match"],
                },
            }
        ),
        encoding="utf-8",
    )
    history_in = tmp_path / "history_in.json"
    history_in.write_text(
        json.dumps(
            {
                "schema": "zenodex/autotrader-krr-history/v1",
                "history_check_stats": {
                    "policy::compile_guard": {"total": 1, "supported": 1, "support_rate": 1.0}
                },
            }
        ),
        encoding="utf-8",
    )
    history_out = tmp_path / "history_out.json"

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--report-glob",
            str(tmp_path / "*.json"),
            "--history-in",
            str(history_in),
            "--history-out",
            str(history_out),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["report_count"] == 2
    assert report["history_check_stats"]["policy::compile_guard"] == {
        "total": 2,
        "supported": 2,
        "support_rate": 1.0,
    }
    assert report["history_check_stats"]["live::signer_match"] == {
        "total": 1,
        "supported": 1,
        "support_rate": 1.0,
    }
    persisted = json.loads(history_out.read_text(encoding="utf-8"))
    assert sorted(persisted["source_reports"]) == sorted([str(compile_report), str(live_report)])


def test_autotrader_krr_history_cli_requires_reports(tmp_path: Path) -> None:
    proc = subprocess.run(
        [sys.executable, str(CLI_PATH)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "at least one report file" in report["error"]
