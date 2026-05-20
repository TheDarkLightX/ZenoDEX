from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "autotrader_krr_bundle_build.py"
VERIFY_CLI = REPO_ROOT / "tools" / "autotrader_krr_bundle_verify.py"


def _write_minimal_bundle_inputs(tmp_path: Path) -> tuple[Path, Path, Path]:
    krr_kb_path = tmp_path / "krr_kb.json"
    history_path = tmp_path / "history.json"
    review_path = tmp_path / "bundle_review.json"
    krr_kb_path.write_text(
        json.dumps(
            {
                "operator_priors": {},
                "semantic_rules": [],
                "check_priors": {"policy::budget_guard": {"base_weight": 1.25}},
                "check_family_priors": {},
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    history_path.write_text(
        json.dumps(
            {"history_source_stats": {"feed.news.alpha": {"submit": 5, "reject": 1, "skip": 2}}},
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    review_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/krr-review-record/v1",
                "review_id": "bundle.review.runtime",
                "target_kind": "bundle",
                "target_id": "bundle.test.cli",
                "decision": "approve",
                "reviewer": "security.review",
                "reviewed_at": "2026-03-12T00:10:00Z",
                "rationale": "runtime bundle approved",
                "approved_for_runtime": True,
                "provenance_ok": True,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    return krr_kb_path, history_path, review_path


def test_autotrader_krr_bundle_build_and_verify_cli_roundtrip(tmp_path: Path) -> None:
    krr_kb_path, history_path, review_path = _write_minimal_bundle_inputs(tmp_path)
    bundle_path = tmp_path / "bundle.json"

    build_proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--bundle-name",
            "bundle.test.cli",
            "--krr-kb",
            str(krr_kb_path),
            "--history-file",
            str(history_path),
            "--review-record-file",
            str(review_path),
            "--signer-privkey",
            "21",
            "--bundle-out",
            str(bundle_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert build_proc.returncode == 0, build_proc.stderr
    build_report = json.loads(build_proc.stdout)
    assert build_report["ok"] is True
    assert build_report["bundle"]["schema"] == "zenodex/autotrader-krr-bundle/v1"
    assert build_report["bundle"]["signer_pubkey"].startswith("0x")

    verify_proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--bundle-file",
            str(bundle_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert verify_proc.returncode == 0, verify_proc.stderr
    verify_report = json.loads(verify_proc.stdout)
    assert verify_report["ok"] is True
    assert verify_report["review_gate_ok"] is True
    assert verify_report["runtime_artifacts"]["krr_kb_present"] is True
    assert verify_report["runtime_artifacts"]["history_present"] is True


def test_autotrader_krr_bundle_verify_cli_rejects_tampered_bundle_hash(tmp_path: Path) -> None:
    krr_kb_path, history_path, review_path = _write_minimal_bundle_inputs(tmp_path)
    bundle_path = tmp_path / "bundle.json"

    build_proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--bundle-name",
            "bundle.test.cli",
            "--krr-kb",
            str(krr_kb_path),
            "--history-file",
            str(history_path),
            "--review-record-file",
            str(review_path),
            "--signer-privkey",
            "21",
            "--bundle-out",
            str(bundle_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_proc.returncode == 0, build_proc.stderr

    tampered = json.loads(bundle_path.read_text(encoding="utf-8"))
    tampered["bundle_hash"] = "0x" + ("0" * 63) + "1"
    tampered_path = tmp_path / "bundle.tampered.json"
    tampered_path.write_text(json.dumps(tampered, indent=2, sort_keys=True), encoding="utf-8")

    verify_proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--bundle-file",
            str(tampered_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert verify_proc.returncode == 1
    verify_report = json.loads(verify_proc.stderr)
    assert verify_report["ok"] is False
    assert "bundle hash mismatch" in verify_report["error"]
