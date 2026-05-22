from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "zenograph_fact_pack_build.py"
VERIFY_CLI = REPO_ROOT / "tools" / "zenograph_fact_pack_verify.py"


def _write_fact_pack_inputs(tmp_path: Path) -> tuple[Path, Path]:
    fact_path = tmp_path / "fact.json"
    review_path = tmp_path / "review.json"
    fact_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-fact-record/v1",
                "fact_id": "protocol.governance_attack_risk",
                "subject_id": "protocol",
                "predicate": "governance_attack_risk",
                "value": "elevated",
                "source_id": "feed.news.alpha",
                "microtheory": "RiskPolicy",
                "observed_at": "2026-03-26T00:00:00Z",
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    review_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/krr-review-record/v1",
                "review_id": "zenograph.pack.review.runtime",
                "target_kind": "bundle",
                "target_id": "zenograph.pack.test",
                "decision": "approve",
                "reviewer": "security.review",
                "reviewed_at": "2026-03-26T00:10:00Z",
                "rationale": "runtime fact pack approved",
                "approved_for_runtime": True,
                "provenance_ok": True,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    return fact_path, review_path


def test_zenograph_fact_pack_build_and_verify_cli_roundtrip(tmp_path: Path) -> None:
    fact_path, review_path = _write_fact_pack_inputs(tmp_path)
    pack_path = tmp_path / "fact_pack.json"

    build_proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--pack-name",
            "zenograph.pack.test",
            "--fact-file",
            str(fact_path),
            "--review-record-file",
            str(review_path),
            "--signer-privkey",
            "21",
            "--pack-out",
            str(pack_path),
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
    assert build_report["pack"]["schema"] == "zenodex/zenograph-fact-pack/v1"
    assert build_report["pack"]["signer_pubkey"].startswith("0x")

    verify_proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--pack-file",
            str(pack_path),
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
    assert verify_report["runtime_fact_count"] == 1
    assert verify_report["subject_predicates"] == ["protocol.governance_attack_risk"]
