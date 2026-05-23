from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.agents.zenograph_schema import ZGFact, ZGFactStatus, ZGSourceKind
from src.agents.zenograph_store import ZenoGraphStore

REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_FROM_STORE_CLI = REPO_ROOT / "tools" / "zenograph_fact_pack_from_store.py"
VERIFY_CLI = REPO_ROOT / "tools" / "zenograph_fact_pack_verify.py"


def _write_review(tmp_path: Path, *, pack_name: str) -> Path:
    review_path = tmp_path / "review.json"
    review_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/krr-review-record/v1",
                "review_id": f"{pack_name}.review.runtime",
                "target_kind": "bundle",
                "target_id": pack_name,
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
    return review_path


def test_zenograph_fact_pack_from_store_cli_exports_only_accepted_facts(tmp_path: Path) -> None:
    store_root = tmp_path / "zenograph_store"
    store = ZenoGraphStore(store_root)
    store.append_fact(
        ZGFact(
            fact_id="fact.accepted.1",
            status=ZGFactStatus.ACCEPTED,
            subject_id="protocol",
            predicate="governance_attack_risk",
            value="elevated",
            source_id="feed.news.alpha",
            source_kind=ZGSourceKind.NEWS,
            microtheory="RiskPolicy",
            validator_status="validated",
            validation_receipt_ids=("receipt.1",),
            accepted_by="validator.local.1",
        )
    )
    store.append_fact(
        ZGFact(
            fact_id="fact.proposed.1",
            status=ZGFactStatus.PROPOSED,
            subject_id="protocol",
            predicate="treasury_signal",
            value="watch",
            source_id="model.extractor.1",
            source_kind=ZGSourceKind.MODEL,
            proposed_by="llm.extractor.1",
        )
    )

    pack_name = "zenograph.store.pack"
    review_path = _write_review(tmp_path, pack_name=pack_name)
    pack_path = tmp_path / "fact_pack.json"

    build_proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_FROM_STORE_CLI),
            "--store-root",
            str(store_root),
            "--pack-name",
            pack_name,
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
    assert build_report["counts"]["accepted_facts_scanned"] == 1
    assert build_report["counts"]["facts_exported"] == 1
    assert build_report["pack"]["facts"][0]["fact_id"] == "fact.accepted.1"

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
    assert verify_report["runtime_fact_count"] == 1
    assert verify_report["subject_predicates"] == ["protocol.governance_attack_risk"]
