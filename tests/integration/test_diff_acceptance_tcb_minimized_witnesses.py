from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.diff_acceptance_tcb_minimized_witnesses import diff_indexes


ROOT_DIR = Path(__file__).resolve().parents[2]


def _index(*, campaign_report: str, witnesses: list[dict[str, object]]) -> dict[str, object]:
    return {
        "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-index/v1",
        "campaign_report": campaign_report,
        "count": len(witnesses),
        "witnesses": witnesses,
    }


def test_diff_indexes_detects_changed_added_and_removed() -> None:
    left = _index(
        campaign_report="left.json",
        witnesses=[
            {
                "id": "a",
                "target": "dex_request_envelope",
                "derivation": "DexReq->UnauthorizedWithDeadFields",
                "outcome_label": "handled:401:unauthorized",
                "path_id": "p1",
                "path_length": 10,
                "original_size": 20,
                "minimized_size": 5,
                "witness_out": "left/a.json",
            },
            {
                "id": "b",
                "target": "signed_intents",
                "derivation": "SignedOps->Duplicate",
                "outcome_label": "ValueError:duplicate",
                "path_id": "p2",
                "path_length": 29,
                "original_size": 40,
                "minimized_size": 30,
                "witness_out": "left/b.json",
            },
        ],
    )
    right = _index(
        campaign_report="right.json",
        witnesses=[
            {
                "id": "a",
                "target": "dex_request_envelope",
                "derivation": "DexReq->UnauthorizedWithDeadFields",
                "outcome_label": "handled:401:unauthorized",
                "path_id": "p1",
                "path_length": 10,
                "original_size": 20,
                "minimized_size": 5,
                "witness_out": "right/a.json",
            },
            {
                "id": "b",
                "target": "signed_intents",
                "derivation": "SignedOps->Duplicate",
                "outcome_label": "ValueError:duplicate",
                "path_id": "p3",
                "path_length": 31,
                "original_size": 40,
                "minimized_size": 28,
                "witness_out": "right/b.json",
            },
            {
                "id": "c",
                "target": "quote_receipt_transport",
                "derivation": "QuoteReceipt->MissingHash",
                "outcome_label": "reject:missing_receipt_hash",
                "path_id": "p4",
                "path_length": 103,
                "original_size": 600,
                "minimized_size": 100,
                "witness_out": "right/c.json",
            },
        ],
    )
    diff = diff_indexes(left, right)
    assert diff["unchanged"] == ["a"]
    assert [item["id"] for item in diff["added"]] == ["c"]
    assert diff["removed"] == []
    assert len(diff["changed"]) == 1
    changed = diff["changed"][0]
    assert changed["id"] == "b"
    assert set(changed["fields"]) == {"minimized_size", "path_id", "path_length"}


def test_diff_acceptance_tcb_minimized_witnesses_cli_reports_no_semantic_change(tmp_path: Path) -> None:
    witness = {
        "id": "api_request_unauthorized",
        "target": "dex_request_envelope",
        "derivation": "DexReq->UnauthorizedWithDeadFields",
        "outcome_label": "handled:401:unauthorized",
        "path_id": "8d3661cc0d8d784c",
        "path_length": 10,
        "original_size": 219,
        "minimized_size": 18,
        "witness_out": "placeholder.json",
    }
    left = tmp_path / "left.json"
    right = tmp_path / "right.json"
    left.write_text(json.dumps(_index(campaign_report="left", witnesses=[witness]), indent=2, sort_keys=True), encoding="utf-8")
    right.write_text(json.dumps(_index(campaign_report="right", witnesses=[{**witness, "witness_out": "other.json"}]), indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [
            sys.executable,
            "tools/diff_acceptance_tcb_minimized_witnesses.py",
            "--left",
            str(left),
            "--right",
            str(right),
            "--format",
            "text",
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "changed: 0" in proc.stdout
    assert "unchanged: 1" in proc.stdout
