from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT_DIR = Path(__file__).resolve().parents[2]


def _write_index(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-shared-index/v1",
                "campaign_count": 2,
                "witness_count": 3,
                "campaigns": [
                    {
                        "campaign_dir": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7",
                        "campaign_report": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7/acceptance_tcb_fuzz_report.json",
                        "count": 2,
                        "index_out": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7/minimized_witness_index.json",
                    },
                    {
                        "campaign_dir": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8",
                        "campaign_report": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/acceptance_tcb_fuzz_report.json",
                        "count": 1,
                        "index_out": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/minimized_witness_index.json",
                    },
                ],
                "witnesses": [
                    {
                        "campaign_dir": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7",
                        "campaign_report": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7/acceptance_tcb_fuzz_report.json",
                        "id": "api_request_unauthorized",
                        "target": "dex_request_envelope",
                        "derivation": "DexReq->UnauthorizedWithDeadFields",
                        "outcome_label": "handled:401:unauthorized",
                        "path_id": "8d3661cc0d8d784c",
                        "minimized_size": 18,
                        "witness_out": "internal/fuzz_campaigns/20260405T160500Z_acceptance-tcb-fuzz-r7/minimized_witnesses/api_request_unauthorized.json",
                    },
                    {
                        "campaign_dir": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8",
                        "campaign_report": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/acceptance_tcb_fuzz_report.json",
                        "id": "api_request_unauthorized",
                        "target": "dex_request_envelope",
                        "derivation": "DexReq->UnauthorizedWithDeadFields",
                        "outcome_label": "handled:401:unauthorized",
                        "path_id": "8d3661cc0d8d784c",
                        "minimized_size": 18,
                        "witness_out": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/minimized_witnesses/api_request_unauthorized.json",
                    },
                    {
                        "campaign_dir": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8",
                        "campaign_report": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/acceptance_tcb_fuzz_report.json",
                        "id": "operations_duplicate_signature",
                        "target": "signed_intents",
                        "derivation": "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail",
                        "outcome_label": "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field)",
                        "path_id": "ead30224ed217555",
                        "minimized_size": 308,
                        "witness_out": "internal/fuzz_campaigns/20260405T162500Z_acceptance-tcb-fuzz-r8/minimized_witnesses/operations_duplicate_signature.json",
                    },
                ],
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )


def test_query_minimized_witnesses_filters_by_target_and_latest(tmp_path: Path) -> None:
    index = tmp_path / "minimized_witness_index.json"
    _write_index(index)
    proc = subprocess.run(
        [
            sys.executable,
            "tools/query_acceptance_tcb_minimized_witnesses.py",
            "--index",
            str(index),
            "--target",
            "dex_request_envelope",
            "--latest-only",
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["schema"] == "zenodex/acceptance-tcb-fuzz-minimized-witness-query/v1"
    assert payload["matched"] == 1
    assert payload["witnesses"][0]["campaign_dir"].endswith("r8")
    assert payload["witnesses"][0]["id"] == "api_request_unauthorized"


def test_query_minimized_witnesses_filters_by_path_id_text_output(tmp_path: Path) -> None:
    index = tmp_path / "minimized_witness_index.json"
    _write_index(index)
    proc = subprocess.run(
        [
            sys.executable,
            "tools/query_acceptance_tcb_minimized_witnesses.py",
            "--index",
            str(index),
            "--path-id",
            "ead30224ed217555",
            "--format",
            "text",
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "matched: 1" in proc.stdout
    assert "operations_duplicate_signature" in proc.stdout
    assert "ead30224ed217555" in proc.stdout
