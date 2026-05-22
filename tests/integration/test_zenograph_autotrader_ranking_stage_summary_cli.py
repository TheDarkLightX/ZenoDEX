from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_stage_summary.py"


def test_zenograph_autotrader_ranking_stage_summary_cli_renders_markdown(
    tmp_path: Path,
) -> None:
    report_path = tmp_path / "ranking_stage_report.json"
    report_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-ranking-stage-report/v1",
                "risk_disclosure": {
                    "summary": "Advanced experimental automation and AI shadow surface.",
                    "guidance": [
                        "Do not use unless you understand the strategy.",
                        "Prefer shadow/replay mode before any live-preparation workflow.",
                    ],
                },
                "ranking_stage": {
                    "current_template_id": "dca",
                    "effective_ranking_template_id": "dca",
                    "zenograph_selected_template_id": None,
                    "stage_tag": "blocked",
                    "block_reason": "submit_vs_block_disagreement",
                    "unmet_criteria": ["submit_vs_block_zero"],
                },
                "zenograph_advisory": {
                    "tactic_evaluation": {
                        "admissible": False,
                        "blocked_reasons": ["governance_risk_elevated"],
                    }
                },
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--stage-report-file",
            str(report_path),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    assert "# ZenoGraph Ranking Stage" in completed.stdout
    assert "Stage tag: `blocked`" in completed.stdout
    assert "submit_vs_block_zero" in completed.stdout
