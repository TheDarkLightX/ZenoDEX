from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_zeno_oracle_compositional_disaster_regressions import (
    CheckError,
    MANIFEST_PATH,
    build_receipt,
)


ROOT = Path(__file__).resolve().parents[1]


def test_compositional_disaster_regression_manifest_accepts_public_projection() -> None:
    receipt = build_receipt()

    assert receipt["schema"] == "zenodex/zeno-oracle-compositional-disaster-regression-check/v1"
    assert receipt["ok"] is True
    assert receipt["campaign_count"] == 2
    assert receipt["private_candidate_witness_count"] == 7
    assert receipt["accepted_public_regression_count"] == 3
    assert receipt["deferred_projection_count"] == 4
    assert set(receipt["accepted_public_regressions"]) == {
        "dex_engine_duplicate_nonce_replay",
        "dex_engine_quote_receipt_stale_pool_snapshot",
        "perp_submission_nonce_replay_without_consumption",
    }
    assert "strategy_policy_live_floor_o3" in receipt["deferred_projections"]


def test_compositional_disaster_regression_manifest_cli_text() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_compositional_disaster_regressions.py",
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "status = accepted" in result.stdout
    assert "accepted_public_regression_count = 3" in result.stdout


def test_compositional_disaster_regression_manifest_rejects_missing_public_test(tmp_path: Path) -> None:
    data = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    data["candidate_witness_projection"]["entries"][0]["test_file"] = "tests/missing_public_replay.py"
    path = tmp_path / "bad_manifest.json"
    path.write_text(json.dumps(data), encoding="utf-8")

    with pytest.raises(CheckError, match="missing"):
        build_receipt(path)
