from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.macos_scout.check_scout_regression_gate import build_receipt


ROOT = Path(__file__).resolve().parents[1]


GOOD_CANDIDATE = {
    "id": 7,
    "score": 10.0,
    "disaster_rate": 0.0,
    "min_insurance_ratio": 1.01,
    "guard_block_rate": 0.01,
    "payout_budget_clamp_rate": 0.10,
    "funding_clamp_rate": 0.10,
    "legal_shape_ok": True,
    "candidate": {
        "fee_burn_share": 0.20,
        "insurance_share": 0.20,
        "payout_cap_share": 0.25,
    },
}


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def _write_run(tmp_path: Path, *, reasons: list[str], promotions: list[dict] | None = None) -> Path:
    run_dir = tmp_path / f"run_{len(list(tmp_path.iterdir()))}"
    run_dir.mkdir()
    (run_dir / "summary.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos_derivatives_scout_summary/v1",
                "candidates": 16,
            }
        ),
        encoding="utf-8",
    )
    _write_jsonl(
        run_dir / "counterexamples.jsonl",
        [
            {
                "id": index + 1,
                "path": 1,
                "step": 1,
                "reason": reason,
                "price": 1.0,
                "oracle": 1.0,
                "insurance": 1_000_000.0,
                "liquidity": 0.5,
                "drawdown": 0.0,
            }
            for index, reason in enumerate(reasons)
        ],
    )
    _write_jsonl(run_dir / "reranked_top_candidates.jsonl", [GOOD_CANDIDATE])
    _write_jsonl(run_dir / "promotion_candidates.jsonl", promotions if promotions is not None else [GOOD_CANDIDATE])
    return run_dir


def test_scout_regression_gate_accepts_classified_repeat_reasons(tmp_path: Path) -> None:
    run_a = _write_run(
        tmp_path,
        reasons=[
            "liquidity_floor_breach_under_oracle_gap",
            "payout_cap_exceeded_initial_budget",
        ],
    )
    run_b = _write_run(
        tmp_path,
        reasons=[
            "liquidity_floor_breach_under_oracle_gap",
            "funding_too_aggressive_in_thin_liquidity",
        ],
    )

    receipt = build_receipt([run_a, run_b])

    assert receipt["schema"] == "zenodex/macos-scout-regression-gate/v1"
    assert receipt["ok"] is True
    assert receipt["aggregate_reason_counts"] == {
        "funding_too_aggressive_in_thin_liquidity": 1,
        "liquidity_floor_breach_under_oracle_gap": 2,
        "payout_cap_exceeded_initial_budget": 1,
    }
    assert receipt["unknown_reasons"] == []


def test_scout_regression_gate_rejects_unclassified_reason(tmp_path: Path) -> None:
    run_dir = _write_run(tmp_path, reasons=["new_unclassified_disaster"])

    receipt = build_receipt([run_dir])

    assert receipt["ok"] is False
    assert receipt["unknown_reasons"] == ["new_unclassified_disaster"]


def test_scout_regression_gate_rejects_bad_promotion_candidate(tmp_path: Path) -> None:
    bad = dict(GOOD_CANDIDATE)
    bad["disaster_rate"] = 0.01
    run_dir = _write_run(
        tmp_path,
        reasons=["liquidity_floor_breach_under_oracle_gap"],
        promotions=[bad],
    )

    receipt = build_receipt([run_dir])

    assert receipt["ok"] is False
    assert "disaster_rate must be zero" in receipt["promotion_errors"][0]


def test_scout_regression_gate_cli_writes_text(tmp_path: Path) -> None:
    run_dir = _write_run(tmp_path, reasons=["liquidity_floor_breach_under_oracle_gap"])
    result = subprocess.run(
        [
            sys.executable,
            "tools/macos_scout/check_scout_regression_gate.py",
            "--run-dir",
            str(run_dir),
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
    assert "liquidity_floor_breach_under_oracle_gap" in result.stdout
