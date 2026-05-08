from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.macos_scout.build_witness_space_receipt import build_receipt


ROOT = Path(__file__).resolve().parents[1]


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def _run_dir(tmp_path: Path, *, reasons: list[str]) -> Path:
    run_dir = tmp_path / f"run_{len(list(tmp_path.iterdir()))}"
    run_dir.mkdir()
    (run_dir / "summary.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos_derivatives_scout_summary/v1",
                "candidates": 32,
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
    _write_jsonl(run_dir / "reranked_top_candidates.jsonl", [])
    _write_jsonl(run_dir / "promotion_candidates.jsonl", [])
    return run_dir


def test_witness_space_receipt_opens_for_zero_counterexample_runs(tmp_path: Path) -> None:
    run_a = _run_dir(tmp_path, reasons=[])
    run_b = _run_dir(tmp_path, reasons=[])

    receipt = build_receipt([run_a, run_b])

    assert receipt["schema"] == "zenodex/macos-scout-witness-space-receipt/v1"
    assert receipt["ok"] is True
    assert receipt["gate"] == "OPEN_FOR_BOUNDED_RESEARCH"
    assert receipt["regression"]["counterexample_count"] == 0
    assert receipt["materialized_witness_count"] > 0
    assert receipt["reachable_witness_count"] == 0
    assert receipt["verdict_counts"] == {
        "NO_REACHABLE_WITNESS_BOUNDED": receipt["materialized_witness_count"]
    }
    assert receipt["frontier"]["compressed"] is True
    assert receipt["stable_receipt_hash"].startswith("sha256:")
    assert all(item["fail_closed"] for item in receipt["synthetic_mutations"])


def test_witness_space_receipt_blocks_reachable_disaster(tmp_path: Path) -> None:
    run_dir = _run_dir(tmp_path, reasons=["liquidity_floor_breach_under_oracle_gap"])

    receipt = build_receipt([run_dir])

    assert receipt["ok"] is False
    assert receipt["gate"] == "BLOCKED_REACHABLE_WITNESS"
    assert receipt["reachable_witness_count"] > 0
    assert any(
        "liquidity_floor_breach_under_oracle_gap" in witness["reasons"]
        for witness in receipt["reachable_witnesses"]
    )


def test_witness_space_receipt_cli_writes_json(tmp_path: Path) -> None:
    run_dir = _run_dir(tmp_path, reasons=[])
    output = tmp_path / "receipt.json"
    result = subprocess.run(
        [
            sys.executable,
            "tools/macos_scout/build_witness_space_receipt.py",
            "--run-dir",
            str(run_dir),
            "--output",
            str(output),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "gate = OPEN_FOR_BOUNDED_RESEARCH" in result.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["ok"] is True
