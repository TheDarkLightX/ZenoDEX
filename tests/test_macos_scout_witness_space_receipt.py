from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.macos_scout import build_witness_space_receipt as witness_receipts
from tools.macos_scout.build_witness_space_receipt import build_receipt


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests" / "fixtures" / "macos_scout"
POST_HARDENING_FIXTURE_HASH = "sha256:3cf55a9dc31294e707c0e219d335ebf258ad42d77670ef67862052a85f5e8d5a"
PRE_HARDENING_BLOCKED_FIXTURE_HASH = "sha256:ab48553793c32f496ad857722c5e44df8da14d2abdf97d748a9e0bdfa81eca55"
EXPECTED_FAMILY_COUNTS = {
    "chain_terminal_disaster": 12,
    "convergence_composition_disaster": 4,
    "cycle_amplification_disaster": 3,
    "edge_composition_disaster": 8,
    "fanout_composition_disaster": 2,
    "independent_2_coreachability": 18,
    "order_inversion_disaster": 8,
    "reentry_retry_disaster": 2,
    "single_surface_disaster": 8,
}


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
    assert receipt["frontier"]["total"] > 0
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


def test_witness_space_receipt_blocks_dirty_checker_when_clean_required(tmp_path: Path, monkeypatch) -> None:
    run_dir = _run_dir(tmp_path, reasons=[])
    monkeypatch.setattr(
        witness_receipts,
        "_worktree_dirty",
        lambda _paths: ["tools/macos_scout/build_witness_space_receipt.py"],
    )

    receipt = witness_receipts.build_receipt([run_dir], require_clean=True)

    assert receipt["ok"] is False
    assert receipt["gate"] == "BLOCKED_REACHABLE_WITNESS"
    assert receipt["reachable_witness_count"] == 0
    assert receipt["gate_critical_dirty_paths"] == ["tools/macos_scout/build_witness_space_receipt.py"]


def test_public_post_hardening_fixture_has_stable_reduction_receipt() -> None:
    receipt = build_receipt([FIXTURES / "post_hardening_zero"])

    assert receipt["ok"] is True
    assert receipt["gate"] == "OPEN_FOR_BOUNDED_RESEARCH"
    assert receipt["stable_receipt_hash"] == POST_HARDENING_FIXTURE_HASH
    assert receipt["materialized_witness_count"] == 65
    assert receipt["reachable_witness_count"] == 0
    assert receipt["family_counts"] == EXPECTED_FAMILY_COUNTS
    assert receipt["frontier"] == {
        "min_order": 3,
        "max_order": 5,
        "by_order": {"3": 9, "4": 0, "5": 0},
        "total": 9,
        "compressed": True,
    }
    assert receipt["graph_frontier"] == {
        "surface_count": 8,
        "max_simple_path_depth": 5,
        "simple_path_count": 17,
        "terminal_path_count": 12,
        "fanout_count": 2,
        "convergence_count": 4,
        "cycle_count": 3,
        "simple_path_frontier_exhausted": True,
    }


def test_public_pre_hardening_fixture_still_blocks_reachable_witnesses() -> None:
    receipt = build_receipt([FIXTURES / "pre_hardening_blocked"])

    assert receipt["ok"] is False
    assert receipt["gate"] == "BLOCKED_REACHABLE_WITNESS"
    assert receipt["stable_receipt_hash"] == PRE_HARDENING_BLOCKED_FIXTURE_HASH
    assert receipt["materialized_witness_count"] == 65
    assert receipt["reachable_witness_count"] == 43
    assert receipt["verdict_counts"] == {
        "NO_REACHABLE_WITNESS_BOUNDED": 22,
        "REACHABLE_DISASTER_WITNESS": 43,
    }


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
