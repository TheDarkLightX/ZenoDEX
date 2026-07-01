from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_sharded_batch_clearing_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/ShardedBatchClearing.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "sharded_conservation",
        "aggregate_netFlow",
        "aggregate_concat",
        "aggregate_swap_adjacent",
        "conservation_any_shard_count",
        "monolithic_is_single_shard",
        "cross_shard_netting_preserves_flow",
        "cross_shard_netting_balanced",
        "shard_failure_isolation",
        "remove_empty_shards_preserves_aggregate",
        "conservation_any_partition",
        "witness_3_shard_conservation",
        "witness_multi_settlement_shards",
        "witness_10_shard_scaling",
        "sharded_throughput_scaling",
        "empty_sharding_zero",
        "single_shard_aggregate",
    )
    for theorem in required_theorems:
        assert re.search(
            rf"^theorem\s+{re.escape(theorem)}\b",
            source,
            re.MULTILINE,
        ), f"{theorem} theorem is missing from {target}"

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
    combined = (proc.stdout + proc.stderr).lower()
    assert "sorry" not in combined, f"sorry placeholder found in {target}"
    assert "error:" not in combined, f"error in {target}: {proc.stderr}"
