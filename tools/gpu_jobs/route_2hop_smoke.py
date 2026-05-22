#!/usr/bin/env python3
"""
Smoke test for GPU-assisted route improvement witness generation.

This runs:
1) tools/gpu_jobs/route_2hop_search_cpmm.py  (search; optionally GPU)
2) tools/proof_verifiers/route_improvement_v1.py (deterministic verification)

It is safe to run without a GPU; the search tool degrades gracefully to CPU.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List


_REPO_ROOT = Path(__file__).resolve().parents[2]


def _pool(
    *,
    pool_id: str,
    asset0: str,
    asset1: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int = 30,
) -> Dict[str, Any]:
    return {
        "pool_id": str(pool_id),
        "asset0": str(asset0),
        "asset1": str(asset1),
        "reserve0": int(reserve0),
        "reserve1": int(reserve1),
        "fee_bps": int(fee_bps),
        "curve_tag": "CPMM",
        "curve_params": "",
        "lp_supply": 0,
        "status": "ACTIVE",
        "created_at": 0,
    }


def main() -> int:
    # Assets (deterministic ids).
    a = "0x" + "01" * 32
    b = "0x" + "02" * 32
    c = "0x" + "03" * 32

    # Construct a scenario where 2-hop dominates:
    # - Direct A->C pool is shallow on C.
    # - A->B and B->C are deep.
    pools: List[Dict[str, Any]] = [
        _pool(pool_id="pool_ac_shallow", asset0=a, asset1=c, reserve0=1_000_000, reserve1=2_000, fee_bps=30),
        _pool(pool_id="pool_ab_deep", asset0=a, asset1=b, reserve0=5_000_000, reserve1=5_000_000, fee_bps=30),
        _pool(pool_id="pool_bc_deep", asset0=b, asset1=c, reserve0=5_000_000, reserve1=5_000_000, fee_bps=30),
    ]

    job = {"asset_in": a, "asset_out": c, "amount_in": 250_000, "pools": pools}

    with tempfile.TemporaryDirectory(prefix="zenodex_route_smoke_") as td:
        td_path = Path(td)
        job_path = td_path / "job.json"
        witness_path = td_path / "witness.json"
        job_path.write_text(json.dumps(job, indent=2, sort_keys=True) + "\n", encoding="utf-8")

        search_cmd = [
            sys.executable,
            str(_REPO_ROOT / "tools" / "gpu_jobs" / "route_2hop_search_cpmm.py"),
            "--input",
            str(job_path),
            "--output",
            str(witness_path),
            "--prefer-gpu",
            "--topk",
            "256",
        ]
        # If no improvement exists, still emit a witness for debugging.
        search_cmd.append("--allow-no-improvement")

        p = subprocess.run(search_cmd, check=False, cwd=str(_REPO_ROOT))
        if p.returncode != 0:
            sys.stderr.write(f"route search failed with code={p.returncode}\n")
            return int(p.returncode)

        payload = json.loads(witness_path.read_text(encoding="utf-8"))
        schema = payload.get("schema")
        meta = payload.get("meta", {})
        baseline_out = payload.get("baseline", {}).get("amount_out")
        proposal_out = payload.get("proposal", {}).get("amount_out")
        improves = payload.get("improves")

        verify_cmd = [
            sys.executable,
            str(_REPO_ROOT / "tools" / "proof_verifiers" / "route_improvement_v1.py"),
            "--input",
            str(witness_path),
        ]
        v = subprocess.run(verify_cmd, check=False, cwd=str(_REPO_ROOT), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

        sys.stdout.write("=== route_2hop_smoke ===\n")
        sys.stdout.write(f"schema={schema}\n")
        sys.stdout.write(f"approx_backend={meta.get('approx_backend')}\n")
        sys.stdout.write(f"baseline_out={baseline_out} proposal_out={proposal_out} improves={improves}\n")
        sys.stdout.write(f"verifier={v.stdout.strip()}\n")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())

