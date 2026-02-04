#!/usr/bin/env python3
"""
GPU-accelerated semantic checker for private-toolchain hole expressions (Mac-friendly via Torch MPS).

This is a *fast refuter/ranker* for candidate hole terms:
- Samples many random (state, params) environments within type bounds.
- Filters to environments where the reference action is applicable (invariants + guard).
- Evaluates the reference expression vs a candidate term in batch on the selected backend.

It does NOT replace the toolchain's SMT verification; it is meant to cut solver calls and
quickly reject obviously wrong hints/candidates.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Optional

from esso_gpu_semantics import Counterexample, ensure_esso_on_path, semantic_check_single


def main() -> int:
    ap = argparse.ArgumentParser(description="GPU-accelerated semantic checker for hole expressions.")
    ap.add_argument("--model", required=True, help="Path to hole model YAML (kernel IR).")
    ap.add_argument("--synth", required=True, help="Path to synth spec JSON.")
    ap.add_argument("--reference", required=True, help="Path to reference model YAML (same action/field).")
    ap.add_argument("--hole-id", required=True, help="Hole id from synth spec (for parsing term).")
    ap.add_argument("--action", required=True, help="Action id where the hole is used.")
    ap.add_argument("--field", required=True, help="Field name (effect id or state var update) to compare.")
    ap.add_argument("--term", required=True, help="Candidate term (S-expression or infix).")
    ap.add_argument("--samples", type=int, default=100_000, help="Number of applicable samples to check.")
    ap.add_argument("--chunk", type=int, default=200_000, help="Chunk size for sampling/filtering.")
    ap.add_argument("--prefer-gpu", action="store_true", help="Prefer GPU backend when available (MPS/CUDA).")
    ap.add_argument("--seed", type=int, default=0, help="PRNG seed (default: 0).")
    ap.add_argument("--self-check", action="store_true", help="Cross-check a few samples against toolchain interpreter (slow).")
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = ap.parse_args()

    model_path = Path(args.model).expanduser().resolve()
    synth_path = Path(args.synth).expanduser().resolve()
    ref_path = Path(args.reference).expanduser().resolve()

    if not model_path.is_file():
        raise SystemExit(f"model not found: {model_path}")
    if not synth_path.is_file():
        raise SystemExit(f"synth not found: {synth_path}")
    if not ref_path.is_file():
        raise SystemExit(f"reference not found: {ref_path}")
    if args.samples <= 0:
        raise SystemExit("--samples must be > 0")
    if args.chunk <= 0:
        raise SystemExit("--chunk must be > 0")

    ensure_esso_on_path()

    res = semantic_check_single(
        model_path=model_path,
        synth_path=synth_path,
        reference_path=ref_path,
        hole_id=str(args.hole_id),
        action_id=str(args.action),
        field=str(args.field),
        term=str(args.term),
        samples=int(args.samples),
        chunk=int(args.chunk),
        prefer_gpu=bool(args.prefer_gpu),
        seed=int(args.seed),
        self_check=bool(args.self_check),
    )

    out = {
        "ok": bool(res.ok),
        "backend": str(res.backend),
        "samples": int(res.samples),
        "mismatch_count": int(res.mismatch_count),
        "mismatch_rate": float(res.mismatch_rate),
        "counterexample": _ce_to_json(res.counterexample),
    }

    if args.json:
        sys.stdout.write(json.dumps(out, sort_keys=True, indent=2) + "\n")
    else:
        sys.stdout.write(
            f"backend={out['backend']} samples={out['samples']} mismatches={out['mismatch_count']} rate={out['mismatch_rate']:.6f}\n"
        )
        ce = out["counterexample"]
        if ce is not None:
            sys.stdout.write(f"first_mismatch idx={ce['idx']} expected={ce['expected']} got={ce['got']}\n")

    return 0 if res.ok else 2


def _ce_to_json(ce: Optional[Counterexample]) -> Optional[dict[str, Any]]:
    if ce is None:
        return None
    return {
        "idx": int(ce.idx),
        "state": {k: int(v) for k, v in ce.state.items()},
        "params": {k: int(v) for k, v in ce.params.items()},
        "expected": int(ce.expected),
        "got": int(ce.got),
    }


if __name__ == "__main__":
    raise SystemExit(main())
