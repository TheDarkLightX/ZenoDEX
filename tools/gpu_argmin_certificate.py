#!/usr/bin/env python3
"""
GPU-assisted argmin certificate generator for Tau.

This is an off-chain helper:
- Compute the canonical winner (argmin) under lex order on (key_u64, index_u32).
- Emit Tau steps for `src/tau_specs/recommended/argmin_stream_certificate_v1.tau`.

Torch is optional. If installed, we can use MPS/CUDA for large candidate sets.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, List, Tuple


def _try_import_torch() -> Any | None:
    try:
        import torch  # type: ignore

        return torch
    except Exception:
        return None


@dataclass(frozen=True)
class Candidate:
    key_u64: int
    index_u32: int


def _require_int(name: str, v: Any) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int, got {type(v).__name__}")
    return int(v)


def _u32(name: str, v: Any) -> int:
    iv = _require_int(name, v)
    if iv < 0 or iv > 0xFFFFFFFF:
        raise ValueError(f"{name} out of u32 range: {iv}")
    return iv


def _u64(name: str, v: Any) -> int:
    iv = _require_int(name, v)
    if iv < 0 or iv > 0xFFFFFFFFFFFFFFFF:
        raise ValueError(f"{name} out of u64 range: {iv}")
    return iv


def _split_u64(x: int) -> Tuple[int, int]:
    return (x >> 32) & 0xFFFFFFFF, x & 0xFFFFFFFF


def _read_candidates(path: Path) -> List[Candidate]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, list):
        raise TypeError("input JSON must be a list of {key,index} objects")
    out: List[Candidate] = []
    for i, item in enumerate(obj):
        if not isinstance(item, dict):
            raise TypeError(f"candidate[{i}] must be an object")
        key = _u64(f"candidate[{i}].key", item.get("key"))
        idx = _u32(f"candidate[{i}].index", item.get("index", i))
        out.append(Candidate(key_u64=key, index_u32=idx))
    if not out:
        raise ValueError("no candidates provided")
    return out


def _argmin_cpu(cands: Iterable[Candidate]) -> Candidate:
    return min(cands, key=lambda c: (c.key_u64, c.index_u32))


def _argmin_torch(cands: List[Candidate], *, prefer_gpu: bool) -> Candidate:
    torch = _try_import_torch()
    if torch is None:
        return _argmin_cpu(cands)

    device = torch.device("cpu")
    if prefer_gpu and bool(getattr(torch.backends, "mps", None)) and torch.backends.mps.is_available():
        device = torch.device("mps")
    elif prefer_gpu and bool(getattr(torch, "cuda", None)) and torch.cuda.is_available():
        device = torch.device("cuda")

    # Compare unsigned u64 by (hi, lo). This avoids signed int64 overflow issues.
    keys_hi = torch.tensor([_split_u64(c.key_u64)[0] for c in cands], dtype=torch.int64, device=device)
    keys_lo = torch.tensor([_split_u64(c.key_u64)[1] for c in cands], dtype=torch.int64, device=device)
    idxs = torch.tensor([c.index_u32 for c in cands], dtype=torch.int64, device=device)

    min_hi = int(torch.min(keys_hi).item())
    mask_hi = keys_hi == min_hi
    # Guard: torch.min on empty would error, but mask_hi is non-empty by definition.
    min_lo = int(torch.min(keys_lo[mask_hi]).item())
    mask_hilo = mask_hi & (keys_lo == min_lo)
    min_idx = int(torch.min(idxs[mask_hilo]).item())

    # Return the first candidate matching the triple (min_hi, min_lo, min_idx).
    for c in cands:
        hi, lo = _split_u64(c.key_u64)
        if hi == min_hi and lo == min_lo and int(c.index_u32) == min_idx:
            return c
    raise RuntimeError("argmin selection failed (unexpected)")


def _emit_steps(*, winner: Candidate, cands: List[Candidate]) -> List[dict[str, int]]:
    steps: List[dict[str, int]] = []
    for c in cands:
        steps.append(
            {
                "i1": int(winner.key_u64),
                "i2": int(winner.index_u32),
                "i3": int(c.key_u64),
                "i4": int(c.index_u32),
                "i5": 1,
            }
        )
    return steps


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="Path to JSON list of candidates: [{\"key\":<u64>,\"index\":<u32>}].")
    ap.add_argument("--output", required=True, help="Path to write Tau steps JSON.")
    ap.add_argument("--prefer-gpu", action="store_true", help="Prefer GPU backend when available (MPS/CUDA).")
    ap.add_argument("--limit", type=int, default=0, help="Optional cap on number of candidates emitted (0 = all).")
    args = ap.parse_args()

    cands = _read_candidates(Path(args.input))
    if args.limit and args.limit > 0:
        cands = cands[: int(args.limit)]
    winner = _argmin_torch(cands, prefer_gpu=bool(args.prefer_gpu))
    steps = _emit_steps(winner=winner, cands=cands)

    out_obj = {
        "winner": {"key": int(winner.key_u64), "index": int(winner.index_u32)},
        "steps": steps,
    }
    Path(args.output).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

