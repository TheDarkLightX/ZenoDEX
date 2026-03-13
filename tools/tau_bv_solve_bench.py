#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional

ROOT = Path(__file__).resolve().parents[1]

import sys

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


def _u_bv_max(bitwidth: int) -> int:
    if bitwidth <= 0 or bitwidth > 64:
        raise ValueError(f"unsupported bitwidth: {bitwidth} (expected 1..64)")
    return (1 << bitwidth) - 1


def _bva_values_u(bitwidth: int) -> list[int]:
    """
    Basic BVA set for unsigned bitvectors.

    Values are always in-range [0, 2^bitwidth - 1].
    """
    maxv = _u_bv_max(bitwidth)
    mid = maxv // 2
    raw = [
        0,
        1,
        2,
        maxv - 1 if maxv >= 1 else 0,
        maxv,
        mid - 1 if mid >= 1 else 0,
        mid,
        mid + 1 if mid < maxv else maxv,
    ]
    out: list[int] = []
    seen: set[int] = set()
    for v in raw:
        v2 = int(v) & maxv
        if v2 not in seen:
            out.append(v2)
            seen.add(v2)
    return out


def _lcg_u64(seed: int) -> int:
    # Deterministic LCG (glibc-like constants), kept 64-bit.
    return (seed * 1103515245 + 12345) & ((1 << 64) - 1)


def _gen_steps_bv_u(
    bitwidth: int,
    steps_n: int,
    *,
    map_value: Callable[[int], int],
    seed: int,
) -> list[dict[str, int]]:
    maxv = _u_bv_max(bitwidth)
    if steps_n <= 0:
        return []

    # Start with BVA values.
    values: list[int] = []
    for v in _bva_values_u(bitwidth):
        values.append(map_value(v) & maxv)

    # Fill deterministically with pseudo-random in-range values.
    s = int(seed) & ((1 << 64) - 1)
    while len(values) < steps_n:
        s = _lcg_u64(s)
        values.append(map_value(int(s) & maxv) & maxv)

    values = values[:steps_n]
    return [{"i1": int(v)} for v in values]


def _spec_texts() -> dict[str, str]:
    # Keep specs tiny and deterministic; write them to internal/ at runtime.
    return {
        "bv16_mul3_solve_v1": "\n".join(
            [
                "set charvar off",
                "always (o1[t]:bv[16] * { #x0003 }:bv[16] = i1[t]:bv[16]).",
                "",
            ]
        ),
        "bv16_mul3_assign_v1": "\n".join(
            [
                "set charvar off",
                "always (o1[t]:bv[16] = i1[t]:bv[16] * { #x0003 }:bv[16]).",
                "",
            ]
        ),
        "bv32_mul3_solve_v1": "\n".join(
            [
                "set charvar off",
                "always (o1[t]:bv[32] * { #x00000003 }:bv[32] = i1[t]:bv[32]).",
                "",
            ]
        ),
        "bv32_mul3_assign_v1": "\n".join(
            [
                "set charvar off",
                "always (o1[t]:bv[32] = i1[t]:bv[32] * { #x00000003 }:bv[32]).",
                "",
            ]
        ),
    }


def _write_specs(out_dir: Path) -> dict[str, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    specs: dict[str, Path] = {}
    for sid, text in _spec_texts().items():
        p = out_dir / f"{sid}.tau"
        if not p.exists() or p.read_text(encoding="utf-8") != text:
            p.write_text(text, encoding="utf-8")
        specs[sid] = p
    return specs


@dataclass(frozen=True)
class Case:
    spec_id: str
    bitwidth: int
    gen_steps: Callable[[int], list[dict[str, int]]]
    check: Callable[[dict[str, int], dict[str, int]], None]


def _case_defs(seed: int) -> list[Case]:
    def gen_mul3_16(n: int) -> list[dict[str, int]]:
        return _gen_steps_bv_u(16, n, map_value=lambda v: v, seed=seed ^ 0x16C0DE)

    def gen_mul3_32(n: int) -> list[dict[str, int]]:
        return _gen_steps_bv_u(32, n, map_value=lambda v: v, seed=seed ^ 0x32C0DE)

    def check_mul3(bitwidth: int) -> Callable[[dict[str, int], dict[str, int]], None]:
        maxv = _u_bv_max(bitwidth)
        c = 3

        def _check(inp: dict[str, int], out: dict[str, int]) -> None:
            i1 = int(inp["i1"]) & maxv
            o1 = int(out["o1"]) & maxv
            if (o1 * c) & maxv != i1:
                raise AssertionError(f"mul3 witness invalid (bw={bitwidth}): o1*3 != i1 (o1={o1}, i1={i1})")

        return _check

    def check_assign_mul3(bitwidth: int) -> Callable[[dict[str, int], dict[str, int]], None]:
        maxv = _u_bv_max(bitwidth)
        c = 3

        def _check(inp: dict[str, int], out: dict[str, int]) -> None:
            i1 = int(inp["i1"]) & maxv
            o1 = int(out["o1"]) & maxv
            if o1 != ((i1 * c) & maxv):
                raise AssertionError(f"mul3 assign invalid (bw={bitwidth}): o1 != i1*3 (o1={o1}, i1={i1})")

        return _check

    return [
        Case("bv16_mul3_assign_v1", 16, gen_mul3_16, check_assign_mul3(16)),
        Case("bv16_mul3_solve_v1", 16, gen_mul3_16, check_mul3(16)),
        Case("bv32_mul3_assign_v1", 32, gen_mul3_32, check_assign_mul3(32)),
        Case("bv32_mul3_solve_v1", 32, gen_mul3_32, check_mul3(32)),
    ]


def _bench_one(
    *,
    tau_bin: str,
    experimental: bool,
    case: Case,
    spec_path: Path,
    steps: list[dict[str, int]],
    timeout_s: float,
    verify_witness: bool,
) -> dict[str, object]:
    t0 = time.perf_counter()
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=steps,
            timeout_s=timeout_s,
            experimental=experimental,
        )
        elapsed_s = float(time.perf_counter() - t0)

        if verify_witness:
            for idx, inp in enumerate(steps):
                out = outputs.get(idx, {})
                if "o1" not in out:
                    raise AssertionError(f"missing o1 at step {idx} (case={case.spec_id})")
                case.check(inp, out)

        return {
            "ok": True,
            "spec_id": case.spec_id,
            "spec_path": str(spec_path),
            "bitwidth": int(case.bitwidth),
            "steps": int(len(steps)),
            "experimental": bool(experimental),
            "elapsed_s": elapsed_s,
            "per_step_ms": (elapsed_s * 1000.0) / float(max(1, len(steps))),
        }
    except Exception as exc:
        elapsed_s = float(time.perf_counter() - t0)
        return {
            "ok": False,
            "spec_id": case.spec_id,
            "spec_path": str(spec_path),
            "bitwidth": int(case.bitwidth),
            "steps": int(len(steps)),
            "experimental": bool(experimental),
            "elapsed_s": elapsed_s,
            "error": f"{type(exc).__name__}: {exc}",
        }


def main() -> int:
    ap = argparse.ArgumentParser(description="BV-heavy Tau microbench: solve for bv outputs under nonlinear constraints.")
    ap.add_argument("--steps", type=int, default=32, help="Number of steps per spec case.")
    ap.add_argument("--timeout-s", type=float, default=60.0)
    ap.add_argument("--repeat", type=int, default=1, help="Repeat each case N times (reports per-run rows).")
    ap.add_argument("--seed", type=int, default=0xC0DEF00D)
    ap.add_argument("--verify-witness", action="store_true", help="Check that tau outputs satisfy the spec equations.")
    ap.add_argument("--a-tau-bin", type=Path, help="Tau binary for run A (default: auto-detect; or set TAU_BIN).")
    ap.add_argument("--b-tau-bin", type=Path, help="Optional Tau binary for run B (A/B compare).")
    ap.add_argument("--a-experimental", action="store_true", help="Enable --experimental for run A.")
    ap.add_argument("--b-experimental", action="store_true", help="Enable --experimental for run B.")
    ap.add_argument("--out", type=Path, default=Path("runs/tau_bv_solve_bench/latest.json"))
    args = ap.parse_args()

    steps_n = max(1, int(args.steps))
    timeout_s = float(args.timeout_s)
    repeats = max(1, int(args.repeat))
    seed = int(args.seed)
    verify = bool(args.verify_witness)

    tau_a = str(args.a_tau_bin) if getattr(args, "a_tau_bin", None) else find_tau_bin(ROOT)
    if not tau_a:
        raise SystemExit("tau binary not found for run A (set TAU_BIN=/path/to/tau or pass --a-tau-bin)")
    tau_b: Optional[str] = str(args.b_tau_bin) if getattr(args, "b_tau_bin", None) else None

    spec_dir = ROOT / "internal" / "tau_microbench_specs" / "bv_solve"
    spec_paths = _write_specs(spec_dir)

    cases = _case_defs(seed=seed)
    rows_a: list[dict[str, object]] = []
    rows_b: list[dict[str, object]] = []

    for case in cases:
        spec_path = spec_paths.get(case.spec_id)
        if not spec_path:
            raise SystemExit(f"missing spec path for case: {case.spec_id}")
        steps = case.gen_steps(steps_n)
        for _ in range(repeats):
            rows_a.append(
                _bench_one(
                    tau_bin=tau_a,
                    experimental=bool(args.a_experimental),
                    case=case,
                    spec_path=spec_path,
                    steps=steps,
                    timeout_s=timeout_s,
                    verify_witness=verify,
                )
            )
            if tau_b:
                rows_b.append(
                    _bench_one(
                        tau_bin=tau_b,
                        experimental=bool(args.b_experimental),
                        case=case,
                        spec_path=spec_path,
                        steps=steps,
                        timeout_s=timeout_s,
                        verify_witness=verify,
                    )
                )

    ok = all(bool(r.get("ok")) for r in rows_a) and (all(bool(r.get("ok")) for r in rows_b) if tau_b else True)
    payload: dict[str, object] = {
        "ok": bool(ok),
        "steps": steps_n,
        "repeat": repeats,
        "timeout_s": timeout_s,
        "seed": seed,
        "verify_witness": verify,
        "spec_dir": str(spec_dir),
        "run_a": {"tau_bin": str(tau_a), "experimental": bool(args.a_experimental), "rows": rows_a},
    }
    if tau_b:
        payload["run_b"] = {"tau_bin": str(tau_b), "experimental": bool(args.b_experimental), "rows": rows_b}

    out_path = args.out if args.out.is_absolute() else (ROOT / args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps({"ok": bool(ok), "out": str(out_path)}, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
