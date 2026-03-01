#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from contextlib import contextmanager
from pathlib import Path
from statistics import median
from typing import Any, Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parents[1]

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import (
    find_tau_bin,
    run_tau_spec_steps,
    run_tau_spec_steps_spec_mode,
)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _compare_expected(
    *,
    expected: Optional[list[dict[str, Any]]],
    outputs: dict[int, dict[str, int]],
) -> Tuple[bool, Optional[dict[str, Any]]]:
    if not expected:
        return True, None

    for idx, want in enumerate(expected):
        got = outputs.get(idx, {})
        for k, v in want.items():
            if v is None:
                continue
            if k not in got:
                return False, {"step": idx, "key": k, "expected": v, "got": None}
            if int(got[k]) != int(v):
                return False, {"step": idx, "key": k, "expected": int(v), "got": int(got[k])}
    return True, None


def _compare_ab(
    *,
    a_outputs: dict[int, dict[str, int]],
    b_outputs: dict[int, dict[str, int]],
    step_count: int,
) -> Tuple[bool, Optional[dict[str, Any]]]:
    for idx in range(step_count):
        a = a_outputs.get(idx, {})
        b = b_outputs.get(idx, {})
        keys = sorted(set(a.keys()) | set(b.keys()))
        for k in keys:
            av = a.get(k)
            bv = b.get(k)
            if av is None or bv is None:
                return False, {"step": idx, "key": k, "a": av, "b": bv}
            if int(av) != int(bv):
                return False, {"step": idx, "key": k, "a": int(av), "b": int(bv)}
    return True, None


def _run_one(
    *,
    tau_bin: str,
    experimental: bool,
    mode: str,
    spec_path: Path,
    steps: list[dict[str, int]],
    timeout_s: float,
) -> dict[int, dict[str, int]]:
    if mode == "repl":
        return run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=steps,
            timeout_s=timeout_s,
            experimental=experimental,
        )
    if mode == "spec":
        return run_tau_spec_steps_spec_mode(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=steps,
            timeout_s=timeout_s,
            severity="error",
            experimental=experimental,
        )
    raise ValueError(f"unsupported mode: {mode!r}")


def _parse_env_kv(items: Optional[list[str]]) -> dict[str, str]:
    out: dict[str, str] = {}
    for raw in items or []:
        s = str(raw).strip()
        if not s:
            continue
        if "=" not in s:
            raise ValueError(f"env override must be KEY=VAL, got: {raw!r}")
        k, v = s.split("=", 1)
        k = k.strip()
        v = v.strip()
        if not k:
            raise ValueError(f"env override must have non-empty KEY, got: {raw!r}")
        out[k] = v
    return out


@contextmanager
def _patched_env(kv: dict[str, str]):
    old: dict[str, Optional[str]] = {}
    try:
        for k, v in kv.items():
            old[k] = os.environ.get(k)
            os.environ[k] = v
        yield
    finally:
        for k, prev in old.items():
            if prev is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = prev


def main() -> int:
    ap = argparse.ArgumentParser(description="A/B compare Tau binaries on tests/tau/spec_registry.json traces.")
    ap.add_argument(
        "--spec-registry",
        type=Path,
        default=Path("tests/tau/spec_registry.json"),
        help="Registry JSON (default: tests/tau/spec_registry.json).",
    )
    ap.add_argument("--timeout-s", type=float, default=60.0, help="Per-spec timeout (seconds).")
    ap.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="Repeat each spec N times and report median times (default: 1).",
    )
    ap.add_argument("--out", type=Path, default=Path("runs/tau_ab_compare_spec_registry/latest.json"))
    ap.add_argument("--a-tau-bin", type=Path, help="Tau binary A (default: auto-detect; or set TAU_BIN).")
    ap.add_argument("--b-tau-bin", type=Path, required=True, help="Tau binary B.")
    ap.add_argument("--a-experimental", action="store_true", help="Run A with --experimental.")
    ap.add_argument("--b-experimental", action="store_true", help="Run B with --experimental.")
    ap.add_argument(
        "--a-env",
        action="append",
        help="Environment override for A (repeatable KEY=VAL).",
    )
    ap.add_argument(
        "--b-env",
        action="append",
        help="Environment override for B (repeatable KEY=VAL).",
    )
    ap.add_argument("--include-skip", action="store_true", help="Also run registry entries marked mode=skip.")
    ap.add_argument(
        "--only",
        action="append",
        help="Run only this spec id (repeatable). If set, all other entries are skipped.",
    )
    ap.add_argument(
        "--exclude",
        action="append",
        help="Exclude this spec id (repeatable).",
    )
    ap.add_argument(
        "--max-specs",
        type=int,
        help="Run at most N specs after filtering.",
    )
    args = ap.parse_args()

    repeats = max(1, int(getattr(args, "repeat", 1)))
    reg_path = args.spec_registry if args.spec_registry.is_absolute() else (ROOT / args.spec_registry)
    data = _load_json(reg_path)
    specs = list(data.get("specs", []))

    only: Optional[set[str]] = None
    if args.only:
        only = {str(x).strip() for x in args.only if str(x).strip()}
    exclude: set[str] = set()
    if args.exclude:
        exclude = {str(x).strip() for x in args.exclude if str(x).strip()}

    tau_a = str(args.a_tau_bin) if getattr(args, "a_tau_bin", None) else find_tau_bin(ROOT)
    if not tau_a:
        raise SystemExit("tau binary A not found (set TAU_BIN=/path/to/tau or pass --a-tau-bin)")
    tau_b = str(args.b_tau_bin)

    a_env = _parse_env_kv(getattr(args, "a_env", None))
    b_env = _parse_env_kv(getattr(args, "b_env", None))

    rows: list[dict[str, Any]] = []
    ok = True
    ran = 0

    for spec in specs:
        sid = str(spec.get("id", ""))
        if only is not None and sid not in only:
            rows.append({"id": sid, "mode": spec.get("mode", "repl"), "skipped": True, "reason": "--only"})
            continue
        if sid in exclude:
            rows.append({"id": sid, "mode": spec.get("mode", "repl"), "skipped": True, "reason": "--exclude"})
            continue

        mode = str(spec.get("mode", "repl"))
        if mode == "skip" and not bool(args.include_skip):
            rows.append({"id": sid, "mode": mode, "skipped": True, "reason": spec.get("skip_reason", "")})
            continue
        if mode not in {"repl", "spec"}:
            rows.append({"id": sid, "mode": mode, "skipped": True, "reason": f"unsupported mode {mode!r}"})
            continue

        rel = spec.get("path", "")
        if not rel:
            rows.append({"id": sid, "mode": mode, "ok": False, "error": "missing spec path"})
            ok = False
            continue

        spec_path = (ROOT / str(rel)).resolve()
        steps = list(spec.get("inputs", []))
        expected = spec.get("expected")
        if not isinstance(steps, list) or not steps:
            rows.append({"id": sid, "mode": mode, "skipped": True, "reason": "no inputs"})
            continue

        if args.max_specs is not None and ran >= int(args.max_specs):
            rows.append({"id": sid, "mode": mode, "skipped": True, "reason": "--max-specs"})
            continue

        print(f"[tau-ab] running {sid} ({mode}, {len(steps)} step(s))", file=sys.stderr)
        t0 = time.perf_counter()
        try:
            a_out: dict[int, dict[str, int]] = {}
            b_out: dict[int, dict[str, int]] = {}
            a_ref: Optional[dict[int, dict[str, int]]] = None
            b_ref: Optional[dict[int, dict[str, int]]] = None
            elapsed_a_s_samples: list[float] = []
            elapsed_b_s_samples: list[float] = []

            # Run paired A/B trials to reduce drift and to detect nondeterministic outputs.
            # Alternate order (AB, BA, AB, ...) to reduce systematic warm-cache bias.
            for rep in range(repeats):
                # rep even: A then B. rep odd: B then A.
                for side in ("a", "b") if (rep % 2 == 0) else ("b", "a"):
                    if side == "a":
                        t0a = time.perf_counter()
                        with _patched_env(a_env):
                            a_rep = _run_one(
                                tau_bin=tau_a,
                                experimental=bool(args.a_experimental),
                                mode=mode,
                                spec_path=spec_path,
                                steps=steps,
                                timeout_s=float(args.timeout_s),
                            )
                        elapsed_a_s = float(time.perf_counter() - t0a)
                        elapsed_a_s_samples.append(elapsed_a_s)

                        if a_ref is None:
                            a_ref = a_rep
                            a_out = a_rep
                        else:
                            det_ok, det_detail = _compare_ab(a_outputs=a_ref, b_outputs=a_rep, step_count=len(steps))
                            if not det_ok:
                                raise RuntimeError(f"{sid}: nondeterministic A output at rep={rep}: {det_detail}")
                    else:
                        t0b = time.perf_counter()
                        with _patched_env(b_env):
                            b_rep = _run_one(
                                tau_bin=tau_b,
                                experimental=bool(args.b_experimental),
                                mode=mode,
                                spec_path=spec_path,
                                steps=steps,
                                timeout_s=float(args.timeout_s),
                            )
                        elapsed_b_s = float(time.perf_counter() - t0b)
                        elapsed_b_s_samples.append(elapsed_b_s)

                        if b_ref is None:
                            b_ref = b_rep
                            b_out = b_rep
                        else:
                            det_ok, det_detail = _compare_ab(a_outputs=b_ref, b_outputs=b_rep, step_count=len(steps))
                            if not det_ok:
                                raise RuntimeError(f"{sid}: nondeterministic B output at rep={rep}: {det_detail}")

            elapsed_s = float(time.perf_counter() - t0)

            exp_ok_a, exp_detail_a = _compare_expected(expected=expected, outputs=a_out)
            exp_ok_b, exp_detail_b = _compare_expected(expected=expected, outputs=b_out)
            ab_ok, ab_detail = _compare_ab(a_outputs=a_out, b_outputs=b_out, step_count=len(steps))

            elapsed_a_s = float(median(elapsed_a_s_samples))
            elapsed_b_s = float(median(elapsed_b_s_samples))
            row = {
                "id": sid,
                "mode": mode,
                "spec_path": str(spec_path),
                "steps": len(steps),
                "elapsed_s": elapsed_s,
                "elapsed_a_s": elapsed_a_s,
                "elapsed_b_s": elapsed_b_s,
                "elapsed_a_s_samples": [float(x) for x in elapsed_a_s_samples],
                "elapsed_b_s_samples": [float(x) for x in elapsed_b_s_samples],
                "repeat": int(repeats),
                "per_step_a_ms": (elapsed_a_s * 1000.0) / float(max(1, len(steps))),
                "per_step_b_ms": (elapsed_b_s * 1000.0) / float(max(1, len(steps))),
                "expected_ok_a": bool(exp_ok_a),
                "expected_ok_b": bool(exp_ok_b),
                "ab_ok": bool(ab_ok),
            }
            if exp_detail_a:
                row["expected_mismatch_a"] = exp_detail_a
            if exp_detail_b:
                row["expected_mismatch_b"] = exp_detail_b
            if ab_detail:
                row["ab_mismatch"] = ab_detail
            row["ok"] = bool(exp_ok_a and exp_ok_b and ab_ok)
            if not row["ok"]:
                ok = False
            rows.append(row)
            ran += 1
        except Exception as exc:
            elapsed_s = float(time.perf_counter() - t0)
            rows.append(
                {
                    "id": sid,
                    "mode": mode,
                    "spec_path": str(spec_path),
                    "steps": len(steps),
                    "elapsed_s": elapsed_s,
                    "ok": False,
                    "error": f"{type(exc).__name__}: {exc}",
                }
            )
            ok = False
            ran += 1

    payload = {
        "ok": bool(ok),
        "registry": str(reg_path),
        "timeout_s": float(args.timeout_s),
        "run_a": {"tau_bin": str(tau_a), "experimental": bool(args.a_experimental), "env": dict(a_env)},
        "run_b": {"tau_bin": str(tau_b), "experimental": bool(args.b_experimental), "env": dict(b_env)},
        "rows": rows,
    }

    out_path = args.out if args.out.is_absolute() else (ROOT / args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps({"ok": bool(ok), "out": str(out_path)}, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
