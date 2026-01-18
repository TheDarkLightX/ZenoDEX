#!/usr/bin/env python3
"""
Trace-level Tau spec harness (imperative shell).

Goal: produce concrete, reproducible evidence that production Tau specs execute
and emit expected outputs on representative inputs.

This is NOT a proof of correctness. It is a practical "does it run / does it
match the expected trace outputs?" check.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import time
from pathlib import Path
from typing import Dict, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps_with_trace  # noqa: E402
from src.integration.tau_runner import run_tau_spec_steps_spec_mode_with_trace  # noqa: E402
from src.integration.tau_trace_cases import TauTraceCase, production_tau_trace_cases  # noqa: E402


def _compare_expected(
    outputs_by_step: Dict[int, Dict[str, int]],
    expected: list[dict[str, int]],
    *,
    label: str,
) -> None:
    if not expected:
        raise RuntimeError(f"{label}: empty expected list")
    for idx, exp_step in enumerate(expected):
        got = outputs_by_step.get(idx, {})
        for name, exp_val in exp_step.items():
            got_val = got.get(name)
            if got_val != exp_val:
                raise RuntimeError(f"{label}: {name}[{idx}] expected {exp_val} got {got_val}")


def _run_case(
    *,
    tau_bin: str,
    case: TauTraceCase,
    timeout_s: float,
    severity: str,
) -> Tuple[bool, Dict[int, Dict[str, int]], str, str, str, str, str, Optional[str]]:
    try:
        if case.mode == "spec":
            outputs, out, err, spec_text, input_text = run_tau_spec_steps_spec_mode_with_trace(
                tau_bin=tau_bin,
                spec_path=case.spec.path,
                steps=case.steps,
                timeout_s=timeout_s,
                severity=severity,
                experimental=case.experimental,
            )
            repl = ""
        elif case.mode == "repl":
            outputs, out, err, repl = run_tau_spec_steps_with_trace(
                tau_bin=tau_bin,
                spec_path=case.spec.path,
                steps=case.steps,
                timeout_s=timeout_s,
                severity=severity,
                inline_defs=case.inline_defs,
                experimental=case.experimental,
            )
            spec_text = ""
            input_text = ""
        else:
            raise ValueError(f"unknown Tau trace case mode: {case.mode!r}")
        _compare_expected(outputs, case.expected, label=case.case_id)
        return True, outputs, out, err, repl, spec_text, input_text, None
    except TauRunError as exc:
        msg = str(exc)
        kind = "error"
        if "timed out" in msg.lower():
            kind = "timeout"
        elif "syntax error" in msg.lower():
            kind = "syntax"
        return (
            False,
            {},
            exc.stdout,
            exc.stderr,
            exc.repl_script,
            getattr(exc, "spec_text", "") or "",
            getattr(exc, "input_text", "") or "",
            f"{kind}:{type(exc).__name__}: {exc}",
        )
    except Exception as exc:
        msg = str(exc)
        kind = "error"
        if "timed out" in msg.lower():
            kind = "timeout"
        elif "syntax error" in msg.lower():
            kind = "syntax"
        return False, {}, "", "", "", "", "", f"{kind}:{type(exc).__name__}: {exc}"


def main(argv: Optional[Sequence[str]] = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--tau-bin", default="", help="Path to tau binary (defaults to auto-detect)")
    p.add_argument("--timeout-s", type=float, default=30.0, help="Default timeout per case (seconds)")
    p.add_argument("--severity", default="trace", choices=["trace", "debug", "info", "error"])
    p.add_argument("--json-out", default=str(REPO_ROOT / "generated" / "tau_trace_harness_report.json"))
    p.add_argument(
        "--no-case-timeouts",
        action="store_true",
        help="Ignore per-case timeout hints embedded in the harness; use --timeout-s for all cases.",
    )
    p.add_argument(
        "--only",
        action="append",
        default=[],
        help="Restrict to a spec_id or case_id (repeatable), e.g. --only settlement_v1 --only swap_exact_in_v4_pass",
    )
    args = p.parse_args(list(argv) if argv is not None else None)

    raw_tau_bin = str(args.tau_bin).strip()
    if raw_tau_bin:
        tau_path = Path(raw_tau_bin)
        if not tau_path.is_absolute():
            tau_path = (REPO_ROOT / tau_path).resolve()
        tau_bin = str(tau_path)
    else:
        tau_bin = find_tau_bin(REPO_ROOT) or ""

    if not tau_bin:
        print("ERROR: tau binary not found (build external/tau-lang or set --tau-bin)", file=sys.stderr)
        return 2

    cases = production_tau_trace_cases()
    only: set[str] = {str(x).strip() for x in (args.only or []) if str(x).strip()}
    if only:
        cases = [c for c in cases if c.case_id in only or c.spec.spec_id in only]
        if not cases:
            print(f"ERROR: --only did not match any known case/spec: {sorted(only)}", file=sys.stderr)
            return 2

    results = []
    ok_all = True

    artifacts_root = REPO_ROOT / "generated" / "tau_trace_harness"
    artifacts_root.mkdir(parents=True, exist_ok=True)

    for case in cases:
        per_timeout = float(args.timeout_s)
        if not bool(args.no_case_timeouts):
            per_timeout = float(case.timeout_s)
        if str(args.severity) in {"trace", "debug"} and per_timeout < 30.0:
            per_timeout = 30.0

        start = time.perf_counter()
        ok, outputs, out, err_text, repl, spec_text, input_text, err = _run_case(
            tau_bin=tau_bin,
            case=case,
            timeout_s=per_timeout,
            severity=str(args.severity),
        )
        elapsed_s = time.perf_counter() - start
        ok_all = ok_all and ok

        case_dir = artifacts_root / case.case_id
        case_dir.mkdir(parents=True, exist_ok=True)

        try:
            shutil.copy2(case.spec.path, case_dir / "spec.tau")
        except Exception:
            # Evidence is best-effort; do not fail the run on snapshot failure.
            pass

        (case_dir / "stdout.txt").write_text(out or "", encoding="utf-8", errors="replace")
        (case_dir / "stderr.txt").write_text(err_text or "", encoding="utf-8", errors="replace")
        if case.mode == "spec":
            (case_dir / "spec_normalized.tau").write_text(spec_text or "", encoding="utf-8", errors="replace")
            (case_dir / "spec_mode_inputs.txt").write_text(input_text or "", encoding="utf-8", errors="replace")
        else:
            (case_dir / "repl_script.tau").write_text(repl or "", encoding="utf-8", errors="replace")
        (case_dir / "outputs.json").write_text(json.dumps(outputs, indent=2), encoding="utf-8")
        (case_dir / "expected.json").write_text(json.dumps(case.expected, indent=2), encoding="utf-8")

        results.append(
            {
                "case_id": case.case_id,
                "spec_id": case.spec.spec_id,
                "spec_path": str(case.spec.path),
                "ok": ok,
                "error": err,
                "outputs_by_step": outputs,
                "expected": case.expected,
                "mode": case.mode,
                "timeout_s": per_timeout,
                "elapsed_s": elapsed_s,
                "inline_defs": case.inline_defs,
                "experimental": case.experimental,
                "artifacts_dir": str(case_dir),
            }
        )

        status = "PASS" if ok else "FAIL"
        print(
            f"[{status}] {case.case_id} ({case.spec.spec_id}) "
            f"elapsed_s={elapsed_s:.2f} timeout_s={per_timeout} severity={args.severity}"
        )
        if err:
            print(f"  {err}")

    out_path = Path(str(args.json_out))
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"ok": ok_all, "results": results}, indent=2), encoding="utf-8")
    print(f"wrote {out_path}")

    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
