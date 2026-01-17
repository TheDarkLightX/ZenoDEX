#!/usr/bin/env python3
"""Smoke-test recommended specs via Tau REPL execution."""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tests.tau import check_formal_completeness as cfc


def normalize_spec_text(text: str) -> str:
    """Strip comments and collapse multi-line always blocks for REPL harness."""
    lines = []
    raw = text.splitlines()
    i = 0
    while i < len(raw):
        line = raw[i]
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue
        if stripped.startswith("set charvar"):
            i += 1
            continue
        if stripped.startswith("always"):
            expr_parts = []
            tail = stripped[len("always"):].strip()
            if tail:
                expr_parts.append(tail)
            i += 1
            while i < len(raw):
                nxt = raw[i].strip()
                if not nxt or nxt.startswith("#"):
                    i += 1
                    continue
                expr_parts.append(nxt)
                if nxt.endswith("."):
                    break
                i += 1
            joined = " ".join(expr_parts)
            if joined.endswith("."):
                joined = joined[:-1]
            lines.append(f"always {joined}.")
            i += 1
            continue
        lines.append(stripped)
        i += 1
    return "\n".join(lines) + "\n"

RECOMMENDED = ROOT / "src" / "tau_specs" / "recommended"


def build_inputs(stream_types, steps: int = 3):
    inputs = []
    for _ in range(steps):
        step = {}
        for name, typ in stream_types.items():
            if not name.startswith("i"):
                continue
            if typ.startswith("sbf"):
                step[name] = 1
            else:
                step[name] = 1
        inputs.append(step)
    return inputs


def smoke_spec(tau_bin: Path, spec_path: Path, timeout_s: int = 12, mode: str = "syntax"):
    spec_text = normalize_spec_text(cfc.rewrite_ternaries(spec_path.read_text()))
    stream_types = cfc.extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    always_exprs = cfc.extract_always_exprs(spec_text)

    if not input_streams or not output_streams or not always_exprs:
        return False, "missing input/output/always"

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        input_paths = {}
        output_paths = {}

        inputs = build_inputs(input_streams, steps=3)
        for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
            values = [str(step[name]) for step in inputs]
            path = tmpdir_path / f"{name}.in"
            path.write_text("\n".join(values) + "\n")
            input_paths[name] = path

        for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
            output_paths[name] = tmpdir_path / f"{name}.out"

        repl_script = cfc.build_repl_script(
            spec_text, input_streams, output_streams, input_paths, output_paths, always_exprs
        )
        if mode == "syntax":
            # Replace the run command with a spec_ok definition so Tau parses the formula but doesn't execute it.
            repl_lines = []
            for line in repl_script.splitlines():
                if line.strip().startswith("r "):
                    repl_lines.append(f"spec_ok() := {line.strip()[2:]}.")
                    continue
                if line.strip() == "q":
                    repl_lines.append("q")
                    break
                repl_lines.append(line)
            repl_script = "\n".join(repl_lines) + "\n"
        script_path = tmpdir_path / "smoke_repl.tau"
        script_path.write_text(repl_script)

        try:
            proc = subprocess.run(
                [str(tau_bin), "--severity", "error", "--charvar", "false"],
                input=script_path.read_text(),
                text=True,
                errors="replace",
                capture_output=True,
                cwd=ROOT,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired:
            return False, "timeout"

        if proc.returncode != 0:
            detail = (proc.stderr or proc.stdout or "unknown error").strip()
            return False, detail[:200]

    return True, ""


def main() -> int:
    tau_bin = Path(cfc.find_tau_bin())
    specs = sorted(RECOMMENDED.glob("*.tau"))
    failures = []
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=12)
    parser.add_argument("--mode", choices=["syntax", "run"], default="syntax")
    args = parser.parse_args()

    subset = specs[args.start:]
    if args.count:
        subset = subset[: args.count]

    for idx, spec in enumerate(subset, start=args.start):
        print(f"[{idx + 1}/{len(specs)}] {spec.name}")
        ok, detail = smoke_spec(tau_bin, spec, timeout_s=args.timeout, mode=args.mode)
        if not ok:
            failures.append((spec, detail))

    print(f"Specs checked: {len(specs)}")
    if failures:
        print(f"Failures: {len(failures)}")
        for spec, detail in failures:
            print(f"- {spec}: {detail}")
        return 1

    print("All recommended specs executed without Tau errors.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
