#!/usr/bin/env python3
"""
Tau Formal Completeness Checker - Enhanced Edition

Ensures Tau specs are formally complete state machines with:
1. Proper base case initialization for all temporal references
2. Single-line predicate definitions (no multi-line)
3. No unsupported operators (prime)
4. Deterministic behavior at all timesteps
5. Truth table generation for verification
6. Auto-fix suggestions for common issues

Usage:
    python check_formal_completeness.py                    # Full check
    python check_formal_completeness.py --lint-only        # Lint only
    python check_formal_completeness.py --fix              # Show fix suggestions
    python check_formal_completeness.py --truth-table FILE # Generate truth table
    python check_formal_completeness.py --analyze FILE     # Deep analysis of single spec
"""
import argparse
import itertools
import json
import os
import re
import shutil
import tempfile
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple


ROOT = Path(__file__).resolve().parents[2]


@dataclass
class StateMachineAnalysis:
    """Complete state machine analysis for a Tau spec."""
    path: str
    inputs: List[str] = field(default_factory=list)
    outputs: List[str] = field(default_factory=list)
    predicates: Dict[str, str] = field(default_factory=dict)
    temporal_refs: Dict[str, int] = field(default_factory=dict)  # var -> max depth
    base_cases: Dict[str, Set[int]] = field(default_factory=dict)  # output -> set of initialized steps
    max_temporal_depth: int = 0
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    fix_suggestions: List[str] = field(default_factory=list)
    is_complete: bool = False


def find_tau_bin() -> str:
    candidates = [
        ROOT / "external" / "tau-nightly" / "usr" / "bin" / "tau",
        ROOT / "external" / "tau-lang" / "build-Release" / "tau",
        ROOT / "external" / "tau-lang" / "build-Debug" / "tau",
    ]
    for candidate in candidates:
        if candidate.exists() and os.access(candidate, os.X_OK):
            return str(candidate)
    tau = shutil.which("tau")
    if tau:
        return tau
    raise FileNotFoundError("Tau compiler not found. Build it at external/tau-lang/build-Release/tau")


def iter_tau_files(roots, exclude_dirs, exclude_suffixes, exclude_prefixes):
    for root in roots:
        base = (ROOT / root).resolve()
        if not base.exists():
            continue
        for path in base.rglob("*.tau"):
            if any(part in exclude_dirs for part in path.parts):
                continue
            if any(path.name.startswith(prefix) for prefix in exclude_prefixes):
                continue
            if any(path.name.endswith(suffix) for suffix in exclude_suffixes):
                continue
            yield path


def analyze_spec_deep(path: Path) -> StateMachineAnalysis:
    """Deep analysis of a Tau spec for state machine completeness."""
    text = path.read_text()
    lines = text.splitlines()
    analysis = StateMachineAnalysis(path=str(path.relative_to(ROOT)))
    
    scan_text = "\n".join(line for line in lines if not line.lstrip().startswith("#"))
    
    # Extract inputs and outputs
    analysis.inputs = sorted(set(re.findall(r'\b(i\d+)\[', scan_text)))
    analysis.outputs = sorted(set(re.findall(r'\b(o\d+)\[', scan_text)))
    
    # Extract predicates
    for line in lines:
        if line.lstrip().startswith("#"):
            continue
        match = re.match(r'\s*(\w+)\s*\([^)]+\)\s*:=', line)
        if match:
            pred_name = match.group(1)
            analysis.predicates[pred_name] = line.strip()
    
    # Extract temporal references with their depths
    for match in re.finditer(r'\b([io]\d+)\[t-(\d+)\]', scan_text):
        var = match.group(1)
        depth = int(match.group(2))
        if var not in analysis.temporal_refs:
            analysis.temporal_refs[var] = depth
        else:
            analysis.temporal_refs[var] = max(analysis.temporal_refs[var], depth)
        analysis.max_temporal_depth = max(analysis.max_temporal_depth, depth)
    
    # Extract base case initializations
    for match in re.finditer(r'\b(o\d+)\[(\d+)\]', scan_text):
        out = match.group(1)
        step = int(match.group(2))
        if out not in analysis.base_cases:
            analysis.base_cases[out] = set()
        analysis.base_cases[out].add(step)
    
    # Check completeness and generate fix suggestions
    _check_state_machine_completeness(analysis, lines)
    
    return analysis


def _check_state_machine_completeness(analysis: StateMachineAnalysis, lines: List[str]) -> None:
    """Check if the state machine is formally complete and generate fixes."""
    non_comment_lines = [(i, line_text) for i, line_text in enumerate(lines, 1) if not line_text.lstrip().startswith("#")]
    
    # Check 1: Must have 'always' constraint
    if not any("always" in line for _, line in non_comment_lines):
        analysis.errors.append("CRITICAL: Missing 'always' constraint - not a valid state machine")
        analysis.fix_suggestions.append("Add: always (... your constraints ...)")
    
    # Check 2: Single-line predicates
    for idx, line in non_comment_lines:
        if ":=" in line and not line.rstrip().endswith("."):
            analysis.errors.append(f"Multi-line predicate at line {idx} - Tau requires single-line")
            analysis.fix_suggestions.append(f"Line {idx}: Combine predicate into single line ending with '.'")
    
    # Check 3: No prime operator
    for idx, line in non_comment_lines:
        if re.search(r"[a-z]\d*'", line):
            analysis.errors.append(f"Prime operator at line {idx} - not supported in spec mode")
    
    # Check 4: Ternary in predicates (warning)
    for idx, line in non_comment_lines:
        if ":=" in line and "?" in line:
            analysis.warnings.append(f"Ternary in predicate at line {idx} - may fail, use boolean expansion")
            # Generate fix suggestion
            pred_match = re.match(r'\s*(\w+)\s*\(([^)]+)\)\s*:=\s*(.+)\.', line)
            if pred_match:
                name, params, body = pred_match.groups()
                analysis.fix_suggestions.append(
                    f"Rewrite ternary: {name}(...) := (cond && then_branch) || (!cond && else_branch)."
                )
    
    # Check 5: Base case completeness for all outputs
    if analysis.max_temporal_depth > 0:
        for out in analysis.outputs:
            initialized = analysis.base_cases.get(out, set())
            missing = [t for t in range(analysis.max_temporal_depth) if t not in initialized]
            if missing:
                analysis.errors.append(
                    f"Output {out} missing base cases for t={missing} (temporal depth {analysis.max_temporal_depth})"
                )
                # Generate specific fix
                for t in missing:
                    analysis.fix_suggestions.append(
                        f"Add to always: ({out}[{t}]:sbf = 0:sbf) &&"
                    )
    
    # Check 6: Temporal input dependencies warning
    input_temporal = [v for v in analysis.temporal_refs if v.startswith('i')]
    if input_temporal:
        analysis.warnings.append(
            f"Temporal inputs {input_temporal} require {analysis.max_temporal_depth} warmup steps"
        )
    
    # Determine overall completeness
    analysis.is_complete = len(analysis.errors) == 0


def lint_spec(path: Path):
    """Lint a spec for formal completeness (backward compatible)."""
    analysis = analyze_spec_deep(path)
    return {
        "path": analysis.path,
        "errors": analysis.errors,
        "warnings": analysis.warnings,
        "max_backref": analysis.max_temporal_depth,
        "analysis": analysis,
    }


def generate_fix_code(analysis: StateMachineAnalysis) -> str:
    """Generate corrected base case code for a spec."""
    if analysis.is_complete:
        return "# Spec is already complete - no fixes needed"
    
    lines = ["# AUTO-GENERATED BASE CASE FIXES", "# Add these constraints to your always statement:", ""]
    
    for out in sorted(analysis.outputs):
        initialized = analysis.base_cases.get(out, set())
        for t in range(analysis.max_temporal_depth):
            if t not in initialized:
                lines.append(f"({out}[{t}]:sbf = 0:sbf) &&")
    
    lines.append("")
    lines.append("# Then your existing temporal constraints for t >= " + str(analysis.max_temporal_depth))
    return "\n".join(lines)


def generate_truth_table(tau_bin: str, spec_path: Path, inputs: List[Dict], 
                         timeout: int = 15) -> Tuple[str, List[Dict]]:
    """Generate a truth table by running the spec with given inputs."""
    analysis = analyze_spec_deep(spec_path)
    
    if not analysis.inputs or not analysis.outputs:
        return "Error: Could not detect inputs/outputs", []
    
    # Build input string
    input_lines = []
    for step_inputs in inputs:
        for inp in sorted(analysis.inputs):
            if inp in step_inputs:
                input_lines.append(str(step_inputs[inp]))
    input_lines.append("q")
    
    # Run Tau
    try:
        result = subprocess.run(
            [tau_bin, str(spec_path), "--charvar", "false", "-x"],
            input="\n".join(input_lines),
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout,
            cwd=ROOT,
        )
    except subprocess.TimeoutExpired:
        return "Error: Tau execution timed out", []
    
    # Parse outputs
    outputs_by_step = {}
    for line in result.stdout.split("\n"):
        for match in re.finditer(r'(o\d+)\[(\d+)\]:\w+\s*:=\s*(\d+)', line):
            out, step, val = match.group(1), int(match.group(2)), int(match.group(3))
            if step not in outputs_by_step:
                outputs_by_step[step] = {}
            outputs_by_step[step][out] = val
    
    # Build markdown table
    all_inputs = sorted(analysis.inputs)
    all_outputs = sorted(analysis.outputs)
    
    header = "| Step |" + "".join(f" {i} |" for i in all_inputs) + "".join(f" {o} |" for o in all_outputs)
    sep = "|------|" + "------|" * (len(all_inputs) + len(all_outputs))
    
    rows = [header, sep]
    for step in sorted(outputs_by_step.keys()):
        row = f"| {step} |"
        step_in = inputs[step] if step < len(inputs) else {}
        for inp in all_inputs:
            row += f" {step_in.get(inp, '-')} |"
        for out in all_outputs:
            row += f" {outputs_by_step[step].get(out, '-')} |"
        rows.append(row)
    
    return "\n".join(rows), list(outputs_by_step.values())


def print_analysis_report(analysis: StateMachineAnalysis, verbose: bool = False) -> None:
    """Print a detailed analysis report."""
    status = "✅ COMPLETE" if analysis.is_complete else "❌ INCOMPLETE"
    
    print("=" * 70)
    print(f"State Machine Analysis: {analysis.path}")
    print("=" * 70)
    print(f"Status: {status}")
    print(f"Temporal Depth: {analysis.max_temporal_depth}")
    print(f"Inputs: {', '.join(analysis.inputs) or 'none'}")
    print(f"Outputs: {', '.join(analysis.outputs) or 'none'}")
    print()
    
    if analysis.predicates and verbose:
        print("Predicates:")
        for name in sorted(analysis.predicates.keys()):
            print(f"  - {name}")
        print()
    
    if analysis.temporal_refs:
        print("Temporal References:")
        for var, depth in sorted(analysis.temporal_refs.items()):
            print(f"  - {var}[t-{depth}]")
        print()
    
    if analysis.base_cases:
        print("Base Cases Found:")
        for out, steps in sorted(analysis.base_cases.items()):
            print(f"  - {out}: steps {sorted(steps)}")
        print()
    
    if analysis.errors:
        print("❌ ERRORS:")
        for err in analysis.errors:
            print(f"  - {err}")
        print()
    
    if analysis.warnings:
        print("⚠️  WARNINGS:")
        for warn in analysis.warnings:
            print(f"  - {warn}")
        print()
    
    if analysis.fix_suggestions:
        print("🔧 FIX SUGGESTIONS:")
        for fix in analysis.fix_suggestions:
            print(f"  {fix}")
        print()


def load_registry(registry_path: Path) -> Dict[str, Dict]:
    if not registry_path.exists():
        return {}
    data = json.loads(registry_path.read_text())
    specs = data.get("specs", [])
    by_path = {}
    for entry in specs:
        path = entry.get("path")
        if path:
            by_path[path] = entry
    return by_path


def extract_ltl_claims(spec_text: str) -> List[str]:
    claims = []
    for line in spec_text.splitlines():
        match = re.match(r"\s*#\s*LTL\s*:\s*([A-Za-z0-9_-]+)", line)
        if match:
            claims.append(match.group(1))
    return claims


def safe_eval(expr: str, context: Dict[str, object]) -> object:
    allowed = {
        "abs": abs,
        "min": min,
        "max": max,
        "sorted": sorted,
        "True": True,
        "False": False,
        "None": None,
    }
    return eval(expr, {"__builtins__": {}}, {**allowed, **context})


def build_enumeration_inputs(entry: Dict, input_names: List[str], default_max_cases: int = 512):
    enumeration = entry.get("enumeration")
    if not enumeration:
        return None, "missing enumeration for INV1"

    values = []
    for name in input_names:
        if name not in enumeration:
            return None, f"missing enumeration for input {name}"
        vals = enumeration[name]
        if not isinstance(vals, list) or not vals:
            return None, f"enumeration for {name} must be a non-empty list"
        values.append(vals)

    max_cases = entry.get("max_cases", default_max_cases)
    total = 1
    for vals in values:
        total *= len(vals)
    if total > max_cases:
        return None, f"enumeration has {total} cases (max {max_cases})"

    combos = []
    for combo in itertools.product(*values):
        combos.append(dict(zip(input_names, combo)))
    return combos, None


def build_eval_context(step_idx: int, inputs: List[Dict], outputs_by_step: Dict[int, Dict]) -> Dict[str, object]:
    context = {"t": step_idx}
    step_inputs = inputs[step_idx] if step_idx < len(inputs) else {}
    step_outputs = outputs_by_step.get(step_idx, {})
    for key, value in step_inputs.items():
        context[key] = value
    for key, value in step_outputs.items():
        context[key] = value

    if step_idx > 0:
        prev_inputs = inputs[step_idx - 1] if step_idx - 1 < len(inputs) else {}
        prev_outputs = outputs_by_step.get(step_idx - 1, {})
    else:
        prev_inputs = {}
        prev_outputs = {}
    for key in step_inputs.keys():
        context[f"prev_{key}"] = prev_inputs.get(key)
    for key in step_outputs.keys():
        context[f"prev_{key}"] = prev_outputs.get(key)
    return context


def run_syntax_checks(tau_bin: str, spec_paths: List[Path], timeout: int = 1) -> List[str]:
    failures = []
    for path in spec_paths:
        try:
            proc = subprocess.run(
                [tau_bin, str(path), "--severity", "error", "--charvar", "false", "-x"],
                input="",
                text=True,
                errors="replace",
                capture_output=True,
                cwd=ROOT,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            failures.append(f"{path.relative_to(ROOT)}: syntax check timed out")
            continue

        output = (proc.stdout or "") + (proc.stderr or "")
        if proc.returncode != 0 or "(Error)" in output:
            first_lines = "\n".join(output.strip().splitlines()[:5]).strip()
            detail = first_lines or "syntax check failed"
            failures.append(f"{path.relative_to(ROOT)}: {detail}")
    return failures


def run_invariant_checks(spec_paths: List[Path], analysis_by_path: Dict[str, StateMachineAnalysis],
                         registry_by_path: Dict[str, Dict], tau_bin: str, allow_unverified: bool) -> Tuple[List[str], List[str], List[str]]:
    inv_failures = []
    inv_warnings = []
    counterexamples = []

    for path in spec_paths:
        rel_path = str(path.relative_to(ROOT))
        analysis = analysis_by_path.get(rel_path) or analyze_spec_deep(path)
        entry = registry_by_path.get(rel_path)
        spec_text = path.read_text()
        ltl_claims = extract_ltl_claims(spec_text)

        if not entry:
            message = f"{rel_path}: missing registry entry for INV1/INV2"
            if allow_unverified:
                inv_warnings.append(message)
            else:
                inv_failures.append(message)
            continue
        mode = entry.get("mode", "repl")
        if mode == "skip":
            reason = entry.get("skip_reason", "no reason provided")
            inv_warnings.append(f"{rel_path}: invariants skipped ({reason})")
            continue

        if analysis.max_temporal_depth > 0 and entry.get("oracle") and mode == "repl":
            inv_failures.append(f"{rel_path}: temporal oracle verification not supported in REPL")
            continue

        stream_indices = None
        if mode == "spec":
            stream_indices = sorted(
                {int(m.group(1)) for m in re.finditer(r"\bi(\d+)\[", spec_text)}
            )

        oracle = entry.get("oracle")
        if oracle:
            input_names = sorted(analysis.inputs, key=lambda s: int(s[1:]))
            combos, error = build_enumeration_inputs(entry, input_names)
            if error:
                inv_failures.append(f"{rel_path}: {error}")
            else:
                if mode == "spec":
                    outputs_by_step, trace_errors = run_tau_spec_trace(
                        tau_bin, path, combos, stream_indices, timeout=entry.get("spec_timeout", 2)
                    )
                else:
                    outputs_by_step, trace_errors = run_tau_repl_trace(
                        tau_bin, path, combos, [{}] * len(combos)
                    )
                if trace_errors:
                    for err in trace_errors:
                        inv_failures.append(f"{rel_path}: {err}")
                else:
                    for idx, step_inputs in enumerate(combos):
                        context = dict(step_inputs)
                        try:
                            expected_outputs = {}
                            if oracle.get("type") != "python":
                                inv_failures.append(f"{rel_path}: unsupported oracle type {oracle.get('type')}")
                                break
                            for out_name, expr in oracle.get("outputs", {}).items():
                                value = safe_eval(expr, context)
                                if isinstance(value, bool):
                                    value = 1 if value else 0
                                expected_outputs[out_name] = int(value)
                        except Exception as exc:
                            inv_failures.append(f"{rel_path}: oracle evaluation error: {exc}")
                            break

                        got_outputs = outputs_by_step.get(idx, {})
                        for out_name, exp_val in expected_outputs.items():
                            got_val = got_outputs.get(out_name)
                            if got_val is None:
                                inv_failures.append(f"{rel_path}: missing {out_name} at step {idx}")
                                counterexamples.append(
                                    f"{rel_path} INV1 counterexample: step {idx} inputs={step_inputs}"
                                )
                                break
                            if got_val != exp_val:
                                inv_failures.append(f"{rel_path}: INV1 mismatch at step {idx} ({out_name})")
                                counterexamples.append(
                                    f"{rel_path} INV1 counterexample: step {idx} inputs={step_inputs} expected={expected_outputs} got={got_outputs}"
                                )
                                break
                        if inv_failures and "INV1 mismatch" in inv_failures[-1]:
                            break
        else:
            message = f"{rel_path}: missing oracle definition (INV1)"
            if allow_unverified:
                inv_warnings.append(message)
            else:
                inv_failures.append(message)

        if ltl_claims:
            ltl_defs = entry.get("ltl", [])
            ltl_map = {claim.get("id"): claim.get("expr") for claim in ltl_defs}
            missing = [claim for claim in ltl_claims if claim not in ltl_map]
            if missing:
                inv_failures.append(f"{rel_path}: missing LTL verification for {missing}")
            else:
                input_names = sorted(analysis.inputs, key=lambda s: int(s[1:]))
                combos, error = build_enumeration_inputs(entry, input_names)
                if error:
                    inv_failures.append(f"{rel_path}: {error}")
                else:
                    if mode == "spec":
                        outputs_by_step, trace_errors = run_tau_spec_trace(
                            tau_bin, path, combos, stream_indices, timeout=entry.get("spec_timeout", 2)
                        )
                    else:
                        outputs_by_step, trace_errors = run_tau_repl_trace(
                            tau_bin, path, combos, [{}] * len(combos)
                        )
                    if trace_errors:
                        for err in trace_errors:
                            inv_failures.append(f"{rel_path}: {err}")
                    else:
                        for idx in range(len(combos)):
                            context = build_eval_context(idx, combos, outputs_by_step)
                            for claim_id in ltl_claims:
                                expr = ltl_map.get(claim_id)
                                if expr is None:
                                    continue
                                try:
                                    result = safe_eval(expr, context)
                                except Exception as exc:
                                    inv_failures.append(f"{rel_path}: LTL {claim_id} eval error: {exc}")
                                    counterexamples.append(
                                        f"{rel_path} LTL counterexample: step {idx} inputs={combos[idx]}"
                                    )
                                    break
                                if not bool(result):
                                    inv_failures.append(f"{rel_path}: LTL {claim_id} failed at step {idx}")
                                    counterexamples.append(
                                        f"{rel_path} LTL counterexample: step {idx} inputs={combos[idx]} outputs={outputs_by_step.get(idx, {})}"
                                    )
                                    break
                            if inv_failures and "LTL" in inv_failures[-1]:
                                break

    return inv_failures, inv_warnings, counterexamples


def run_trace_tests(tau_bin: str, registry_path: Path):
    data = json.loads(registry_path.read_text())
    specs = data.get("specs", [])
    failures = []
    skipped = []

    for spec in specs:
        mode = spec.get("mode", "repl")
        if mode == "skip":
            reason = spec.get("skip_reason", "no reason provided")
            skipped.append(f"{spec['id']}: {reason}")
            continue
        spec_path = ROOT / spec["path"]
        inputs = spec["inputs"]
        expected = spec["expected"]
        if len(inputs) != len(expected):
            failures.append(
                f"{spec['id']}: inputs length {len(inputs)} != expected length {len(expected)}"
            )
            continue

        stream_indices = sorted(
            {int(m.group(1)) for m in re.finditer(r"\bi(\d+)\[", spec_path.read_text())}
        )
        if not stream_indices:
            failures.append(f"{spec['id']}: no input streams detected")
            continue

        for step, step_inputs in enumerate(inputs):
            for idx in stream_indices:
                key = f"i{idx}"
                if key not in step_inputs:
                    failures.append(f"{spec['id']}: missing {key} for step {step}")
                    break
        if failures:
            continue

        if mode == "spec":
            output, trace_errors = run_tau_spec_trace(
                tau_bin, spec_path, inputs, stream_indices, timeout=spec.get("spec_timeout", 2)
            )
        else:
            output, trace_errors = run_tau_repl_trace(
                tau_bin, spec_path, inputs, expected
            )
        if trace_errors:
            failures.extend([f"{spec['id']}: {err}" for err in trace_errors])
            continue

        for step, exp in enumerate(expected):
            got = output.get(step, {})
            for key, exp_val in exp.items():
                if exp_val is None:
                    continue
                if key not in got:
                    failures.append(f"{spec['id']}: missing {key} at step {step}")
                    continue
                if got[key] != exp_val:
                    failures.append(
                        f"{spec['id']}: {key} step {step} expected {exp_val} got {got[key]}"
                    )

    if skipped:
        print("Trace tests skipped:")
        for entry in skipped:
            print(f"- {entry}")
    return failures


def run_tau_repl_trace(tau_bin, spec_path, inputs, expected):
    failures = []
    spec_text = spec_path.read_text()
    spec_text = rewrite_ternaries(spec_text)
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}

    if not input_streams:
        return {}, ["no input streams detected for REPL trace"]
    if not output_streams:
        return {}, ["no output streams detected for REPL trace"]

    always_exprs = extract_always_exprs(spec_text)
    if not always_exprs:
        return {}, ["missing always constraint for REPL trace"]

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        input_paths = {}
        output_paths = {}

        for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
            values = [str(step[name]) for step in inputs]
            path = tmpdir_path / f"{name}.in"
            path.write_text("\n".join(values) + "\n")
            input_paths[name] = path

        for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
            path = tmpdir_path / f"{name}.out"
            output_paths[name] = path

        repl_script = build_repl_script(
            spec_text, input_streams, output_streams, input_paths, output_paths, always_exprs
        )
        script_path = tmpdir_path / "trace_repl.tau"
        script_path.write_text(repl_script)

        proc = subprocess.run(
            [tau_bin, "--severity", "error", "--charvar", "false"],
            input=script_path.read_text(),
            text=True,
            errors="replace",
            capture_output=True,
            cwd=ROOT,
        )
        if proc.returncode != 0:
            stderr = proc.stderr.strip()
            stdout = proc.stdout.strip()
            detail = stderr or stdout or "unknown error"
            return {}, [f"tau REPL failed: {detail}"]

        outputs_by_step = {}
        for name, path in output_paths.items():
            if not path.exists():
                failures.append(f"missing output file {name}")
                continue
            values = [line.strip() for line in path.read_text().splitlines() if line.strip()]
            for idx, raw in enumerate(values):
                try:
                    value = int(raw)
                except ValueError:
                    failures.append(f"{name} output non-integer value: {raw}")
                    continue
                outputs_by_step.setdefault(idx, {})[name] = value

    return outputs_by_step, failures


def run_tau_spec_trace(tau_bin, spec_path, inputs, stream_indices, timeout=2):
    failures = []
    input_lines = []
    for step_inputs in inputs:
        for idx in stream_indices:
            key = f"i{idx}"
            if key not in step_inputs:
                failures.append(f"missing {key} in spec-mode inputs")
                return {}, failures
            input_lines.append(str(step_inputs[key]))

    command = ["timeout", str(timeout), tau_bin, str(spec_path), "--severity", "error", "--charvar", "false", "-x"]
    proc = subprocess.run(
        command,
        input="\n".join(input_lines) + "\n",
        text=True,
        errors="replace",
        capture_output=True,
        cwd=ROOT,
    )

    output_text = (proc.stdout or "") + (proc.stderr or "")
    outputs_by_step = {}
    for line in output_text.splitlines():
        for match in re.finditer(r"\bo(\d+)\[(\d+)\]:\w+\s*:=\s*(\d+)", line):
            out_idx = int(match.group(1))
            step = int(match.group(2))
            value = int(match.group(3))
            outputs_by_step.setdefault(step, {})[f"o{out_idx}"] = value

    return outputs_by_step, failures


def extract_stream_types(spec_text):
    stream_types = {}
    for match in re.finditer(r"\b([io]\d+)\[[^\]]+\]:([a-zA-Z]+\[\d+\]|[a-zA-Z]+)", spec_text):
        name = match.group(1)
        if name not in stream_types:
            stream_types[name] = match.group(2)
    return stream_types


def extract_always_exprs(spec_text):
    exprs = []
    for line in spec_text.splitlines():
        if line.lstrip().startswith("#"):
            continue
        if "always" in line:
            match = re.search(r"always\s*(.*)\.\s*$", line.strip())
            if match:
                exprs.append(match.group(1))
    return exprs


def build_repl_script(spec_text, input_streams, output_streams, input_paths, output_paths, always_exprs):
    lines = []
    lines.append("# Auto-generated REPL harness for trace testing")
    lines.append("")

    for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
        lines.append(f"{name} : {input_streams[name]} = in file(\"{input_paths[name]}\")")

    lines.append("")
    for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
        lines.append(f"{name} : {output_streams[name]} = out file(\"{output_paths[name]}\")")

    lines.append("")
    for line in spec_text.splitlines():
        if line.lstrip().startswith("#"):
            continue
        if "always" in line:
            continue
        if line.strip():
            lines.append(line)

    expr = " && ".join(f"({expr})" for expr in always_exprs)
    lines.append("")
    lines.append(f"r {expr}")
    lines.append("q")
    lines.append("")
    return "\n".join(lines)


def rewrite_ternaries(spec_text):
    lines = []
    for line in spec_text.splitlines():
        if line.lstrip().startswith("#") or ":=" not in line or "?" not in line:
            lines.append(line)
            continue
        prefix, expr = line.split(":=", 1)
        expr = expr.strip()
        if expr.endswith("."):
            expr = expr[:-1].strip()
            rewritten = expand_ternary_expr(expr)
            lines.append(f"{prefix}:= {rewritten}.")
        else:
            lines.append(line)
    return "\n".join(lines)


def expand_ternary_expr(expr):
    parts = split_ternary(expr)
    if not parts:
        return expr.strip()
    cond, then_branch, else_branch = parts
    cond = cond.strip()
    then_branch = expand_ternary_expr(then_branch.strip())
    else_branch = expand_ternary_expr(else_branch.strip())
    return f"(({cond}) && ({then_branch})) || (!({cond}) && ({else_branch}))"


def split_ternary(expr):
    depth = 0
    qmark = None
    for i, ch in enumerate(expr):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "?" and depth == 0:
            qmark = i
            break
    if qmark is None:
        return None
    depth = 0
    colon = None
    for j in range(qmark + 1, len(expr)):
        ch = expr[j]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == ":" and depth == 0:
            colon = j
            break
    if colon is None:
        return None
    return expr[:qmark], expr[qmark + 1:colon], expr[colon + 1:]


def main():
    parser = argparse.ArgumentParser(
        description="Tau Formal Completeness Checker - Ensures specs are complete state machines.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                              # Full lint + trace check
  %(prog)s --lint-only                  # Lint only, no trace tests
  %(prog)s --analyze FILE.tau           # Deep analysis of single spec
  %(prog)s --fix FILE.tau               # Show fix suggestions for spec
  %(prog)s --summary                    # Show summary with completeness stats
  %(prog)s --strict                     # Treat warnings as errors
        """
    )
    parser.add_argument(
        "--roots",
        nargs="*",
        default=["experiments", "src/tau_specs"],
        help="Roots to scan for .tau specs.",
    )
    parser.add_argument(
        "--registry",
        default="tests/tau/spec_registry.json",
        help="Registry file with trace tests.",
    )
    parser.add_argument("--lint-only", action="store_true", help="Run lint only.")
    parser.add_argument("--trace-only", action="store_true", help="Run trace tests only.")
    parser.add_argument("--analyze", metavar="FILE", help="Deep analysis of a single spec file.")
    parser.add_argument("--fix", metavar="FILE", help="Show fix suggestions for a spec file.")
    parser.add_argument("--summary", action="store_true", help="Show completeness summary.")
    parser.add_argument("--strict", action="store_true", help="Treat warnings as errors.")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output.")
    parser.add_argument("--no-syntax", action="store_true", help="Skip Tau syntax verification.")
    parser.add_argument(
        "--allow-unverified",
        action="store_true",
        help="Treat missing oracle/registry entries as warnings instead of failures.",
    )
    parser.add_argument(
        "--syntax-timeout",
        type=int,
        default=1,
        help="Per-spec syntax check timeout in seconds (default: 1).",
    )
    args = parser.parse_args()

    # Single file analysis mode
    if args.analyze:
        spec_path = ROOT / args.analyze if not Path(args.analyze).is_absolute() else Path(args.analyze)
        if not spec_path.exists():
            print(f"Error: File not found: {spec_path}")
            return 1
        analysis = analyze_spec_deep(spec_path)
        print_analysis_report(analysis, verbose=args.verbose)
        if not analysis.is_complete:
            print("\n" + generate_fix_code(analysis))
        return 0 if analysis.is_complete else 1

    # Fix suggestions mode
    if args.fix:
        spec_path = ROOT / args.fix if not Path(args.fix).is_absolute() else Path(args.fix)
        if not spec_path.exists():
            print(f"Error: File not found: {spec_path}")
            return 1
        analysis = analyze_spec_deep(spec_path)
        if analysis.is_complete:
            print(f"✅ {spec_path.name} is already formally complete!")
        else:
            print(f"❌ {spec_path.name} needs fixes:\n")
            print(generate_fix_code(analysis))
        return 0 if analysis.is_complete else 1

    exclude_dirs = {"external", ".git", "io"}
    exclude_suffixes = {"_io.tau"}
    exclude_prefixes = {"tmp_"}

    lint_results = []
    spec_paths = []
    analysis_by_path = {}
    if not args.trace_only:
        roots = args.roots
        lint_results = [
            lint_spec(path)
            for path in iter_tau_files(roots, exclude_dirs, exclude_suffixes, exclude_prefixes)
        ]
        spec_paths = [ROOT / result["path"] for result in lint_results]
        analysis_by_path = {
            result["path"]: result["analysis"]
            for result in lint_results
            if result.get("analysis")
        }
    else:
        roots = args.roots
        spec_paths = list(iter_tau_files(roots, exclude_dirs, exclude_suffixes, exclude_prefixes))

    lint_errors = [r for r in lint_results if r["errors"]]
    lint_warnings = [r for r in lint_results if r["warnings"]]
    complete_specs = [r for r in lint_results if r.get("analysis") and r["analysis"].is_complete]

    syntax_failures = []
    inv_failures = []
    inv_warnings = []
    inv_counterexamples = []

    if lint_results:
        if args.summary:
            # Enhanced summary view
            print("=" * 70)
            print("FORMAL COMPLETENESS SUMMARY")
            print("=" * 70)
            print(f"  Total specs:     {len(lint_results)}")
            print(f"  ✅ Complete:     {len(complete_specs)}")
            print(f"  ❌ With errors:  {len(lint_errors)}")
            print(f"  ⚠️  With warnings: {len(lint_warnings)}")
            if syntax_failures:
                print(f"  ❌ Syntax errors: {len(syntax_failures)}")
            if inv_failures:
                print(f"  ❌ INV failures:  {len(inv_failures)}")
            if inv_warnings:
                print(f"  ⚠️  INV warnings: {len(inv_warnings)}")
            print()
            
            if complete_specs:
                print("Complete state machines:")
                for r in complete_specs:
                    print(f"  ✅ {r['path']}")
                print()
            
            if lint_errors:
                print("Incomplete (need fixes):")
                for r in lint_errors:
                    print(f"  ❌ {r['path']}: {len(r['errors'])} errors")
                print()
        else:
            # Standard output
            print("Lint summary:")
            print(f"  Specs checked: {len(lint_results)}")
            print(f"  Complete: {len(complete_specs)}")
            print(f"  Errors: {len(lint_errors)}")
            print(f"  Warnings: {len(lint_warnings)}")
            
            for result in lint_results:
                if result["errors"] or result["warnings"]:
                    print(f"- {result['path']}")
                    for err in result["errors"]:
                        print(f"  ERROR: {err}")
                    for warn in result["warnings"]:
                        print(f"  WARN: {warn}")

    trace_failures = []
    registry_path = ROOT / args.registry
    registry_by_path = load_registry(registry_path)

    if not args.lint_only:
        try:
            tau_bin = find_tau_bin()
        except FileNotFoundError as exc:
            syntax_failures.append(str(exc))
            tau_bin = None

        if tau_bin and not args.no_syntax:
            syntax_failures = run_syntax_checks(tau_bin, spec_paths, timeout=args.syntax_timeout)

        if tau_bin:
            inv_failures, inv_warnings, inv_counterexamples = run_invariant_checks(
                spec_paths, analysis_by_path, registry_by_path, tau_bin, args.allow_unverified
            )

        if registry_path.exists() and tau_bin:
            trace_failures = run_trace_tests(tau_bin, registry_path)
        else:
            if not args.summary:
                trace_failures.append(f"registry not found: {registry_path}")

    if syntax_failures:
        print("Syntax failures:")
        for failure in syntax_failures:
            print(f"- {failure}")

    if inv_failures or inv_warnings:
        print("Invariant checks:")
        for failure in inv_failures:
            print(f"- FAIL: {failure}")
        for warning in inv_warnings:
            print(f"- WARN: {warning}")
        for example in inv_counterexamples:
            print(f"- COUNTEREXAMPLE: {example}")

    if trace_failures:
        print("Trace test failures:")
        for failure in trace_failures:
            print(f"- {failure}")

    # Determine exit code
    has_errors = bool(lint_errors) or bool(trace_failures) or bool(syntax_failures) or bool(inv_failures)
    has_warnings = (bool(lint_warnings) or bool(inv_warnings)) and args.strict
    
    if has_errors or has_warnings:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
