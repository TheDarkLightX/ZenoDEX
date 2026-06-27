"""
Tau spec assurance helpers.

Bounded exhaustive checking for Tau specs against explicit output contracts and
property probes. This is an imperative-shell analysis tool: the goal is to
detect semantic drift, typos, and overclaimed outputs in Tau policies.
"""

from __future__ import annotations

import ast
import itertools
import json
import os
import re
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence, cast

from .tau_runner import (
    build_repl_script,
    extract_always_exprs,
    extract_stream_types,
    normalize_spec_text,
    parse_definitions,
    inline_definitions,
)


ROOT = Path(__file__).resolve().parents[2]


class BV:
    def __init__(self, width: int, value: int) -> None:
        if width <= 0:
            raise ValueError("bitvector width must be positive")
        self.width = int(width)
        self.mask = (1 << self.width) - 1
        self.value = int(value) & self.mask

    def _coerce(self, other: object) -> int:
        if isinstance(other, BV):
            if other.width != self.width:
                raise ValueError(f"bitvector width mismatch: {self.width} != {other.width}")
            return other.value
        if isinstance(other, int) and not isinstance(other, bool):
            return int(other) & self.mask
        raise TypeError(f"unsupported operand type for BV[{self.width}]: {type(other)!r}")

    def __add__(self, other: object) -> "BV":
        return BV(self.width, self.value + self._coerce(other))

    def __sub__(self, other: object) -> "BV":
        return BV(self.width, self.value - self._coerce(other))

    def __mul__(self, other: object) -> "BV":
        return BV(self.width, self.value * self._coerce(other))

    def __lt__(self, other: object) -> bool:
        return self.value < self._coerce(other)

    def __le__(self, other: object) -> bool:
        return self.value <= self._coerce(other)

    def __gt__(self, other: object) -> bool:
        return self.value > self._coerce(other)

    def __ge__(self, other: object) -> bool:
        return self.value >= self._coerce(other)

    def __eq__(self, other: object) -> bool:
        try:
            return self.value == self._coerce(other)
        except Exception:
            return False

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

    def __bool__(self) -> bool:
        return bool(self.value)

    def __repr__(self) -> str:
        return f"BV({self.width}, {self.value})"


def safe_eval(expr: str, context: Mapping[str, object]) -> object:
    env = {
        "abs": abs,
        "int": int,
        "min": min,
        "max": max,
        "sorted": sorted,
        "len": len,
        "BV": BV,
        "True": True,
        "False": False,
        "None": None,
    }
    env.update(context)
    tree = ast.parse(expr, mode="eval")
    return _SafeExpressionEvaluator(env).evaluate(tree)


class _SafeExpressionEvaluator:
    _CALLABLES = frozenset({"abs", "int", "min", "max", "sorted", "len", "BV"})

    def __init__(self, env: Mapping[str, object]) -> None:
        self._env = env

    def evaluate(self, node: ast.AST) -> object:
        if isinstance(node, ast.Expression):
            return self.evaluate(node.body)
        if isinstance(node, ast.Constant):
            if isinstance(node.value, (bool, int, str)) or node.value is None:
                return node.value
            raise ValueError(f"unsupported constant in expression: {node.value!r}")
        if isinstance(node, ast.Name):
            if node.id not in self._env:
                raise NameError(f"unknown name in expression: {node.id}")
            return self._env[node.id]
        if isinstance(node, ast.BoolOp):
            return self._eval_bool_op(node)
        if isinstance(node, ast.UnaryOp):
            return self._eval_unary_op(node)
        if isinstance(node, ast.BinOp):
            return self._eval_bin_op(node)
        if isinstance(node, ast.Compare):
            return self._eval_compare(node)
        if isinstance(node, ast.IfExp):
            return self.evaluate(node.body if bool(self.evaluate(node.test)) else node.orelse)
        if isinstance(node, ast.Call):
            return self._eval_call(node)
        if isinstance(node, ast.Subscript):
            return self._eval_subscript(node)
        if isinstance(node, ast.List):
            return [self.evaluate(item) for item in node.elts]
        if isinstance(node, ast.Tuple):
            return tuple(self.evaluate(item) for item in node.elts)
        raise ValueError(f"unsupported expression syntax: {type(node).__name__}")

    def _eval_bool_op(self, node: ast.BoolOp) -> bool:
        if isinstance(node.op, ast.And):
            for value in node.values:
                if not bool(self.evaluate(value)):
                    return False
            return True
        if isinstance(node.op, ast.Or):
            for value in node.values:
                if bool(self.evaluate(value)):
                    return True
            return False
        raise ValueError(f"unsupported boolean operator: {type(node.op).__name__}")

    def _eval_unary_op(self, node: ast.UnaryOp) -> object:
        value = self.evaluate(node.operand)
        if isinstance(node.op, ast.Not):
            return not bool(value)
        if isinstance(node.op, ast.USub):
            return -value  # type: ignore[operator]
        if isinstance(node.op, ast.UAdd):
            return +value  # type: ignore[operator]
        if isinstance(node.op, ast.Invert):
            return ~value  # type: ignore[operator]
        raise ValueError(f"unsupported unary operator: {type(node.op).__name__}")

    def _eval_bin_op(self, node: ast.BinOp) -> object:
        left = self.evaluate(node.left)
        right = self.evaluate(node.right)
        if isinstance(node.op, ast.Add):
            return left + right  # type: ignore[operator]
        if isinstance(node.op, ast.Sub):
            return left - right  # type: ignore[operator]
        if isinstance(node.op, ast.Mult):
            return left * right  # type: ignore[operator]
        if isinstance(node.op, ast.FloorDiv):
            return left // right  # type: ignore[operator]
        if isinstance(node.op, ast.Div):
            return left / right  # type: ignore[operator]
        if isinstance(node.op, ast.Mod):
            return left % right  # type: ignore[operator]
        if isinstance(node.op, ast.BitAnd):
            return left & right  # type: ignore[operator]
        if isinstance(node.op, ast.BitOr):
            return left | right  # type: ignore[operator]
        if isinstance(node.op, ast.BitXor):
            return left ^ right  # type: ignore[operator]
        if isinstance(node.op, ast.LShift):
            return left << right  # type: ignore[operator]
        if isinstance(node.op, ast.RShift):
            return left >> right  # type: ignore[operator]
        raise ValueError(f"unsupported binary operator: {type(node.op).__name__}")

    def _eval_compare(self, node: ast.Compare) -> bool:
        left = self.evaluate(node.left)
        for op, comparator in zip(node.ops, node.comparators):
            right = self.evaluate(comparator)
            if isinstance(op, ast.Eq):
                ok = left == right
            elif isinstance(op, ast.NotEq):
                ok = left != right
            elif isinstance(op, ast.Lt):
                ok = left < right  # type: ignore[operator]
            elif isinstance(op, ast.LtE):
                ok = left <= right  # type: ignore[operator]
            elif isinstance(op, ast.Gt):
                ok = left > right  # type: ignore[operator]
            elif isinstance(op, ast.GtE):
                ok = left >= right  # type: ignore[operator]
            elif isinstance(op, ast.In):
                ok = left in right  # type: ignore[operator]
            elif isinstance(op, ast.NotIn):
                ok = left not in right  # type: ignore[operator]
            else:
                raise ValueError(f"unsupported comparison operator: {type(op).__name__}")
            if not ok:
                return False
            left = right
        return True

    def _eval_call(self, node: ast.Call) -> object:
        if not isinstance(node.func, ast.Name):
            raise ValueError("only direct allowlisted function calls are supported")
        if node.func.id not in self._CALLABLES:
            raise ValueError(f"function is not allowlisted in expression: {node.func.id}")
        func = self._env.get(node.func.id)
        if not callable(func):
            raise ValueError(f"allowlisted function is unavailable in expression: {node.func.id}")
        args = [self.evaluate(arg) for arg in node.args]
        kwargs = {kw.arg: self.evaluate(kw.value) for kw in node.keywords if kw.arg is not None}
        if len(kwargs) != len(node.keywords):
            raise ValueError("starred keyword arguments are not supported")
        return func(*args, **kwargs)

    def _eval_subscript(self, node: ast.Subscript) -> object:
        value = self.evaluate(node.value)
        key = self.evaluate(node.slice)
        if not isinstance(value, (Mapping, Sequence)) or isinstance(value, (str, bytes, bytearray)):
            raise ValueError("subscript is supported only for mappings and non-string sequences")
        return value[key]  # type: ignore[index]


def _coerce_int(value: object) -> int:
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, int) and not isinstance(value, bool):
        return int(value)
    raise ValueError(f"expected bool/int result, got {value!r}")


def _coerce_str(value: object) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _entry_int(entry: Mapping[str, object], key: str, default: int) -> int:
    value = entry.get(key, default)
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, str, bytes, bytearray)):
        return int(value)
    raise ValueError(f"invalid integer field {key!r}: {value!r}")


def _entry_float(entry: Mapping[str, object], key: str, default: float) -> float:
    value = entry.get(key, default)
    if isinstance(value, bool):
        return float(int(value))
    if isinstance(value, (int, float, str, bytes, bytearray)):
        return float(value)
    raise ValueError(f"invalid float field {key!r}: {value!r}")


def _entry_property_list(entry: Mapping[str, object], key: str) -> list[Mapping[str, object]]:
    raw = entry.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list")
    result: list[Mapping[str, object]] = []
    for item in raw:
        if not isinstance(item, Mapping):
            raise ValueError(f"{key} entries must be objects")
        result.append(cast(Mapping[str, object], item))
    return result


def _strip_outer_parens(expr: str) -> str:
    current = expr.strip()
    while current.startswith("(") and current.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(current):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(current) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        current = current[1:-1].strip()
    return current


def _split_top_level_and(expr: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and expr.startswith("&&", idx):
            parts.append(expr[start:idx].strip())
            idx += 2
            start = idx
            continue
        idx += 1
    tail = expr[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _translate_tau_expr(expr: str) -> str:
    translated = expr
    translated = re.sub(
        r"\{\s*#x([0-9A-Fa-f]+)\s*\}:bv\[(\d+)\]",
        lambda m: f"BV({m.group(2)}, 0x{m.group(1)})",
        translated,
    )
    translated = re.sub(
        r"\b([A-Za-z_][A-Za-z0-9_]*)\[t\]:bv\[(\d+)\]",
        lambda m: f"BV({m.group(2)}, {m.group(1)})",
        translated,
    )
    translated = re.sub(r"\b([A-Za-z_][A-Za-z0-9_]*)\[t\]:sbf\b", lambda m: f"int({m.group(1)})", translated)
    translated = re.sub(r"\b([01]):sbf\b", lambda m: m.group(1), translated)
    translated = translated.replace("<->", " == ")
    translated = translated.replace("&&", " and ")
    translated = translated.replace("||", " or ")
    translated = re.sub(r"(?<![<>=!])=(?!=)", "==", translated)
    translated = re.sub(r"!(?!=)", " not ", translated)
    return translated


def _extract_output_equations(spec_path: Path) -> dict[str, str]:
    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    defs = parse_definitions(spec_text)
    always_exprs = extract_always_exprs(spec_text)
    if not always_exprs:
        raise ValueError(f"{spec_path}: missing always clause")
    expanded = [inline_definitions(expr, defs) for expr in always_exprs]
    equations: dict[str, str] = {}
    for expanded_expr in expanded:
        for part in _split_top_level_and(expanded_expr):
            clause = _strip_outer_parens(part)
            match = re.match(r"^(o\d+)\[t\]:sbf\s*=\s*1:sbf\s*<->\s*(.+)$", clause)
            if not match:
                continue
            equations[match.group(1)] = match.group(2).strip()
    if not equations:
        raise ValueError(f"{spec_path}: could not extract output equations")
    return equations


def _run_mirror_combinational_batch(
    *,
    spec_path: Path,
    steps: Sequence[Mapping[str, int]],
) -> dict[int, dict[str, int]]:
    equations = _extract_output_equations(spec_path)
    outputs_by_step: dict[int, dict[str, int]] = {}
    for idx, step in enumerate(steps):
        context: dict[str, object] = {name: int(value) for name, value in step.items()}
        step_outputs: dict[str, int] = {}
        for out_name in sorted(equations.keys(), key=_sort_stream_name):
            translated = _translate_tau_expr(equations[out_name])
            value = safe_eval(translated, {"BV": BV, **context, **step_outputs})
            step_outputs[out_name] = _coerce_int(value)
        outputs_by_step[idx] = step_outputs
    return outputs_by_step


def _run_tau_spec_mode_batch(
    *,
    tau_bin: str,
    spec_path: Path,
    steps: Sequence[Mapping[str, int]],
    timeout_s: float,
) -> dict[int, dict[str, int]]:
    raw_spec_text = spec_path.read_text(encoding="utf-8")
    spec_text = normalize_spec_text(raw_spec_text)
    defs = parse_definitions(spec_text)
    always_exprs = extract_always_exprs(spec_text)
    if always_exprs:
        expanded = [inline_definitions(expr, defs) for expr in always_exprs]
        kept_lines: list[str] = []
        for raw_line in spec_text.splitlines():
            stripped = raw_line.strip()
            if not stripped:
                continue
            if re.match(r"^always\b", stripped):
                continue
            if re.match(r"^[A-Za-z_][A-Za-z0-9_]*\s*\(.*\)\s*:=\s*.*\.\s*$", stripped):
                continue
            kept_lines.append(stripped)
        for expr in expanded:
            kept_lines.append(f"always {expr}.")
        spec_text = "\n".join(kept_lines) + "\n"

    input_names = sorted(set(re.findall(r"\b(i\d+)\[", spec_text)))
    output_names = sorted(set(re.findall(r"\b(o\d+)\[", spec_text)))
    if not input_names or not output_names:
        raise ValueError(f"{spec_path}: could not detect input/output streams")

    input_lines: list[str] = []
    for step in steps:
        for name in input_names:
            if name not in step:
                raise ValueError(f"{spec_path}: missing input {name}")
            input_lines.append(str(int(step[name])))

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        tmp_spec_path = tmpdir_path / spec_path.name
        tmp_spec_path.write_text(spec_text, encoding="utf-8")
        try:
            proc = subprocess.run(
                [tau_bin, str(tmp_spec_path), "--severity", "error", "--charvar", "false", "-x"],
                input="\n".join(input_lines) + "\n\n",
                text=True,
                errors="replace",
                capture_output=True,
                cwd=tmpdir_path,
                timeout=float(timeout_s),
            )
            output_text = (proc.stdout or "") + ("\n" + proc.stderr if proc.stderr else "")
        except subprocess.TimeoutExpired as exc:
            stdout_text = _coerce_str(exc.stdout or "")
            stderr_text = _coerce_str(exc.stderr or "")
            output_text = stdout_text + (("\n" + stderr_text) if stderr_text else "")

    outputs_by_step: dict[int, dict[str, int]] = {}
    for line in output_text.splitlines():
        for match in re.finditer(r"\b(o\d+)\[(\d+)\]:\w+\s*:=\s*(-?\d+)", line):
            out_name = match.group(1)
            step_idx = int(match.group(2))
            value = int(match.group(3))
            outputs_by_step.setdefault(step_idx, {})[out_name] = value

    for idx in range(len(steps)):
        got = outputs_by_step.get(idx, {})
        missing = [name for name in output_names if name not in got]
        if missing:
            raise RuntimeError(
                f"{spec_path}: incomplete spec-mode outputs for step {idx}; missing {missing}"
            )
    return outputs_by_step


def _run_tau_repl_batch(
    *,
    tau_bin: str,
    spec_path: Path,
    steps: Sequence[Mapping[str, int]],
    timeout_s: float,
) -> dict[int, dict[str, int]]:
    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    always_exprs = extract_always_exprs(spec_text)
    defs = parse_definitions(spec_text)
    expanded_always_exprs = [inline_definitions(expr, defs) for expr in always_exprs]
    if not input_streams or not output_streams or not always_exprs:
        raise ValueError(f"{spec_path}: missing streams or always clause")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        input_paths: dict[str, Path] = {}
        output_paths: dict[str, Path] = {}

        for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
            values = [str(int(step[name])) for step in steps]
            path = tmpdir_path / f"{name}.in"
            path.write_text("\n".join(values) + "\n", encoding="utf-8")
            input_paths[name] = path

        for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
            output_paths[name] = tmpdir_path / f"{name}.out"

        repl_script = build_repl_script(
            spec_text=spec_text,
            input_streams=input_streams,
            output_streams=output_streams,
            input_paths=input_paths,
            output_paths=output_paths,
            always_exprs=expanded_always_exprs,
            skip_definitions=True,
        )

        proc = subprocess.Popen(
            [tau_bin, "--severity", "error", "--charvar", "false"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
            cwd=spec_path.parent,
            start_new_session=True,
        )
        if proc.stdin is None:
            raise RuntimeError("tau subprocess misconfigured: stdin pipe unavailable")
        proc.stdin.write(repl_script)
        proc.stdin.close()

        deadline = time.monotonic() + float(timeout_s)
        complete = False
        while time.monotonic() < deadline:
            complete = True
            for path in output_paths.values():
                if not path.exists():
                    complete = False
                    break
                values = [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
                if len(values) < len(steps):
                    complete = False
                    break
            if complete:
                break
            time.sleep(0.05)

        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass
        try:
            proc.wait(timeout=1.0)
        except Exception:
            pass

        if not complete:
            raise RuntimeError(f"{spec_path}: Tau REPL batch did not finish within {timeout_s} seconds")

        outputs_by_step: dict[int, dict[str, int]] = {}
        for name, path in output_paths.items():
            values = [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(values) != len(steps):
                raise RuntimeError(
                    f"{spec_path}: output length mismatch for {name}: expected {len(steps)} got {len(values)}"
                )
            for idx, raw in enumerate(values):
                outputs_by_step.setdefault(idx, {})[name] = int(raw)
        return outputs_by_step


def _sort_stream_name(name: str) -> tuple[int, str]:
    suffix = name[1:]
    if suffix.isdigit():
        return int(suffix), name
    return 10**9, name


def build_enumeration_inputs(
    enumeration: Mapping[str, Sequence[int]],
    *,
    max_cases: int,
) -> list[dict[str, int]]:
    if not enumeration:
        raise ValueError("enumeration must not be empty")
    names = sorted(enumeration.keys(), key=_sort_stream_name)
    value_lists: list[list[int]] = []
    total = 1
    for name in names:
        raw_values = enumeration[name]
        if not isinstance(raw_values, Sequence) or isinstance(raw_values, (str, bytes)):
            raise ValueError(f"enumeration for {name} must be a sequence of ints")
        vals = [int(v) for v in raw_values]
        if not vals:
            raise ValueError(f"enumeration for {name} must not be empty")
        value_lists.append(vals)
        total *= len(vals)
    if total > max_cases:
        raise ValueError(f"enumeration has {total} cases (max {max_cases})")
    return [dict(zip(names, combo)) for combo in itertools.product(*value_lists)]


@dataclass(frozen=True)
class TauPropertyResult:
    property_id: str
    expect: str
    passed: bool
    checked_cases: int
    counterexamples: list[dict[str, object]]
    description: str


@dataclass(frozen=True)
class TauAssuranceCase:
    case_index: int
    inputs: dict[str, int]
    outputs: dict[str, int]
    oracle_outputs: dict[str, int]


def _evaluate_property_cases(
    *,
    prop: Mapping[str, object],
    contexts: Sequence[Mapping[str, object]],
    kind: str,
) -> TauPropertyResult:
    prop_id = str(prop.get("id", "")).strip() or f"{kind}_property"
    expr = str(prop.get("expr", "")).strip()
    if not expr:
        raise ValueError(f"{prop_id}: missing expr")
    expect = str(prop.get("expect", "holds")).strip()
    if expect not in {"holds", "counterexample"}:
        raise ValueError(f"{prop_id}: invalid expect {expect!r}")
    when_expr = str(prop.get("when", "")).strip()
    description = str(prop.get("description", "")).strip()

    checked_cases = 0
    counterexamples: list[dict[str, object]] = []
    max_examples_obj = prop.get("max_examples", 3)
    max_examples = _coerce_int(max_examples_obj)
    for idx, context in enumerate(contexts):
        if when_expr and not bool(safe_eval(when_expr, context)):
            continue
        checked_cases += 1
        if bool(safe_eval(expr, context)):
            continue
        if len(counterexamples) < max_examples:
            counterexamples.append(
                {
                    "case_index": idx,
                    "inputs": context.get("inputs"),
                    "outputs": context.get("outputs"),
                    "oracle_outputs": context.get("oracle_outputs"),
                }
            )
    if expect == "holds":
        passed = len(counterexamples) == 0
    else:
        passed = len(counterexamples) > 0
    return TauPropertyResult(
        property_id=prop_id,
        expect=expect,
        passed=passed,
        checked_cases=checked_cases,
        counterexamples=counterexamples,
        description=description,
    )


def collect_assurance_entry_cases(
    *,
    tau_bin: str | None,
    entry: Mapping[str, object],
    root: Path = ROOT,
    oracle_outputs_override: Mapping[str, object] | None = None,
    execution_backend_override: str | None = None,
) -> dict[str, object]:
    spec_path_value = entry.get("path")
    if not isinstance(spec_path_value, str) or not spec_path_value:
        raise ValueError("entry missing path")
    spec_path = Path(spec_path_value)
    if not spec_path.is_absolute():
        spec_path = (root / spec_path).resolve()
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    backend = str(execution_backend_override or entry.get("backend", "")).strip() or "tau_repl"
    mode = str(entry.get("mode", "repl"))
    enumeration_obj = entry.get("enumeration")
    if not isinstance(enumeration_obj, Mapping):
        raise ValueError(f"{spec_path}: missing enumeration object")
    combos = build_enumeration_inputs(enumeration_obj, max_cases=_entry_int(entry, "max_cases", 1024))
    batch_size = _entry_int(entry, "batch_size", 64)
    if batch_size <= 0:
        raise ValueError(f"{spec_path}: batch_size must be positive")

    outputs_by_step: dict[int, dict[str, int]] = {}
    if tau_bin or backend == "mirror_combinational":
        timeout_s = _entry_float(entry, "timeout_s", 10.0)
        for offset in range(0, len(combos), batch_size):
            batch = combos[offset : offset + batch_size]
            if backend == "mirror_combinational":
                batch_outputs = _run_mirror_combinational_batch(
                    spec_path=spec_path,
                    steps=batch,
                )
            elif mode == "spec":
                if not tau_bin:
                    raise ValueError(f"{spec_path}: tau_bin is required for spec backend")
                batch_outputs = _run_tau_spec_mode_batch(
                    tau_bin=tau_bin,
                    spec_path=spec_path,
                    steps=batch,
                    timeout_s=timeout_s,
                )
            elif mode == "repl":
                if not tau_bin:
                    raise ValueError(f"{spec_path}: tau_bin is required for repl backend")
                batch_outputs = _run_tau_repl_batch(
                    tau_bin=tau_bin,
                    spec_path=spec_path,
                    steps=batch,
                    timeout_s=timeout_s,
                )
            else:
                raise ValueError(f"{spec_path}: unsupported backend/mode {backend!r}/{mode!r}")
            for idx, step_outputs in batch_outputs.items():
                outputs_by_step[offset + idx] = step_outputs

    oracle_outputs_cfg = oracle_outputs_override if oracle_outputs_override is not None else entry.get("oracle_outputs", {})
    if oracle_outputs_cfg is None:
        oracle_outputs_cfg = {}
    if not isinstance(oracle_outputs_cfg, Mapping):
        raise ValueError(f"{spec_path}: oracle_outputs must be an object")

    oracle_mismatches: list[dict[str, object]] = []
    step_contexts: list[dict[str, object]] = []
    case_details: list[TauAssuranceCase] = []
    max_oracle_examples = _entry_int(entry, "max_oracle_examples", 8)
    spec_text = spec_path.read_text(encoding="utf-8")

    for idx, inputs in enumerate(combos):
        outputs = outputs_by_step.get(idx, {})
        expected_outputs: dict[str, int] = {}
        for out_name, expr_obj in oracle_outputs_cfg.items():
            expr = str(expr_obj).strip()
            value = _coerce_int(safe_eval(expr, dict(inputs)))
            expected_outputs[str(out_name)] = value
            if outputs_by_step:
                got = outputs.get(str(out_name))
                if got != value and len(oracle_mismatches) < max_oracle_examples:
                    oracle_mismatches.append(
                        {
                            "case_index": idx,
                            "output": str(out_name),
                            "inputs": dict(inputs),
                            "expected": value,
                            "got": got,
                        }
                    )

        outputs_copy = dict(outputs)
        case_details.append(
            TauAssuranceCase(
                case_index=idx,
                inputs=dict(inputs),
                outputs=outputs_copy,
                oracle_outputs=dict(expected_outputs),
            )
        )

        context: dict[str, object] = {
            "inputs": dict(inputs),
            "outputs": outputs_copy,
            "oracle_outputs": dict(expected_outputs),
            "spec_text": spec_text,
            "spec_path": str(spec_path),
        }
        for key, value in inputs.items():
            context[key] = value
        for key, value in outputs_copy.items():
            context[key] = value
        for key, value in expected_outputs.items():
            context[f"oracle_{key}"] = value
        step_contexts.append(context)

    return {
        "id": str(entry.get("id", spec_path.stem)),
        "path": str(spec_path),
        "backend": backend,
        "mode": mode,
        "cases": len(combos),
        "oracle_mismatches": oracle_mismatches,
        "step_contexts": step_contexts,
        "case_details": case_details,
    }


def run_assurance_entry(
    *,
    tau_bin: str | None,
    entry: Mapping[str, object],
    root: Path = ROOT,
) -> dict[str, object]:
    case_report = collect_assurance_entry_cases(tau_bin=tau_bin, entry=entry, root=root)
    spec_path = Path(str(case_report["path"]))
    backend = str(case_report["backend"])
    mode = str(case_report["mode"])
    oracle_mismatches = cast(list[dict[str, object]], case_report["oracle_mismatches"])
    step_contexts = cast(list[dict[str, object]], case_report["step_contexts"])

    property_results = [
        _evaluate_property_cases(prop=prop, contexts=step_contexts, kind="property")
        for prop in _entry_property_list(entry, "properties")
    ]
    static_results = [
        _evaluate_property_cases(
            prop=prop,
            contexts=[
                {
                    "spec_text": spec_path.read_text(encoding="utf-8"),
                    "spec_path": str(spec_path),
                    "inputs": {},
                    "outputs": {},
                    "oracle_outputs": {},
                }
            ],
            kind="static",
        )
        for prop in _entry_property_list(entry, "static_properties")
    ]

    passed = (len(oracle_mismatches) == 0) and all(r.passed for r in property_results) and all(r.passed for r in static_results)
    return {
        "id": str(case_report["id"]),
        "path": str(spec_path),
        "backend": backend,
        "mode": mode,
        "cases": int(case_report["cases"]),
        "passed": passed,
        "oracle_mismatches": oracle_mismatches,
        "properties": [
            {
                "id": r.property_id,
                "expect": r.expect,
                "passed": r.passed,
                "checked_cases": r.checked_cases,
                "description": r.description,
                "counterexamples": r.counterexamples,
            }
            for r in property_results
        ],
        "static_properties": [
            {
                "id": r.property_id,
                "expect": r.expect,
                "passed": r.passed,
                "checked_cases": r.checked_cases,
                "description": r.description,
                "counterexamples": r.counterexamples,
            }
            for r in static_results
        ],
    }


def run_assurance_registry(
    *,
    tau_bin: str | None,
    registry_path: Path,
    only: set[str] | None = None,
    root: Path = ROOT,
) -> dict[str, object]:
    raw = json.loads(registry_path.read_text(encoding="utf-8"))
    specs = raw.get("specs", [])
    if not isinstance(specs, list) or not specs:
        raise ValueError(f"{registry_path}: missing specs list")
    results = []
    selected = only or set()
    for entry in specs:
        if not isinstance(entry, Mapping):
            raise ValueError(f"{registry_path}: spec entries must be objects")
        entry_id = str(entry.get("id", "")).strip()
        if selected and entry_id not in selected:
            continue
        results.append(run_assurance_entry(tau_bin=tau_bin, entry=entry, root=root))
    return {
        "registry": str(registry_path),
        "ok": all(bool(result.get("passed")) for result in results),
        "results": results,
    }
