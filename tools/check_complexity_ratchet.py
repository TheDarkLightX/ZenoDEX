#!/usr/bin/env python3
"""Ratchet Python cyclomatic complexity and function-size metrics.

This checker intentionally supports a non-blocking migration path from the
legacy baseline to a strict high-assurance budget. It fails when existing
function metrics exceed the committed baseline or when new functions exceed the
strict budget, so complexity cannot silently grow while teams burn down existing
hotspots.
"""

from __future__ import annotations

import argparse
import ast
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_BASELINE = Path("config/quality/complexity_ratchet_baseline.json")
DEFAULT_PATHS = (Path("src"),)
DEFAULT_COMPLEXITY_BUDGET = 5
DEFAULT_LINE_BUDGET = 60


@dataclass(frozen=True)
class FunctionMetric:
    path: str
    name: str
    line_start: int
    line_end: int
    complexity: int
    lines: int


@dataclass(frozen=True)
class ComplexitySummary:
    file_count: int
    function_count: int
    complexity_budget: int
    line_budget: int
    max_complexity: int
    over_complexity_budget_count: int
    over_line_budget_count: int
    max_function_lines: int
    top_complexity: list[FunctionMetric]
    top_lines: list[FunctionMetric]
    functions: dict[str, FunctionMetric]


class ComplexityVisitor(ast.NodeVisitor):
    """Compute a conservative McCabe-style score for a function body.

    DbC:
    - Precondition: visitor receives a parsed Python function node.
    - Invariant: every independent branch/loop/handler/comprehension increases
      the reported path count monotonically.
    - Postcondition: a straight-line function has complexity 1.
    """

    def __init__(self, root: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self.root = root
        self.complexity = 1

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        if node is self.root:
            self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        if node is self.root:
            self.generic_visit(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:  # noqa: N802
        return

    def visit_If(self, node: ast.If) -> None:  # noqa: N802
        self.complexity += 1
        self.generic_visit(node)

    def visit_For(self, node: ast.For) -> None:  # noqa: N802
        self.complexity += 1
        self.generic_visit(node)

    def visit_AsyncFor(self, node: ast.AsyncFor) -> None:  # noqa: N802
        self.complexity += 1
        self.generic_visit(node)

    def visit_While(self, node: ast.While) -> None:  # noqa: N802
        self.complexity += 1
        self.generic_visit(node)

    def visit_Try(self, node: ast.Try) -> None:  # noqa: N802
        self.complexity += len(node.handlers)
        self.complexity += int(bool(node.orelse))
        self.complexity += int(bool(node.finalbody))
        self.generic_visit(node)

    def visit_BoolOp(self, node: ast.BoolOp) -> None:  # noqa: N802
        self.complexity += max(0, len(node.values) - 1)
        self.generic_visit(node)

    def visit_IfExp(self, node: ast.IfExp) -> None:  # noqa: N802
        self.complexity += 1
        self.generic_visit(node)

    def visit_Match(self, node: ast.Match) -> None:  # noqa: N802
        self.complexity += len(node.cases)
        self.generic_visit(node)

    def visit_comprehension(self, node: ast.comprehension) -> None:
        self.complexity += 1 + len(node.ifs)
        self.generic_visit(node)


class FunctionCollector(ast.NodeVisitor):
    def __init__(self, path: Path) -> None:
        self.path = path
        self.scope: list[str] = []
        self.metrics: list[FunctionMetric] = []

    def visit_ClassDef(self, node: ast.ClassDef) -> None:  # noqa: N802
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        self._visit_function(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        self._visit_function(node)

    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        qualname = ".".join([*self.scope, node.name])
        self.metrics.append(_function_metric(self.path, node, qualname))
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()


def _python_files(paths: Sequence[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".py":
            files.append(path)
            continue
        if path.is_dir():
            files.extend(sorted(path.rglob("*.py")))
    return sorted(set(files))


def _function_metric(path: Path, node: ast.FunctionDef | ast.AsyncFunctionDef, name: str) -> FunctionMetric:
    visitor = ComplexityVisitor(node)
    visitor.visit(node)
    end_line = getattr(node, "end_lineno", node.lineno)
    return FunctionMetric(
        path=path.as_posix(),
        name=name,
        line_start=node.lineno,
        line_end=end_line,
        complexity=visitor.complexity,
        lines=end_line - node.lineno + 1,
    )


def collect_function_metrics(paths: Sequence[Path]) -> tuple[int, list[FunctionMetric]]:
    metrics: list[FunctionMetric] = []
    files = _python_files(paths)
    for path in files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=path.as_posix())
        collector = FunctionCollector(path)
        collector.visit(tree)
        metrics.extend(collector.metrics)
    return len(files), metrics


def _top(metrics: Iterable[FunctionMetric], *, key: str, count: int) -> list[FunctionMetric]:
    return sorted(metrics, key=lambda metric: (getattr(metric, key), metric.path), reverse=True)[:count]


def _metric_base_key(metric: FunctionMetric) -> str:
    return f"{metric.path}::{metric.name}"


def _function_map(metrics: Iterable[FunctionMetric]) -> dict[str, FunctionMetric]:
    functions: dict[str, FunctionMetric] = {}
    seen: dict[str, int] = {}
    for metric in metrics:
        base_key = _metric_base_key(metric)
        seen[base_key] = seen.get(base_key, 0) + 1
        key = base_key if seen[base_key] == 1 else f"{base_key}#{seen[base_key]}"
        functions[key] = metric
    return functions


def summarize(
    metrics: list[FunctionMetric],
    *,
    file_count: int,
    complexity_budget: int,
    line_budget: int,
    top_count: int,
) -> ComplexitySummary:
    return ComplexitySummary(
        file_count=file_count,
        function_count=len(metrics),
        complexity_budget=complexity_budget,
        line_budget=line_budget,
        max_complexity=max((metric.complexity for metric in metrics), default=0),
        over_complexity_budget_count=sum(
            metric.complexity > complexity_budget for metric in metrics
        ),
        over_line_budget_count=sum(metric.lines > line_budget for metric in metrics),
        max_function_lines=max((metric.lines for metric in metrics), default=0),
        top_complexity=_top(metrics, key="complexity", count=top_count),
        top_lines=_top(metrics, key="lines", count=top_count),
        functions=_function_map(metrics),
    )


def _summary_to_json(summary: ComplexitySummary) -> dict[str, object]:
    data = asdict(summary)
    data["functions"] = {
        key: {"complexity": metric.complexity, "lines": metric.lines}
        for key, metric in summary.functions.items()
    }
    data["schema"] = "zenodex/complexity-ratchet/v2"
    return data


def _load_baseline(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _metric_budget_from_baseline(key: str, raw: object) -> tuple[int, int] | None:
    if not isinstance(raw, dict):
        return None
    try:
        return int(raw["complexity"]), int(raw["lines"])
    except (KeyError, TypeError, ValueError):
        return None


def _assert_not_worse(summary: ComplexitySummary, baseline: dict[str, object]) -> list[str]:
    checks = {
        "max_complexity": summary.max_complexity,
        "over_complexity_budget_count": summary.over_complexity_budget_count,
        "over_line_budget_count": summary.over_line_budget_count,
        "max_function_lines": summary.max_function_lines,
    }
    errors: list[str] = []
    for key, current in checks.items():
        allowed = int(baseline.get(key, current))
        if current > allowed:
            errors.append(f"{key} worsened: current={current} baseline={allowed}")

    baseline_functions_raw = baseline.get("functions")
    if not isinstance(baseline_functions_raw, dict):
        errors.append("baseline is missing per-function metrics; regenerate the complexity baseline")
        return errors

    baseline_functions: dict[str, tuple[int, int]] = {}
    for key, value in baseline_functions_raw.items():
        budget = _metric_budget_from_baseline(key, value)
        if budget is None:
            errors.append(f"baseline function metric is malformed: {key}")
            continue
        baseline_functions[str(key)] = budget

    for key, current in summary.functions.items():
        previous = baseline_functions.get(key)
        if previous is None:
            if current.complexity > summary.complexity_budget:
                errors.append(
                    "new function exceeds complexity budget: "
                    f"{key} current={current.complexity} budget={summary.complexity_budget}"
                )
            if current.lines > summary.line_budget:
                errors.append(
                    "new function exceeds line budget: "
                    f"{key} current={current.lines} budget={summary.line_budget}"
                )
            continue
        previous_complexity, previous_lines = previous
        if current.complexity > previous_complexity:
            errors.append(
                f"{key} complexity worsened: current={current.complexity} "
                f"baseline={previous_complexity}"
            )
        if current.lines > previous_lines:
            errors.append(
                f"{key} length worsened: current={current.lines} baseline={previous_lines}"
            )
    return errors


def _assert_strict(summary: ComplexitySummary) -> list[str]:
    errors: list[str] = []
    if summary.over_complexity_budget_count:
        errors.append(
            "strict complexity budget failed: "
            f"{summary.over_complexity_budget_count} functions exceed {summary.complexity_budget}"
        )
    if summary.over_line_budget_count:
        errors.append(
            "strict function-size budget failed: "
            f"{summary.over_line_budget_count} functions exceed {summary.line_budget} lines"
        )
    return errors


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, default=list(DEFAULT_PATHS))
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--complexity-budget", type=int, default=DEFAULT_COMPLEXITY_BUDGET)
    parser.add_argument("--line-budget", type=int, default=DEFAULT_LINE_BUDGET)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--write-baseline", action="store_true")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--allow-empty", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    file_count, metrics = collect_function_metrics(args.paths)
    summary = summarize(
        metrics,
        file_count=file_count,
        complexity_budget=args.complexity_budget,
        line_budget=args.line_budget,
        top_count=args.top,
    )
    data = _summary_to_json(summary)
    empty_errors: list[str] = []
    if not args.allow_empty and (file_count == 0 or not metrics):
        empty_errors.append("scan found no Python functions; pass --allow-empty to permit this")

    if args.write_baseline:
        if empty_errors:
            for error in empty_errors:
                print(f"ERROR: {error}")
            return 2
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        args.baseline.write_text(
            json.dumps(data, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"wrote complexity baseline: {args.baseline}")
        return 0

    errors = (
        _assert_strict(summary)
        if args.strict
        else _assert_not_worse(summary, _load_baseline(args.baseline))
    )
    errors = [*empty_errors, *errors]
    if args.json:
        print(json.dumps({**data, "ok": not errors, "errors": errors}, indent=2, sort_keys=True))
    else:
        print(
            "complexity ratchet: "
            f"functions={summary.function_count} max_complexity={summary.max_complexity} "
            f"over_{summary.complexity_budget}={summary.over_complexity_budget_count} "
            f"max_lines={summary.max_function_lines} "
            f"over_{summary.line_budget}_lines={summary.over_line_budget_count}"
        )
        for error in errors:
            print(f"ERROR: {error}")
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
