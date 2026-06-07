#!/usr/bin/env python3
"""Ratchet Python cyclomatic complexity and function-size metrics.

This checker intentionally supports a non-blocking migration path from the
legacy baseline to a strict high-assurance budget. It fails when current metrics
exceed the committed baseline, so complexity cannot silently grow while teams
burn down existing hotspots.
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
    qualname: str
    metric_id: str
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


class ComplexityVisitor(ast.NodeVisitor):
    """Compute a conservative McCabe-style score for a function body.

    DbC:
    - Precondition: visitor receives a parsed Python function node.
    - Invariant: every independent branch/loop/handler/comprehension increases
      the reported path count monotonically.
    - Postcondition: a straight-line function has complexity 1.
    """

    def __init__(self) -> None:
        self.complexity = 1
        self._inside_nested_function = False

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        if self._inside_nested_function:
            return
        self._inside_nested_function = True
        self.generic_visit(node)
        self._inside_nested_function = False

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        if self._inside_nested_function:
            return
        self._inside_nested_function = True
        self.generic_visit(node)
        self._inside_nested_function = False

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

    def visit_comprehension(self, node: ast.comprehension) -> None:
        self.complexity += 1 + len(node.ifs)
        self.generic_visit(node)


def _python_files(paths: Sequence[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".py":
            files.append(path)
            continue
        if path.is_dir():
            files.extend(sorted(path.rglob("*.py")))
    return sorted(set(files))


def _function_metric(
    path: Path, node: ast.FunctionDef | ast.AsyncFunctionDef, *, qualname: str
) -> FunctionMetric:
    visitor = ComplexityVisitor()
    visitor.visit(node)
    end_line = getattr(node, "end_lineno", node.lineno)
    path_text = path.as_posix()
    return FunctionMetric(
        path=path_text,
        qualname=qualname,
        metric_id=f"{path_text}::{qualname}@{node.lineno}",
        name=node.name,
        line_start=node.lineno,
        line_end=end_line,
        complexity=visitor.complexity,
        lines=end_line - node.lineno + 1,
    )


class FunctionMetricCollector(ast.NodeVisitor):
    """Collect function metrics with qualified names.

    REVIEW [B -> A-]: the first ratchet compared only aggregate maxima/counts.
    That missed regressions inside existing hotspots. Qualified per-function
    identities make those hotspots independently ratcheted.
    """

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
        self.metrics.append(_function_metric(self.path, node, qualname=qualname))
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()


def collect_function_metrics(paths: Sequence[Path]) -> tuple[int, list[FunctionMetric]]:
    metrics: list[FunctionMetric] = []
    files = _python_files(paths)
    for path in files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=path.as_posix())
        collector = FunctionMetricCollector(path)
        collector.visit(tree)
        metrics.extend(collector.metrics)
    return len(files), metrics


def _top(metrics: Iterable[FunctionMetric], *, key: str, count: int) -> list[FunctionMetric]:
    return sorted(metrics, key=lambda metric: (getattr(metric, key), metric.path), reverse=True)[:count]


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
    )


def _summary_to_json(summary: ComplexitySummary) -> dict[str, object]:
    data = asdict(summary)
    data["schema"] = "zenodex/complexity-ratchet/v1"
    return data


def _protected_metrics(metrics: Iterable[FunctionMetric], *, summary: ComplexitySummary) -> list[FunctionMetric]:
    """Return functions that must never worsen under the legacy ratchet.

    A function is protected once it already exceeds either budget. New functions
    are still allowed only when they stay within both budgets.
    """
    return sorted(
        (
            metric
            for metric in metrics
            if metric.complexity > summary.complexity_budget or metric.lines > summary.line_budget
        ),
        key=lambda metric: metric.metric_id,
    )


def _report_to_json(summary: ComplexitySummary, metrics: list[FunctionMetric]) -> dict[str, object]:
    data = _summary_to_json(summary)
    data["protected_functions"] = [asdict(metric) for metric in _protected_metrics(metrics, summary=summary)]
    return data


def _load_baseline(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _baseline_protected_functions(baseline: dict[str, object]) -> dict[str, dict[str, object]]:
    raw = baseline.get("protected_functions")
    if not isinstance(raw, list):
        return {}
    out: dict[str, dict[str, object]] = {}
    for entry in raw:
        if not isinstance(entry, dict):
            continue
        metric_id = entry.get("metric_id")
        if isinstance(metric_id, str):
            out[metric_id] = entry
    return out


def _int_field(mapping: dict[str, object], key: str, default: int) -> int:
    value = mapping.get(key)
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return default


def _assert_function_metrics_not_worse(
    metrics: list[FunctionMetric], summary: ComplexitySummary, baseline: dict[str, object]
) -> list[str]:
    errors: list[str] = []
    baseline_by_id = _baseline_protected_functions(baseline)
    current_by_id = {metric.metric_id: metric for metric in metrics}

    for metric_id, baseline_metric in sorted(baseline_by_id.items()):
        current = current_by_id.get(metric_id)
        if current is None:
            continue
        allowed_complexity = _int_field(baseline_metric, "complexity", current.complexity)
        allowed_lines = _int_field(baseline_metric, "lines", current.lines)
        if current.complexity > allowed_complexity:
            errors.append(
                f"{metric_id} complexity worsened: "
                f"current={current.complexity} baseline={allowed_complexity}"
            )
        if current.lines > allowed_lines:
            errors.append(
                f"{metric_id} lines worsened: current={current.lines} baseline={allowed_lines}"
            )

    for metric in metrics:
        if metric.metric_id in baseline_by_id:
            continue
        if metric.complexity > summary.complexity_budget:
            errors.append(
                f"{metric.metric_id} is a new over-complexity function: "
                f"current={metric.complexity} budget={summary.complexity_budget}"
            )
        if metric.lines > summary.line_budget:
            errors.append(
                f"{metric.metric_id} is a new oversized function: "
                f"current={metric.lines} budget={summary.line_budget}"
            )
    return errors


def _assert_not_worse(
    summary: ComplexitySummary, metrics: list[FunctionMetric], baseline: dict[str, object]
) -> list[str]:
    checks = {
        "max_complexity": summary.max_complexity,
        "over_complexity_budget_count": summary.over_complexity_budget_count,
        "over_line_budget_count": summary.over_line_budget_count,
        "max_function_lines": summary.max_function_lines,
    }
    errors: list[str] = []
    for key, current in checks.items():
        allowed = _int_field(baseline, key, current)
        if current > allowed:
            errors.append(f"{key} worsened: current={current} baseline={allowed}")
    if "protected_functions" not in baseline:
        errors.append("baseline missing protected_functions per-function ratchet")
    else:
        errors.extend(_assert_function_metrics_not_worse(metrics, summary, baseline))
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
    data = _report_to_json(summary, metrics)

    if args.write_baseline:
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
        else _assert_not_worse(summary, metrics, _load_baseline(args.baseline))
    )
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
