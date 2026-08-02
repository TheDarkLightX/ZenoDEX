#!/usr/bin/env python3
"""Independent finite-state replay and mutation gate for the FCIS M6 ESSO suite.

This checker intentionally implements only the small ESSO-IR subset used by the
committed models. It is an independent bounded oracle, not a replacement for
`ESSO verify-multi --solvers z3,cvc5`.
"""
from __future__ import annotations

import argparse
import copy
import itertools
import json
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

import yaml


class CheckError(RuntimeError):
    pass


@dataclass(frozen=True)
class Violation:
    invariant: str
    state: tuple[Any, ...]
    action: str | None
    params: tuple[tuple[str, Any], ...]
    reason: str


@dataclass
class Exploration:
    model_id: str
    states: int
    transitions: int
    action_counts: dict[str, int]
    violations: list[Violation]


def _domain(type_spec: Mapping[str, Any]) -> tuple[Any, ...]:
    kind = type_spec["kind"]
    if kind == "bool":
        return (False, True)
    if kind == "enum":
        values = tuple(type_spec["symbols"])
        if not values:
            raise CheckError("empty enum domain")
        return values
    if kind == "int":
        lo, hi = int(type_spec["min"]), int(type_spec["max"])
        if hi < lo or hi - lo > 32:
            raise CheckError(f"invalid or excessive bounded int domain {lo}..{hi}")
        return tuple(range(lo, hi + 1))
    raise CheckError(f"unsupported type kind {kind!r}")


def _eval(expr: Mapping[str, Any], state: Mapping[str, Any], params: Mapping[str, Any]) -> Any:
    if "var" in expr:
        return state[expr["var"]]
    if "param" in expr:
        return params[expr["param"]]
    if "const" in expr:
        return expr["const"]
    if "bool" in expr:
        return bool(expr["bool"])
    if "enum" in expr:
        return expr["enum"]
    op = expr.get("op")
    args = [_eval(item, state, params) for item in expr.get("args", [])]
    if op == "and":
        return all(bool(x) for x in args)
    if op == "or":
        return any(bool(x) for x in args)
    if op == "not":
        if len(args) != 1:
            raise CheckError("not expects one argument")
        return not bool(args[0])
    if op == "=>":
        if len(args) != 2:
            raise CheckError("implication expects two arguments")
        return (not bool(args[0])) or bool(args[1])
    if op == "+":
        return sum(args)
    if op == "-":
        if len(args) == 1:
            return -args[0]
        if len(args) == 2:
            return args[0] - args[1]
        raise CheckError("subtraction expects one or two arguments")
    if op in {"=", "!=", "<", "<=", ">", ">="}:
        if len(args) != 2:
            raise CheckError(f"{op} expects two arguments")
        left, right = args
        return {
            "=": left == right,
            "!=": left != right,
            "<": left < right,
            "<=": left <= right,
            ">": left > right,
            ">=": left >= right,
        }[op]
    raise CheckError(f"unsupported expression {expr!r}")


def _load_model(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or data.get("ir_version") != "esso-ir/v1":
        raise CheckError(f"{path}: not esso-ir/v1")
    required = {"meta", "state_vars", "invariants", "init", "actions"}
    missing = sorted(required - data.keys())
    if missing:
        raise CheckError(f"{path}: missing keys {missing}")
    return data


def _initial_state(model: Mapping[str, Any]) -> tuple[tuple[str, ...], tuple[Any, ...], dict[str, tuple[Any, ...]]]:
    names = tuple(item["id"] for item in model["state_vars"])
    domains = {item["id"]: _domain(item["type"]) for item in model["state_vars"]}
    init_map: dict[str, Any] = {}
    for assignment in model["init"]:
        init_map[assignment["var"]] = _eval(assignment["expr"], init_map, {})
    if set(init_map) != set(names):
        raise CheckError(f"init mismatch: expected {names}, got {tuple(init_map)}")
    values = tuple(init_map[name] for name in names)
    return names, values, domains


def _params(action: Mapping[str, Any]) -> Iterable[dict[str, Any]]:
    specs = action.get("params", [])
    if not specs:
        yield {}
        return
    names = [spec["id"] for spec in specs]
    domains = [_domain(spec["type"]) for spec in specs]
    for values in itertools.product(*domains):
        yield dict(zip(names, values, strict=True))


def explore(model: Mapping[str, Any], *, state_cap: int = 200_000) -> Exploration:
    model_id = model["meta"]["model_id"]
    names, initial, domains = _initial_state(model)
    index = {name: i for i, name in enumerate(names)}
    invariants = tuple(model["invariants"])
    actions = tuple(model["actions"])
    queue: deque[tuple[Any, ...]] = deque([initial])
    seen = {initial}
    transitions = 0
    action_counts = {a["id"]: 0 for a in actions}
    violations: list[Violation] = []
    violation_keys: set[tuple[str, tuple[Any, ...], str | None, tuple[tuple[str, Any], ...], str]] = set()

    def check_state(state_tuple: tuple[Any, ...], action: str | None, params: Mapping[str, Any]) -> None:
        state = dict(zip(names, state_tuple, strict=True))
        for name, value in state.items():
            if value not in domains[name]:
                key = ("__TYPE_DOMAIN__", state_tuple, action, tuple(sorted(params.items())), f"{name}={value!r}")
                if key not in violation_keys:
                    violation_keys.add(key)
                    violations.append(Violation("__TYPE_DOMAIN__", state_tuple, action, tuple(sorted(params.items())), f"{name}={value!r} outside {domains[name]!r}"))
        for invariant in invariants:
            if not bool(_eval(invariant["expr"], state, params)):
                key = (invariant["id"], state_tuple, action, tuple(sorted(params.items())), "false")
                if key not in violation_keys:
                    violation_keys.add(key)
                    violations.append(Violation(invariant["id"], state_tuple, action, tuple(sorted(params.items())), "invariant evaluated false"))

    check_state(initial, None, {})
    while queue:
        current = queue.popleft()
        state = dict(zip(names, current, strict=True))
        for action in actions:
            for params in _params(action):
                if not bool(_eval(action["guard"], state, params)):
                    continue
                updates = {u["var"]: _eval(u["expr"], state, params) for u in action.get("updates", [])}
                successor = list(current)
                for name, value in updates.items():
                    successor[index[name]] = value
                successor_tuple = tuple(successor)
                transitions += 1
                action_counts[action["id"]] += 1
                check_state(successor_tuple, action["id"], params)
                if all(successor_tuple[index[name]] in domains[name] for name in names) and successor_tuple not in seen:
                    seen.add(successor_tuple)
                    if len(seen) > state_cap:
                        raise CheckError(f"{model_id}: state cap exceeded")
                    queue.append(successor_tuple)
    return Exploration(model_id, len(seen), transitions, action_counts, violations)


def mutate(model: Mapping[str, Any], mutation: Mapping[str, Any]) -> dict[str, Any]:
    out = copy.deepcopy(model)
    action = next((a for a in out["actions"] if a["id"] == mutation["action"]), None)
    if action is None:
        raise CheckError(f"unknown action {mutation['action']!r}")
    op = mutation["op"]
    if op == "replace_guard_true":
        action["guard"] = {"bool": True}
    elif op == "remove_update":
        before = len(action["updates"])
        action["updates"] = [u for u in action["updates"] if u["var"] != mutation["var"]]
        if len(action["updates"]) == before:
            raise CheckError(f"update {mutation['var']!r} not found in {mutation['action']}")
    elif op == "replace_update":
        found = False
        for update in action["updates"]:
            if update["var"] == mutation["var"]:
                update["expr"] = mutation["expr"]
                found = True
        if not found:
            raise CheckError(f"update {mutation['var']!r} not found in {mutation['action']}")
    elif op == "append_update":
        action["updates"].append({"var": mutation["var"], "expr": mutation["expr"]})
    else:
        raise CheckError(f"unsupported mutation op {op!r}")
    return out


def _violation_doc(v: Violation, names: tuple[str, ...]) -> dict[str, Any]:
    return {
        "invariant": v.invariant,
        "state": dict(zip(names, v.state, strict=True)),
        "action": v.action,
        "params": dict(v.params),
        "reason": v.reason,
    }


def run(root: Path, output: Path) -> dict[str, Any]:
    manifest_path = root / "formal/esso/fcis_m6_formal_suite_v1.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    models: dict[str, dict[str, Any]] = {}
    paths: dict[str, Path] = {}
    base_results: dict[str, Any] = {}
    errors: list[str] = []

    for item in manifest["models"]:
        path = root / item["path"]
        model = _load_model(path)
        mid = model["meta"]["model_id"]
        models[mid] = model
        paths[mid] = path
        result = explore(model)
        names = tuple(v["id"] for v in model["state_vars"])
        if result.violations:
            errors.append(f"base model {mid} has {len(result.violations)} violation(s)")
        base_results[mid] = {
            "path": str(path.relative_to(root)),
            "states": result.states,
            "transitions": result.transitions,
            "action_counts": result.action_counts,
            "violations": [_violation_doc(v, names) for v in result.violations[:8]],
        }

    disabled_by_model = {
        mid: set(expectations.get("disabled", []))
        for mid, expectations in manifest.get("expected_action_coverage", {}).items()
    }
    for mid, result in base_results.items():
        counts = result["action_counts"]
        disabled = disabled_by_model.get(mid, set())
        for action, count in counts.items():
            if action in disabled:
                if count != 0:
                    errors.append(f"{mid}:{action} expected disabled but has {count} transitions")
            elif count == 0:
                errors.append(f"{mid}:{action} is vacuous/unreachable")

    mutations: list[dict[str, Any]] = list(manifest.get("mutants", []))
    for relative in manifest.get("mutant_manifests", []):
        mutant_doc = json.loads((root / relative).read_text(encoding="utf-8"))
        if mutant_doc.get("schema") != "zenodex/fcis/m6/formal-mutants/v1":
            raise CheckError(f"{relative}: unsupported mutant manifest")
        if any(item.get("model") != mutant_doc.get("model_id") for item in mutant_doc.get("mutants", [])):
            raise CheckError(f"{relative}: crossed model identity")
        mutations.extend(mutant_doc.get("mutants", []))

    mutant_results: list[dict[str, Any]] = []
    invariant_kills: dict[tuple[str, str], int] = {}
    for mutation in mutations:
        model = models[mutation["model"]]
        mutated = mutate(model, mutation)
        result = explore(mutated)
        expected = mutation["expect_invariant"]
        matching = [v for v in result.violations if v.invariant == expected]
        killed = bool(matching)
        if not killed:
            errors.append(f"mutant {mutation['id']} survived; expected {expected}")
        else:
            invariant_kills[(mutation["model"], expected)] = invariant_kills.get((mutation["model"], expected), 0) + 1
        names = tuple(v["id"] for v in model["state_vars"])
        mutant_results.append({
            "id": mutation["id"],
            "model": mutation["model"],
            "operation": mutation["op"],
            "expected_invariant": expected,
            "killed": killed,
            "states": result.states,
            "transitions": result.transitions,
            "witness": _violation_doc(matching[0], names) if matching else None,
            "other_violations": sorted({v.invariant for v in result.violations if v.invariant != expected}),
        })

    invariant_coverage: dict[str, dict[str, int]] = {}
    for mid, model in models.items():
        coverage = {item["id"]: invariant_kills.get((mid, item["id"]), 0) for item in model["invariants"]}
        invariant_coverage[mid] = coverage
        for invariant_id, kills in coverage.items():
            if kills == 0:
                errors.append(f"{mid}:{invariant_id} lacks a retained killing mutant")

    compact_mutants = [
        {
            "id": item["id"],
            "model": item["model"],
            "expected_invariant": item["expected_invariant"],
            "killed": item["killed"],
        }
        for item in mutant_results
    ]
    report = {
        "schema": "zenodex/fcis/m6/formal-suite-check/v1",
        "checker": "independent-bounded-esso-subset-replay",
        "esso_verify_multi_run": False,
        "base_models_safe": not any(base_results[mid]["violations"] for mid in base_results),
        "models": base_results,
        "invariant_mutant_coverage": invariant_coverage,
        "mutants_total": len(mutant_results),
        "mutants_killed": sum(1 for x in mutant_results if x["killed"]),
        "mutants": compact_mutants,
        "errors": errors,
        "nonclaims": manifest["formal_nonclaims"],
        "verdict": "PASS_BOUNDED_INDEPENDENT_REPLAY" if not errors else "FAIL",
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    output = args.output or (args.root / "docs/research/FCIS_M6_FORMAL_SUITE_BOUNDED_RESULT_V1.json")
    report = run(args.root, output)
    print(json.dumps({
        "verdict": report["verdict"],
        "models": len(report["models"]),
        "states": sum(m["states"] for m in report["models"].values()),
        "transitions": sum(m["transitions"] for m in report["models"].values()),
        "mutants_killed": report["mutants_killed"],
        "mutants_total": report["mutants_total"],
        "output": str(output),
        "errors": report["errors"],
    }, indent=2))
    return 0 if report["verdict"].startswith("PASS") else 1


if __name__ == "__main__":
    raise SystemExit(main())
