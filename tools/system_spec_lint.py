#!/usr/bin/env python3
"""
System-spec linter (internal).

This repo contains "system-spec/v1" YAML files that describe how verified ESSO
kernels are composed via explicit wiring and global invariants (see:
`src/kernels/dex/zenodex_system_compose_v1.yaml` and
`src/kernels/dex/zenodex_system_compose_v2.yaml`).

This tool is a *static* checker:
  - validates that referenced module kernel YAML files exist
  - validates wiring references: <alias>.<action>.<effect> -> <alias>.<state_var>
  - validates that global invariant expressions reference known <alias>.<state_var>

It does NOT attempt to prove global invariants; it is a mistake-proofing tool
to prevent silent miswiring and typo-driven composition bugs.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Mapping, Sequence, Set, Tuple

import yaml


_REF_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\.([A-Za-z_][A-Za-z0-9_]*)\b")


@dataclass(frozen=True)
class ModuleIndex:
    alias: str
    req_id: str
    kernel_path: Path
    state_vars: Set[str]
    action_effects: Dict[str, Set[str]]


def _load_yaml(path: Path) -> Any:
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _index_kernel(alias: str, req_id: str, kernel_path: Path) -> ModuleIndex:
    obj = _load_yaml(kernel_path)
    if not isinstance(obj, dict):
        raise ValueError(f"kernel YAML is not a mapping: {kernel_path}")
    if obj.get("ir_version") != "esso-ir/v1":
        raise ValueError(f"unexpected kernel ir_version in {kernel_path}: {obj.get('ir_version')!r}")

    state_vars = set()
    for sv in obj.get("state_vars", []) or []:
        if isinstance(sv, dict) and isinstance(sv.get("id"), str):
            state_vars.add(sv["id"])

    action_effects: Dict[str, Set[str]] = {}
    for act in obj.get("actions", []) or []:
        if not isinstance(act, dict) or not isinstance(act.get("id"), str):
            continue
        act_id = act["id"]
        effs = act.get("effects", {}) or {}
        if isinstance(effs, dict):
            action_effects[act_id] = set(str(k) for k in effs.keys())
        else:
            action_effects[act_id] = set()

    return ModuleIndex(
        alias=alias,
        req_id=req_id,
        kernel_path=kernel_path,
        state_vars=state_vars,
        action_effects=action_effects,
    )


def _parse_from_ref(s: str) -> Tuple[str, str, str]:
    # Expected: <alias>.<action_id>.<effect_id>
    parts = s.split(".")
    if len(parts) != 3:
        raise ValueError(f"expected from ref '<alias>.<action>.<effect>', got: {s!r}")
    return parts[0], parts[1], parts[2]


def _parse_to_ref(s: str) -> Tuple[str, str]:
    # Expected: <alias>.<state_var_id>
    parts = s.split(".")
    if len(parts) != 2:
        raise ValueError(f"expected to ref '<alias>.<state_var>', got: {s!r}")
    return parts[0], parts[1]


def lint_system_spec(*, system_spec_path: Path, kernel_dir: Path) -> Mapping[str, Any]:
    errors: List[dict] = []
    warnings: List[dict] = []

    if not system_spec_path.exists():
        return {"ok": False, "errors": [{"code": "missing_system_spec", "path": str(system_spec_path)}], "warnings": []}

    spec = _load_yaml(system_spec_path)
    if not isinstance(spec, dict):
        return {"ok": False, "errors": [{"code": "system_spec_not_mapping", "path": str(system_spec_path)}], "warnings": []}

    if spec.get("schema") != "system-spec/v1":
        errors.append(
            {
                "code": "unexpected_schema",
                "path": str(system_spec_path),
                "expected": "system-spec/v1",
                "actual": spec.get("schema"),
            }
        )

    # Index modules.
    modules = spec.get("modules", []) or []
    if not isinstance(modules, list):
        errors.append({"code": "modules_not_list", "path": str(system_spec_path)})
        modules = []

    idx_by_alias: Dict[str, ModuleIndex] = {}
    for m in modules:
        if not isinstance(m, dict):
            errors.append({"code": "module_not_mapping", "module": m})
            continue
        req_id = m.get("req_id")
        alias = m.get("alias")
        if not isinstance(req_id, str) or not req_id:
            errors.append({"code": "module_missing_req_id", "module": m})
            continue
        if not isinstance(alias, str) or not alias:
            errors.append({"code": "module_missing_alias", "module": m})
            continue
        if alias in idx_by_alias:
            errors.append({"code": "duplicate_alias", "alias": alias})
            continue

        kernel_path = kernel_dir / f"{req_id}.yaml"
        if not kernel_path.exists():
            errors.append({"code": "missing_kernel_yaml", "alias": alias, "req_id": req_id, "path": str(kernel_path)})
            continue

        try:
            idx_by_alias[alias] = _index_kernel(alias, req_id, kernel_path)
        except Exception as exc:
            errors.append(
                {
                    "code": "kernel_index_failed",
                    "alias": alias,
                    "req_id": req_id,
                    "path": str(kernel_path),
                    "error": str(exc),
                }
            )

    # Wiring checks.
    wiring = spec.get("wiring", []) or []
    if not isinstance(wiring, list):
        errors.append({"code": "wiring_not_list", "path": str(system_spec_path)})
        wiring = []

    for w in wiring:
        if not isinstance(w, dict):
            errors.append({"code": "wiring_not_mapping", "wiring": w})
            continue
        from_ref = w.get("from")
        to_ref = w.get("to")
        op = w.get("op")
        if op not in ("set",):
            errors.append({"code": "unsupported_wiring_op", "wiring": w})
            continue
        if not isinstance(from_ref, str) or not isinstance(to_ref, str):
            errors.append({"code": "wiring_missing_refs", "wiring": w})
            continue
        try:
            from_alias, action_id, effect_id = _parse_from_ref(from_ref)
            to_alias, state_var = _parse_to_ref(to_ref)
        except Exception as exc:
            errors.append({"code": "wiring_ref_parse_failed", "wiring": w, "error": str(exc)})
            continue

        src = idx_by_alias.get(from_alias)
        if src is None:
            errors.append({"code": "unknown_from_alias", "alias": from_alias, "wiring": w})
        else:
            effs = src.action_effects.get(action_id)
            if effs is None:
                errors.append(
                    {
                        "code": "unknown_from_action",
                        "alias": from_alias,
                        "action": action_id,
                        "wiring": w,
                        "kernel": str(src.kernel_path),
                    }
                )
            elif effect_id not in effs:
                errors.append(
                    {
                        "code": "unknown_from_effect",
                        "alias": from_alias,
                        "action": action_id,
                        "effect": effect_id,
                        "wiring": w,
                        "kernel": str(src.kernel_path),
                    }
                )

        dst = idx_by_alias.get(to_alias)
        if dst is None:
            errors.append({"code": "unknown_to_alias", "alias": to_alias, "wiring": w})
        else:
            if state_var not in dst.state_vars:
                errors.append(
                    {
                        "code": "unknown_to_state_var",
                        "alias": to_alias,
                        "state_var": state_var,
                        "wiring": w,
                        "kernel": str(dst.kernel_path),
                    }
                )

    # Global invariants: only check that referenced <alias>.<state_var> exist.
    ginvs = spec.get("global_invariants", []) or []
    if not isinstance(ginvs, list):
        errors.append({"code": "global_invariants_not_list", "path": str(system_spec_path)})
        ginvs = []

    for inv in ginvs:
        if not isinstance(inv, dict):
            errors.append({"code": "global_inv_not_mapping", "inv": inv})
            continue
        expr = inv.get("expr")
        if not isinstance(expr, str) or not expr.strip():
            errors.append({"code": "global_inv_missing_expr", "inv": inv})
            continue

        for alias, var in _REF_RE.findall(expr):
            mi = idx_by_alias.get(alias)
            if mi is None:
                errors.append({"code": "global_inv_unknown_alias", "alias": alias, "var": var, "expr": expr})
                continue
            if var not in mi.state_vars:
                errors.append(
                    {
                        "code": "global_inv_unknown_state_var",
                        "alias": alias,
                        "var": var,
                        "expr": expr,
                        "kernel": str(mi.kernel_path),
                    }
                )

    return {"ok": len(errors) == 0, "errors": errors, "warnings": warnings}


def main(argv: Sequence[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("system_spec", type=Path)
    ap.add_argument("--kernel-dir", type=Path, default=Path("src/kernels/dex"))
    ap.add_argument("--json", dest="json_out", type=Path, default=None)
    args = ap.parse_args(list(argv))

    res = lint_system_spec(system_spec_path=args.system_spec, kernel_dir=args.kernel_dir)
    out = json.dumps(res, indent=2, sort_keys=True)
    print(out)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(out + "\n", encoding="utf-8")

    return 0 if res.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
