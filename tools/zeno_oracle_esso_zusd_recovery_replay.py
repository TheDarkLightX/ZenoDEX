#!/usr/bin/env python3
"""Deterministic public replay for the bounded zUSD Oracle recovery ESSO-IR shell."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Any, Mapping

import yaml


ROOT = Path(__file__).resolve().parents[1]
MODEL_PATH = ROOT / "src" / "kernels" / "dex" / "zusd_oracle_recovery_lifecycle_v1.yaml"
SCHEMA = "zenodex.oracle.esso_zusd_recovery_replay.v1"
ACTION_ID = "compose_oracle_recovery_lifecycle"
PARAM_IDS = [
    "previous_risky_action_blocked",
    "current_oracle_env_ok",
    "current_sync_gate_ok",
    "sync_aligned_to_current_gate",
    "current_risky_ops_allowed",
    "risky_ops_reenabled",
    "rejected_with_reason",
    "rejection_reason_present",
]
EFFECT_IDS = [
    "healthy_now",
    "reenabled_requires_healthy",
    "outcome_total",
    "rejection_total",
    "lifecycle_ok",
]


def _load_yaml(path: Path) -> Mapping[str, Any]:
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must contain an object")
    return obj


def _eval_expr(expr: Mapping[str, Any], params: Mapping[str, bool]) -> bool:
    if "bool" in expr:
        return bool(expr["bool"])
    if "param" in expr:
        name = str(expr["param"])
        if name not in params:
            raise ValueError(f"unknown_param:{name}")
        return bool(params[name])
    op = expr.get("op")
    args = expr.get("args")
    if op == "not":
        if not isinstance(args, list) or len(args) != 1 or not isinstance(args[0], Mapping):
            raise ValueError("invalid_not_expr")
        return not _eval_expr(args[0], params)
    if op in {"and", "or", "xor"}:
        if not isinstance(args, list) or not all(isinstance(arg, Mapping) for arg in args):
            raise ValueError(f"invalid_{op}_expr")
        values = [_eval_expr(arg, params) for arg in args]
        if op == "and":
            return all(values)
        if op == "or":
            return any(values)
        return sum(1 for value in values if value) == 1
    raise ValueError(f"unknown_expr_op:{op}")


def _action(model: Mapping[str, Any]) -> Mapping[str, Any]:
    actions = model.get("actions")
    if not isinstance(actions, list):
        raise ValueError("actions_must_be_list")
    matches = [action for action in actions if isinstance(action, Mapping) and action.get("id") == ACTION_ID]
    if len(matches) != 1:
        raise ValueError(f"expected_one_action:{ACTION_ID}:found_{len(matches)}")
    return matches[0]


def _params_from_action(action: Mapping[str, Any]) -> list[str]:
    params = action.get("params")
    if not isinstance(params, list):
        return []
    return [str(param.get("id")) for param in params if isinstance(param, Mapping)]


def _effects_from_action(action: Mapping[str, Any]) -> Mapping[str, Any]:
    effects = action.get("effects")
    if not isinstance(effects, Mapping):
        return {}
    return effects


def _expected_effects(params: Mapping[str, bool]) -> dict[str, bool]:
    healthy_now = (
        params["current_oracle_env_ok"]
        and params["current_sync_gate_ok"]
        and params["sync_aligned_to_current_gate"]
    )
    reenabled_requires_healthy = (
        not params["risky_ops_reenabled"]
        or (
            params["previous_risky_action_blocked"]
            and healthy_now
            and params["current_risky_ops_allowed"]
        )
    )
    outcome_total = params["risky_ops_reenabled"] != params["rejected_with_reason"]
    rejection_total = not params["rejected_with_reason"] or params["rejection_reason_present"]
    lifecycle_ok = outcome_total and reenabled_requires_healthy and rejection_total
    return {
        "healthy_now": healthy_now,
        "reenabled_requires_healthy": reenabled_requires_healthy,
        "outcome_total": outcome_total,
        "rejection_total": rejection_total,
        "lifecycle_ok": lifecycle_ok,
    }


def _assignment_rows(effects: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for values in itertools.product([False, True], repeat=len(PARAM_IDS)):
        params = dict(zip(PARAM_IDS, values))
        observed = {
            effect_id: _eval_expr(effect, params)
            for effect_id, effect in effects.items()
            if effect_id in EFFECT_IDS and isinstance(effect, Mapping)
        }
        expected = _expected_effects(params)
        rows.append(
            {
                "params": params,
                "observed": observed,
                "expected": expected,
                "ok": observed == expected,
            }
        )
    return rows


def _case(name: str, params: Mapping[str, bool], effects: Mapping[str, Any], expected_lifecycle_ok: bool) -> dict[str, Any]:
    observed = {
        effect_id: _eval_expr(effect, params)
        for effect_id, effect in effects.items()
        if effect_id in EFFECT_IDS and isinstance(effect, Mapping)
    }
    expected = _expected_effects(params)
    ok = observed == expected and observed.get("lifecycle_ok") is expected_lifecycle_ok
    return {
        "id": name,
        "ok": ok,
        "expected_lifecycle_ok": expected_lifecycle_ok,
        "lifecycle_ok": observed.get("lifecycle_ok"),
        "observed": observed,
    }


def _witness_cases(effects: Mapping[str, Any]) -> list[dict[str, Any]]:
    base = {
        "previous_risky_action_blocked": True,
        "current_oracle_env_ok": True,
        "current_sync_gate_ok": True,
        "sync_aligned_to_current_gate": True,
        "current_risky_ops_allowed": True,
        "risky_ops_reenabled": True,
        "rejected_with_reason": False,
        "rejection_reason_present": False,
    }
    reject = {
        **base,
        "current_oracle_env_ok": False,
        "risky_ops_reenabled": False,
        "rejected_with_reason": True,
        "rejection_reason_present": True,
    }
    return [
        _case("valid_reenable_accepts", base, effects, True),
        _case("valid_reject_accepts", reject, effects, True),
        _case(
            "reject_missing_reason_rejects",
            {**reject, "rejection_reason_present": False},
            effects,
            False,
        ),
        _case(
            "reenable_without_previous_block_rejects",
            {**base, "previous_risky_action_blocked": False},
            effects,
            False,
        ),
        _case(
            "reenable_unhealthy_env_rejects",
            {**base, "current_oracle_env_ok": False},
            effects,
            False,
        ),
        _case(
            "reenable_bad_sync_gate_rejects",
            {**base, "current_sync_gate_ok": False},
            effects,
            False,
        ),
        _case(
            "reenable_misaligned_sync_rejects",
            {**base, "sync_aligned_to_current_gate": False},
            effects,
            False,
        ),
        _case(
            "reenable_disallowed_current_risky_ops_rejects",
            {**base, "current_risky_ops_allowed": False},
            effects,
            False,
        ),
        _case(
            "double_outcome_rejects",
            {**base, "rejected_with_reason": True, "rejection_reason_present": True},
            effects,
            False,
        ),
        _case(
            "missing_outcome_rejects",
            {**base, "risky_ops_reenabled": False, "rejected_with_reason": False},
            effects,
            False,
        ),
    ]


def build_receipt(model_path: Path = MODEL_PATH) -> dict[str, Any]:
    errors: list[str] = []
    model = _load_yaml(model_path)

    meta = model.get("meta")
    model_id = meta.get("model_id") if isinstance(meta, Mapping) else None
    if model_id != "zusd_oracle_recovery_lifecycle_v1":
        errors.append("model_id_mismatch")

    try:
        action = _action(model)
    except ValueError as exc:
        action = {}
        errors.append(str(exc))

    params = _params_from_action(action)
    effects = _effects_from_action(action)
    missing_params = [param for param in PARAM_IDS if param not in params]
    unexpected_params = [param for param in params if param not in PARAM_IDS]
    missing_effects = [effect for effect in EFFECT_IDS if effect not in effects]
    unexpected_effects = [effect for effect in effects if effect not in EFFECT_IDS]
    errors.extend(f"missing_param:{param}" for param in missing_params)
    errors.extend(f"unexpected_param:{param}" for param in unexpected_params)
    errors.extend(f"missing_effect:{effect}" for effect in missing_effects)
    errors.extend(f"unexpected_effect:{effect}" for effect in unexpected_effects)

    assignment_rows: list[dict[str, Any]] = []
    witness_cases: list[dict[str, Any]] = []
    if not missing_params and not missing_effects:
        try:
            assignment_rows = _assignment_rows(effects)
            witness_cases = _witness_cases(effects)
        except ValueError as exc:
            errors.append(str(exc))

    mismatches = [row for row in assignment_rows if not row["ok"]]
    failed_witnesses = [case for case in witness_cases if not case["ok"]]
    errors.extend("assignment_effect_mismatch" for _row in mismatches[:1])
    errors.extend(f"witness_failed:{case['id']}" for case in failed_witnesses)

    lifecycle_ok_count = sum(
        1 for row in assignment_rows if row.get("observed", {}).get("lifecycle_ok") is True
    )
    return {
        "schema": SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "model_id": model_id,
        "action_id": ACTION_ID,
        "assignment_count": len(assignment_rows),
        "lifecycle_ok_count": lifecycle_ok_count,
        "assignment_mismatch_count": len(mismatches),
        "witness_case_count": len(witness_cases),
        "failed_witness_count": len(failed_witnesses),
        "errors": errors,
        "witnesses": witness_cases,
        "mismatches": mismatches[:3],
        "not_claimed": [
            "does_not_claim_external_esso_verify_multi",
            "does_not_claim_live_governance_recovery",
            "does_not_claim_production_oracle_truth",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, default=MODEL_PATH)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_receipt(args.model)
    if args.format == "json":
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"status = {receipt['status']}")
        print(f"assignment_count = {receipt['assignment_count']}")
        print(f"lifecycle_ok_count = {receipt['lifecycle_ok_count']}")
        print(f"assignment_mismatch_count = {receipt['assignment_mismatch_count']}")
        print(f"failed_witness_count = {receipt['failed_witness_count']}")
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
