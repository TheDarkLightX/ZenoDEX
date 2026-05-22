from __future__ import annotations

"""State-feedback explorer for cross-surface exact-in quote-receipt weird machines.

This explorer stays in the tooling layer. It replays short action sequences over a
single exact-in quote receipt and looks for cross-surface failures that emerge
only after earlier transport or repair steps:
- transport hash failure -> repair -> canonical certificate mismatch
- transport hash failure -> repair -> stale pool snapshot mismatch
- direct pool drift / missing pool after a previously valid receipt
"""

import argparse
import copy
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence, cast

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.quote_receipts import pool_state_fingerprint, receipt_hash
from src.integration.exact_in_route_certificate import EXACT_IN_ROUTE_CERTIFICATE_SCHEMA
from tools import receipt_boundary_concolic as legacy
from tools.stateful_feedback import (
    ExplorationTargetReport,
    FeedbackMode,
    Mutation,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
    report_to_json,
    stable_jsonable,
)
from tools.stateful_semantics import sequence_action_summary


QUOTE_RECEIPTS_FILE = (ROOT_DIR / "src/core/quote_receipts.py").resolve()
EXACT_IN_CERTIFICATE_FILE = (ROOT_DIR / "src/integration/exact_in_route_certificate.py").resolve()
TRACE_FILES = (QUOTE_RECEIPTS_FILE, EXACT_IN_CERTIFICATE_FILE)
TARGET_NAME = "quote_receipt_cross_surface_sequence"
HARNESS_ID = f"quote_receipt_cross_surface_sequence:{TARGET_NAME}"


@dataclass(frozen=True)
class MinimizedWitness:
    target: str
    derivation: str
    outcome_label: str
    path_id: str
    path_length: int
    original_size: int
    minimized_size: int
    payload: object


ActionFn = Callable[[tuple[dict[str, Any], dict[str, Any]]], tuple[dict[str, Any], dict[str, Any]]]


@dataclass(frozen=True)
class ActionSpec:
    name: str
    apply: ActionFn


def _seed_state() -> tuple[dict[str, Any], dict[str, Any]]:
    receipt, pools = legacy._valid_quote_exact_in_target()
    return copy.deepcopy(receipt), copy.deepcopy(pools)


def _copy_state(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    return copy.deepcopy(state[0]), copy.deepcopy(state[1])


def _tamper_body_amount_no_rehash(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    return cast(
        tuple[dict[str, Any], dict[str, Any]],
        legacy._mutate_quote_seed(
            state,
            receipt_mutator=lambda receipt: legacy._mutate_body_only(
                receipt,
                lambda body: body.__setitem__("amount_out", int(body["amount_out"]) + 1),
                rehash=False,
            ),
        ),
    )


def _rehash_current_body(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    receipt, pools = _copy_state(state)
    body = receipt.get("body")
    if not isinstance(body, dict):
        raise TypeError("receipt.body must be a dict")
    receipt["receipt_hash"] = receipt_hash(body)
    return receipt, pools


def _drop_receipt_hash(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    receipt, pools = _copy_state(state)
    receipt["receipt_hash"] = ""
    return receipt, pools


def _tamper_certificate_winner_index_rehash(
    state: tuple[dict[str, Any], dict[str, Any]]
) -> tuple[dict[str, Any], dict[str, Any]]:
    return cast(
        tuple[dict[str, Any], dict[str, Any]],
        legacy._mutate_quote_seed(
            state,
            receipt_mutator=lambda receipt: legacy._mutate_body_only(
                receipt,
                lambda body: body["canonical_route_certificate"].__setitem__(
                    "winner_index",
                    int(body["canonical_route_certificate"]["winner_index"]) + 1,
                ),
                rehash=True,
            ),
        ),
    )


def _drift_pool_snapshot(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    return cast(
        tuple[dict[str, Any], dict[str, Any]],
        legacy._mutate_quote_seed(
            state,
            pools_mutator=lambda pools: pools.__setitem__(
                "p_ab",
                legacy.replace(pools["p_ab"], reserve0=int(pools["p_ab"].reserve0) + 1),
            ),
        ),
    )


def _remove_pool(state: tuple[dict[str, Any], dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    return cast(
        tuple[dict[str, Any], dict[str, Any]],
        legacy._mutate_quote_seed(state, pools_mutator=lambda pools: pools.clear()),
    )


ACTION_SPECS: tuple[ActionSpec, ...] = (
    ActionSpec("drop_receipt_hash", _drop_receipt_hash),
    ActionSpec("tamper_body_amount_no_rehash", _tamper_body_amount_no_rehash),
    ActionSpec("rehash_current_body", _rehash_current_body),
    ActionSpec("tamper_certificate_winner_index_rehash", _tamper_certificate_winner_index_rehash),
    ActionSpec("drift_pool_snapshot", _drift_pool_snapshot),
    ActionSpec("remove_pool", _remove_pool),
)
ACTION_BY_NAME = {spec.name: spec for spec in ACTION_SPECS}


def _append_action_mutation(action_name: str) -> Mutation:
    def _apply(payload: object) -> object:
        return _append_action(payload, action_name)

    return Mutation(name=action_name, apply=_apply)


MUTATIONS: tuple[Mutation, ...] = tuple(_append_action_mutation(spec.name) for spec in ACTION_SPECS)


DERIVATION_BUILDERS: dict[str, Callable[[], object]] = {
    "valid_seed": lambda: _seed_payload(),
    "hash_mismatch": lambda: _seed_payload(("tamper_body_amount_no_rehash",)),
    "tamper_then_rehash": lambda: _seed_payload(("tamper_body_amount_no_rehash", "rehash_current_body")),
    "drop_hash_then_rehash_then_drift": lambda: _seed_payload(
        ("drop_receipt_hash", "rehash_current_body", "drift_pool_snapshot")
    ),
    "drift_pool_snapshot": lambda: _seed_payload(("drift_pool_snapshot",)),
    "winner_index_tamper": lambda: _seed_payload(("tamper_certificate_winner_index_rehash",)),
}


def _seed_payload(steps: tuple[str, ...] = ()) -> dict[str, Any]:
    return {
        "seed": "exact_in_quote_receipt",
        "steps": [{"action": step} for step in steps],
    }


def _append_action(payload: object, action_name: str) -> object:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    out = cast(dict[str, Any], copy.deepcopy(payload))
    steps = out.get("steps")
    if not isinstance(steps, list):
        raise TypeError("payload.steps must be a list")
    steps.append({"action": action_name})
    return out


def _steps(payload: object) -> tuple[str, ...]:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    steps = payload.get("steps")
    if not isinstance(steps, list):
        raise TypeError("payload.steps must be a list")
    names: list[str] = []
    for idx, step in enumerate(steps):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        action = step.get("action")
        if not isinstance(action, str) or action not in ACTION_BY_NAME:
            raise KeyError(f"unknown action at step {idx}: {action!r}")
        names.append(action)
    return tuple(names)


def _materialize_state(payload: object) -> tuple[dict[str, Any], dict[str, Any], tuple[str, ...]]:
    state = _seed_state()
    names = _steps(payload)
    for action_name in names:
        state = ACTION_BY_NAME[action_name].apply(state)
    receipt, pools = state
    return receipt, pools, names


def _transport_relation(receipt: dict[str, Any]) -> str:
    body = receipt.get("body")
    if not isinstance(body, dict):
        return "bad_body"
    raw_hash = receipt.get("receipt_hash")
    if not isinstance(raw_hash, str) or not raw_hash:
        return "missing_hash"
    if raw_hash != receipt_hash(body):
        return "hash_mismatch"
    return "hash_match"


def _certificate_relation(receipt: dict[str, Any]) -> str:
    body = receipt.get("body")
    if not isinstance(body, dict):
        return "bad_body"
    cert = body.get("canonical_route_certificate")
    if cert is None:
        return "missing"
    if not isinstance(cert, dict):
        return "bad_type"
    if str(cert.get("schema", "")) != EXACT_IN_ROUTE_CERTIFICATE_SCHEMA:
        return "bad_schema"
    winner = cert.get("winner_quote")
    if not isinstance(winner, dict):
        return "bad_winner"
    for field in ("asset_in", "asset_out", "amount_in", "amount_out"):
        if winner.get(field) != body.get(field):
            return f"{field}_mismatch"
    if stable_jsonable(winner.get("legs")) != stable_jsonable(body.get("legs")):
        return "legs_mismatch"
    return "match"


def _pool_relation(receipt: dict[str, Any], pools: dict[str, Any]) -> str:
    body = receipt.get("body")
    if not isinstance(body, dict):
        return "bad_body"
    body_pools = body.get("pools")
    if not isinstance(body_pools, dict):
        return "bad_body_pools"
    body_keys = sorted(str(key) for key in body_pools)
    current_keys = sorted(str(key) for key in pools)
    if body_keys != current_keys:
        return "missing_pool"
    for pool_id in body_keys:
        pool = pools.get(pool_id)
        if pool is None:
            return "missing_pool"
        try:
            expected = pool_state_fingerprint(pool)
        except Exception:
            return "bad_pool_state"
        if body_pools.get(pool_id) != expected:
            return "snapshot_mismatch"
    return "snapshot_match"


def cross_surface_semantic_state(
    payload: object,
    outcome_label: str,
    _path_id: str,
    _line_trace: tuple[str, ...],
    target_hits: tuple[str, ...],
    _waypoint_tags: tuple[str, ...],
    _harness_id: str,
) -> object:
    try:
        receipt, pools, actions = _materialize_state(payload)
    except Exception:
        return {
            "outcome_class": outcome_label.split(":", 1)[0],
            "target_hits": list(target_hits),
            "payload_shape": stable_jsonable(payload),
        }
    body = receipt.get("body") if isinstance(receipt, dict) else {}
    cert = body.get("canonical_route_certificate") if isinstance(body, dict) else {}
    return {
        "outcome_class": outcome_label.split(":", 1)[0],
        "target_hits": list(target_hits),
        "step_count": len(actions),
        "applied_actions": list(actions),
        "transport_relation": _transport_relation(receipt),
        "certificate_relation": _certificate_relation(receipt),
        "pool_relation": _pool_relation(receipt, pools),
        "receipt_kind": str(body.get("kind", "")) if isinstance(body, dict) else "",
        "candidate_count": len(cert.get("candidates", [])) if isinstance(cert, dict) else 0,
        "winner_index": cert.get("winner_index") if isinstance(cert, dict) else None,
        "pool_count": len(pools),
    }


def _trace(payload: object) -> tuple[str, str, int, tuple[str, ...]]:
    try:
        receipt, pools, actions = _materialize_state(payload)
        outcome = _sequence_outcome(payload)
        path_summary = {
            "actions": list(actions),
            "transport_relation": _transport_relation(receipt),
            "certificate_relation": _certificate_relation(receipt),
            "pool_relation": _pool_relation(receipt, pools),
            "outcome": outcome,
        }
        path_length = len(actions)
    except Exception as exc:  # pragma: no cover
        outcome = f"{type(exc).__name__}:{exc}"
        path_summary = {"payload": stable_jsonable(payload), "outcome": outcome}
        path_length = 0
    digest = hashlib.sha256(
        json.dumps(stable_jsonable(path_summary), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
            "utf-8"
        )
    ).hexdigest()[:16]
    return outcome, digest, path_length, ()


def _sequence_outcome(payload: object) -> str:
    receipt, pools, names = _materialize_state(payload)
    outcome = legacy._quote_outcome((receipt, pools))
    if outcome == "ok":
        return f"ok:steps={len(names)}"
    if outcome.startswith("reject:"):
        return f"reject:step={len(names)}:{outcome[len('reject:') :]}"
    return f"reject:step={len(names)}:{outcome}"


def _expandable(payload: object) -> bool:
    return isinstance(payload, dict)


def _payload_size(payload: object) -> int:
    return len(json.dumps(stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True))


def minimize_case(derivation: str) -> MinimizedWitness:
    if derivation not in DERIVATION_BUILDERS:
        raise KeyError(f"unknown derivation: {derivation}")
    current = copy.deepcopy(DERIVATION_BUILDERS[derivation]())
    outcome_label, path_id, path_length, _ = _trace(current)
    original_size = _payload_size(current)
    current_steps = _steps(current)
    changed = True
    while changed and current_steps:
        changed = False
        for idx in range(len(current_steps)):
            trial_steps = current_steps[:idx] + current_steps[idx + 1 :]
            trial = _seed_payload(trial_steps)
            trial_outcome, trial_path, trial_length, _ = _trace(trial)
            if (trial_outcome, trial_path, trial_length) == (outcome_label, path_id, path_length):
                current = trial
                current_steps = trial_steps
                changed = True
                break
    minimized_size = _payload_size(current)
    return MinimizedWitness(
        target=TARGET_NAME,
        derivation=derivation,
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        original_size=original_size,
        minimized_size=minimized_size,
        payload=current,
    )


def explore_target(
    name: str = TARGET_NAME,
    *,
    max_depth: int = 3,
    max_frontier: int = 96,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
) -> ExplorationTargetReport:
    if name != TARGET_NAME:
        raise KeyError(f"unknown target: {name}")
    dangerous_surfaces = load_dangerous_surface_manifest(target_manifest)
    return explore_bounded_frontier(
        harness_id=HARNESS_ID,
        seed=_seed_payload(),
        mutations=MUTATIONS,
        trace_fn=_trace,
        expandable=_expandable,
        max_depth=max_depth,
        max_frontier=max_frontier,
        feedback_mode=feedback_mode,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        semantic_state_fn=cross_surface_semantic_state,
        action_summary_fn=lambda prev_payload, next_payload, mutation_name: sequence_action_summary(
            cross_surface_semantic_state,
            prev_payload,
            next_payload,
            mutation_name,
        ),
    )


def explore_all_targets(
    *,
    max_depth: int = 3,
    max_frontier: int = 96,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
) -> tuple[ExplorationTargetReport, ...]:
    return (
        explore_target(
            max_depth=max_depth,
            max_frontier=max_frontier,
            target_manifest=target_manifest,
            target_id=target_id,
            feedback_mode=feedback_mode,
        ),
    )


def _reports_json(reports: Sequence[ExplorationTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/quote-receipt-cross-surface-sequence-grammar-fuzz/v1",
        "reports": [report_to_json(report) for report in reports],
    }


def _minimized_witness_json(witness: MinimizedWitness) -> dict[str, Any]:
    return {
        "schema": "zenodex/quote-receipt-cross-surface-sequence-minimized-witness/v1",
        "witness": {
            **asdict(witness),
            "payload": stable_jsonable(witness.payload),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default=TARGET_NAME, choices=(TARGET_NAME,))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=3)
    parser.add_argument("--max-frontier", type=int, default=96)
    parser.add_argument("--target-manifest")
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    parser.add_argument("--minimize-derivation", choices=tuple(DERIVATION_BUILDERS))
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.minimize_derivation is not None:
        witness = minimize_case(args.minimize_derivation)
        if args.format == "json":
            print(json.dumps(_minimized_witness_json(witness), indent=2, sort_keys=True))
            return 0
        print(f"[{witness.target}] {witness.derivation}: {witness.outcome_label} ({witness.path_id}, len={witness.path_length})")
        return 0

    reports = explore_all_targets(
        max_depth=args.max_depth,
        max_frontier=args.max_frontier,
        target_manifest=args.target_manifest,
        target_id=args.target_id,
        feedback_mode=args.feedback_mode,
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
        return 0
    for report in reports:
        print(
            f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} "
            f"paths={report.unique_path_count} states={report.unique_state_count} transitions={report.unique_transition_count}"
        )
        if report.reached_target_ids:
            print(f"  targets: {', '.join(report.reached_target_ids)}")
        for case in report.cases:
            print(f"  - depth={case.depth} {case.mutation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
