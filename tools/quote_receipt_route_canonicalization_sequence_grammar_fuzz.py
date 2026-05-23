from __future__ import annotations

"""State-feedback explorer for receipt-level route-canonicalization composition.

This harness starts from a valid exact-in quote receipt with a real multi-candidate
canonical route certificate, then explores short action sequences that mutate the
certificate, rebuild it, and optionally repair the body and pool fingerprint map.

The goal is to distinguish:
- certificate-level canonicalization drift
- stale body bindings after a recanonicalized winner
- stale pool fingerprint envelopes after body repair
- fully repaired receipt/certificate states
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

from src.core.quote_receipts import make_route_quote_receipt, pool_state_fingerprint, receipt_hash, verify_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.exact_in_route_certificate import (
    build_exact_in_route_canonical_certificate,
    extract_exact_in_route_certificate_quotes,
)
from src.state.pools import PoolState, PoolStatus
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
TARGET_NAME = "quote_receipt_route_canonicalization_sequence"
HARNESS_ID = f"{TARGET_NAME}:{TARGET_NAME}"


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


ActionFn = Callable[[tuple[dict[str, Any], dict[str, PoolState]]], tuple[dict[str, Any], dict[str, PoolState]]]


@dataclass(frozen=True)
class ActionSpec:
    name: str
    apply: ActionFn


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 10) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _seed_state() -> tuple[dict[str, Any], dict[str, PoolState]]:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000),
        "p_ac": _pool("p_ac", "A", "C", 1_000, 1_000),
        "p_cb": _pool("p_cb", "C", "B", 1_000, 1_000),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    if quote is None:
        raise RuntimeError("failed to build valid exact-in seed quote")
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    if not ok:
        raise RuntimeError(f"invalid seed receipt: {err}")
    return copy.deepcopy(receipt), copy.deepcopy(pools)


def _copy_state(state: tuple[dict[str, Any], dict[str, PoolState]]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    return copy.deepcopy(state[0]), copy.deepcopy(state[1])


def _canonical_certificate(receipt: dict[str, Any]) -> dict[str, Any]:
    body = receipt.get("body")
    if not isinstance(body, dict):
        raise TypeError("receipt.body must be a dict")
    cert = body.get("canonical_route_certificate")
    if not isinstance(cert, dict):
        raise TypeError("receipt.body.canonical_route_certificate must be a dict")
    return cert


def _rehash_receipt_body(receipt: dict[str, Any]) -> dict[str, Any]:
    body = receipt.get("body")
    if not isinstance(body, dict):
        raise TypeError("receipt.body must be a dict")
    receipt["receipt_hash"] = receipt_hash(body)
    return receipt


def _winner_quote_from_cert(cert: dict[str, Any]) -> dict[str, Any]:
    winner = cert.get("winner_quote")
    if not isinstance(winner, dict):
        raise TypeError("certificate.winner_quote must be a dict")
    return winner


def _reorder_candidates_rehash(
    state: tuple[dict[str, Any], dict[str, PoolState]]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    receipt, pools = _copy_state(state)
    cert = _canonical_certificate(receipt)
    candidates = cert.get("candidates")
    if not isinstance(candidates, list) or len(candidates) < 2:
        return receipt, pools
    cert["candidates"] = list(reversed(copy.deepcopy(candidates)))
    return _rehash_receipt_body(receipt), pools


def _drop_current_winner_candidate_rehash(
    state: tuple[dict[str, Any], dict[str, PoolState]]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    receipt, pools = _copy_state(state)
    cert = _canonical_certificate(receipt)
    candidates = cert.get("candidates")
    winner_index = cert.get("winner_index")
    if not isinstance(candidates, list) or len(candidates) <= 1:
        return receipt, pools
    if not isinstance(winner_index, int) or winner_index < 0 or winner_index >= len(candidates):
        return receipt, pools
    del candidates[winner_index]
    return _rehash_receipt_body(receipt), pools


def _rebuild_certificate_from_current_candidates_rehash(
    state: tuple[dict[str, Any], dict[str, PoolState]]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    receipt, pools = _copy_state(state)
    cert = _canonical_certificate(receipt)
    try:
        quotes = extract_exact_in_route_certificate_quotes(cert)
    except Exception:
        return receipt, pools
    rebuilt = build_exact_in_route_canonical_certificate(quotes).to_dict()
    body = cast(dict[str, Any], receipt["body"])
    body["canonical_route_certificate"] = rebuilt
    return _rehash_receipt_body(receipt), pools


def _sync_body_to_certificate_winner_rehash(
    state: tuple[dict[str, Any], dict[str, PoolState]]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    receipt, pools = _copy_state(state)
    body = cast(dict[str, Any], receipt["body"])
    winner = _winner_quote_from_cert(_canonical_certificate(receipt))
    for field in ("asset_in", "asset_out", "amount_in", "amount_out", "legs"):
        body[field] = copy.deepcopy(winner[field])
    return _rehash_receipt_body(receipt), pools


def _sync_body_pools_to_winner_rehash(
    state: tuple[dict[str, Any], dict[str, PoolState]]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    receipt, pools = _copy_state(state)
    body = cast(dict[str, Any], receipt["body"])
    legs = body.get("legs")
    if not isinstance(legs, list):
        return receipt, pools
    pool_ids: set[str] = set()
    for leg in legs:
        if not isinstance(leg, dict):
            continue
        hops = leg.get("hops")
        if not isinstance(hops, list):
            continue
        for hop in hops:
            if not isinstance(hop, dict):
                continue
            pool_id = hop.get("pool_id")
            if isinstance(pool_id, str) and pool_id in pools:
                pool_ids.add(pool_id)
    body["pools"] = {pid: pool_state_fingerprint(pools[pid]) for pid in sorted(pool_ids)}
    return _rehash_receipt_body(receipt), pools


ACTION_SPECS: tuple[ActionSpec, ...] = (
    ActionSpec("reorder_candidates_rehash", _reorder_candidates_rehash),
    ActionSpec("drop_current_winner_candidate_rehash", _drop_current_winner_candidate_rehash),
    ActionSpec("rebuild_certificate_from_current_candidates_rehash", _rebuild_certificate_from_current_candidates_rehash),
    ActionSpec("sync_body_to_certificate_winner_rehash", _sync_body_to_certificate_winner_rehash),
    ActionSpec("sync_body_pools_to_winner_rehash", _sync_body_pools_to_winner_rehash),
)
ACTION_BY_NAME = {spec.name: spec for spec in ACTION_SPECS}


def _append_action_mutation(action_name: str) -> Mutation:
    def _apply(payload: object) -> object:
        return _append_action(payload, action_name)

    return Mutation(name=action_name, apply=_apply)


MUTATIONS: tuple[Mutation, ...] = tuple(_append_action_mutation(spec.name) for spec in ACTION_SPECS)


def _seed_payload(steps: tuple[str, ...] = ()) -> dict[str, Any]:
    return {
        "seed": "exact_in_quote_receipt_route_canonicalization",
        "steps": [{"action": step} for step in steps],
    }


DERIVATION_BUILDERS: dict[str, Callable[[], object]] = {
    "valid_seed": lambda: _seed_payload(),
    "reorder_candidates_rehash": lambda: _seed_payload(("reorder_candidates_rehash",)),
    "reorder_then_rebuild": lambda: _seed_payload(
        ("reorder_candidates_rehash", "rebuild_certificate_from_current_candidates_rehash")
    ),
    "drop_winner_then_rebuild": lambda: _seed_payload(
        ("drop_current_winner_candidate_rehash", "rebuild_certificate_from_current_candidates_rehash")
    ),
    "drop_winner_rebuild_sync_body": lambda: _seed_payload(
        (
            "drop_current_winner_candidate_rehash",
            "rebuild_certificate_from_current_candidates_rehash",
            "sync_body_to_certificate_winner_rehash",
        )
    ),
    "drop_winner_rebuild_sync_body_sync_pools": lambda: _seed_payload(
        (
            "drop_current_winner_candidate_rehash",
            "rebuild_certificate_from_current_candidates_rehash",
            "sync_body_to_certificate_winner_rehash",
            "sync_body_pools_to_winner_rehash",
        )
    ),
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


def _materialize_state(payload: object) -> tuple[dict[str, Any], dict[str, PoolState], tuple[str, ...]]:
    state = _seed_state()
    names = _steps(payload)
    for action_name in names:
        state = ACTION_BY_NAME[action_name].apply(state)
    receipt, pools = state
    return receipt, pools, names


def _stable_field(value: Any) -> Any:
    return stable_jsonable(value)


def _precise_canonical_mismatch(receipt: dict[str, Any]) -> str | None:
    try:
        cert = _canonical_certificate(receipt)
    except Exception as exc:
        return str(exc)
    try:
        quotes = extract_exact_in_route_certificate_quotes(cert)
    except Exception as exc:
        return str(exc)
    expected = build_exact_in_route_canonical_certificate(quotes).to_dict()
    field_reasons = (
        ("asset_in", "asset_in mismatch"),
        ("asset_out", "asset_out mismatch"),
        ("amount_in", "amount_in mismatch"),
        ("candidate_set_hash", "candidate_set_hash mismatch"),
        ("winner_index", "winner_index mismatch"),
        ("winner_route_key_rank_u64", "winner_route_key_rank_u64 mismatch"),
        ("winner_quote", "winner_quote mismatch"),
        ("candidates", "candidate list mismatch"),
        ("argmin_steps", "argmin steps mismatch"),
    )
    for field, reason in field_reasons:
        if _stable_field(cert.get(field)) != _stable_field(expected.get(field)):
            return reason
    return None


def _body_binding_relation(receipt: dict[str, Any]) -> str:
    body = receipt.get("body")
    if not isinstance(body, dict):
        return "bad_body"
    try:
        winner = _winner_quote_from_cert(_canonical_certificate(receipt))
    except Exception:
        return "bad_certificate"
    for field in ("asset_in", "asset_out", "amount_in", "amount_out"):
        if winner.get(field) != body.get(field):
            return f"{field}_mismatch"
    if _stable_field(winner.get("legs")) != _stable_field(body.get("legs")):
        return "legs_mismatch"
    return "match"


def _pool_binding_relation(receipt: dict[str, Any], pools: dict[str, PoolState]) -> str:
    body = receipt.get("body")
    if not isinstance(body, dict):
        return "bad_body"
    pools_payload = body.get("pools")
    if not isinstance(pools_payload, dict):
        return "bad_pools"
    legs = body.get("legs")
    if not isinstance(legs, list):
        return "bad_legs"
    expected_pool_ids: list[str] = []
    for leg in legs:
        if not isinstance(leg, dict):
            return "bad_leg"
        hops = leg.get("hops")
        if not isinstance(hops, list):
            return "bad_hops"
        for hop in hops:
            if not isinstance(hop, dict):
                return "bad_hop"
            pool_id = hop.get("pool_id")
            if not isinstance(pool_id, str) or not pool_id:
                return "bad_pool_id"
            expected_pool_ids.append(pool_id)
    expected_ids = sorted(set(expected_pool_ids))
    current_ids = sorted(str(pid) for pid in pools_payload)
    if expected_ids != current_ids:
        missing = sorted(set(expected_ids) - set(current_ids))
        if missing:
            return "missing_pool_fingerprint"
        return "unexpected_pool_fingerprint"
    for pool_id in expected_ids:
        pool = pools.get(pool_id)
        if pool is None:
            return "missing_pool"
        if pools_payload.get(pool_id) != pool_state_fingerprint(pool):
            return "pool_snapshot_mismatch"
    return "match"


def route_canonicalization_receipt_semantic_state(
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
    winner_quote = cert.get("winner_quote") if isinstance(cert, dict) else {}
    candidates = cert.get("candidates", []) if isinstance(cert, dict) else []
    return {
        "outcome_class": outcome_label.split(":", 1)[0],
        "target_hits": list(target_hits),
        "step_count": len(actions),
        "applied_actions": list(actions),
        "candidate_count": len(candidates) if isinstance(candidates, list) else 0,
        "candidate_amount_outs": [
            int(candidate["quote"]["amount_out"])
            for candidate in candidates[:4]
            if isinstance(candidate, dict)
            and isinstance(candidate.get("quote"), dict)
            and isinstance(candidate["quote"].get("amount_out"), int)
        ]
        if isinstance(candidates, list)
        else [],
        "winner_index": cert.get("winner_index") if isinstance(cert, dict) else None,
        "winner_amount_out": winner_quote.get("amount_out") if isinstance(winner_quote, dict) else None,
        "body_amount_out": body.get("amount_out") if isinstance(body, dict) else None,
        "body_pool_ids": sorted(body.get("pools", {}).keys()) if isinstance(body, dict) and isinstance(body.get("pools"), dict) else [],
        "certificate_relation": _precise_canonical_mismatch(receipt) or "match",
        "body_binding_relation": _body_binding_relation(receipt),
        "pool_binding_relation": _pool_binding_relation(receipt, pools),
    }


def _trace(payload: object) -> tuple[str, str, int, tuple[str, ...]]:
    try:
        receipt, pools, actions = _materialize_state(payload)
        ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
        if ok:
            outcome = f"ok:steps={len(actions)}"
        else:
            error = str(err)
            if error == "bad_canonical_route_certificate:certificate payload mismatch":
                precise = _precise_canonical_mismatch(receipt)
                if precise:
                    error = f"bad_canonical_route_certificate:{precise}"
            outcome = f"reject:step={len(actions)}:{error}"
        path_summary = {
            "actions": list(actions),
            "certificate_relation": _precise_canonical_mismatch(receipt) or "match",
            "body_binding_relation": _body_binding_relation(receipt),
            "pool_binding_relation": _pool_binding_relation(receipt, pools),
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
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    if ok:
        return f"ok:steps={len(names)}"
    error = str(err)
    if error == "bad_canonical_route_certificate:certificate payload mismatch":
        precise = _precise_canonical_mismatch(receipt)
        if precise:
            error = f"bad_canonical_route_certificate:{precise}"
    return f"reject:step={len(names)}:{error}"


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
    max_depth: int = 4,
    max_frontier: int = 48,
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
        semantic_state_fn=route_canonicalization_receipt_semantic_state,
        action_summary_fn=lambda prev_payload, next_payload, mutation_name: sequence_action_summary(
            route_canonicalization_receipt_semantic_state,
            prev_payload,
            next_payload,
            mutation_name,
        ),
    )


def explore_all_targets(
    *,
    max_depth: int = 4,
    max_frontier: int = 48,
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
        "schema": "zenodex/quote-receipt-route-canonicalization-sequence-grammar-fuzz/v1",
        "reports": [report_to_json(report) for report in reports],
    }


def _minimized_witness_json(witness: MinimizedWitness) -> dict[str, Any]:
    return {
        "schema": "zenodex/quote-receipt-route-canonicalization-sequence-minimized-witness/v1",
        "witness": {
            **asdict(witness),
            "payload": stable_jsonable(witness.payload),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default=TARGET_NAME, choices=(TARGET_NAME,))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=4)
    parser.add_argument("--max-frontier", type=int, default=48)
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
