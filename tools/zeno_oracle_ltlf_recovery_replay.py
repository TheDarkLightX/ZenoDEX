#!/usr/bin/env python3
"""Deterministic public replay for the bounded Oracle recovery LTLf model."""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import yaml


ROOT = Path(__file__).resolve().parents[1]
MODEL_PATH = ROOT / "formal" / "ltlf" / "oracle_recovery_ltlf_v1.yaml"
GOALS_PATH = ROOT / "formal" / "ltlf" / "oracle_recovery_goal_family_v1.json"
SCHEMA = "zenodex.oracle.ltlf_recovery_replay.v1"
MAX_NOW_EPOCH = 4
MAX_STALE_EPOCHS = 1


@dataclass(frozen=True)
class State:
    now_epoch: int
    oracle_epoch: int
    oracle_fresh: bool
    permanently_blocked: bool
    risky_op_attempted: bool


def _load_yaml(path: Path) -> Mapping[str, Any]:
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must contain an object")
    return obj


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must contain an object")
    return obj


def _action_ids(model: Mapping[str, Any]) -> set[str]:
    raw = model.get("actions")
    if not isinstance(raw, list):
        return set()
    return {str(action.get("id")) for action in raw if isinstance(action, Mapping)}


def _invariant_ids(model: Mapping[str, Any]) -> set[str]:
    raw = model.get("invariants")
    if not isinstance(raw, list):
        return set()
    return {str(invariant.get("id")) for invariant in raw if isinstance(invariant, Mapping)}


def _required_goal_ids(goals: Mapping[str, Any]) -> set[str]:
    raw = goals.get("required_goal_ids")
    if not isinstance(raw, list):
        return set()
    return {str(goal_id) for goal_id in raw}


def _all_goal_ids(goals: Mapping[str, Any]) -> set[str]:
    raw = goals.get("goals")
    if not isinstance(raw, list):
        return set()
    return {str(goal.get("id")) for goal in raw if isinstance(goal, Mapping)}


def _initial_state() -> State:
    return State(
        now_epoch=0,
        oracle_epoch=0,
        oracle_fresh=True,
        permanently_blocked=False,
        risky_op_attempted=False,
    )


def _is_stale(state: State) -> bool:
    return not state.oracle_fresh and not state.permanently_blocked


def _enabled_actions(state: State) -> set[str]:
    enabled = {"end"}
    if state.now_epoch < MAX_NOW_EPOCH and not state.permanently_blocked:
        enabled.add("advance_time")
    if not state.permanently_blocked and not state.oracle_fresh:
        enabled.add("update_oracle")
        enabled.add("block_permanently")
    if state.oracle_fresh and not state.permanently_blocked:
        enabled.add("attempt_risky_op")
    return enabled


def _step(state: State, action: str) -> State:
    if action not in _enabled_actions(state):
        raise ValueError(f"action_not_enabled:{action}")
    if action == "advance_time":
        next_now = state.now_epoch + 1
        return State(
            now_epoch=next_now,
            oracle_epoch=state.oracle_epoch,
            oracle_fresh=(next_now - state.oracle_epoch) <= MAX_STALE_EPOCHS,
            permanently_blocked=state.permanently_blocked,
            risky_op_attempted=state.risky_op_attempted,
        )
    if action == "update_oracle":
        return State(
            now_epoch=state.now_epoch,
            oracle_epoch=state.now_epoch,
            oracle_fresh=True,
            permanently_blocked=False,
            risky_op_attempted=state.risky_op_attempted,
        )
    if action == "block_permanently":
        return State(
            now_epoch=state.now_epoch,
            oracle_epoch=state.oracle_epoch,
            oracle_fresh=False,
            permanently_blocked=True,
            risky_op_attempted=state.risky_op_attempted,
        )
    if action == "attempt_risky_op":
        return State(
            now_epoch=state.now_epoch,
            oracle_epoch=state.oracle_epoch,
            oracle_fresh=state.oracle_fresh,
            permanently_blocked=state.permanently_blocked,
            risky_op_attempted=True,
        )
    if action == "end":
        return state
    raise ValueError(f"unknown_action:{action}")


def _state_json(state: State) -> dict[str, Any]:
    return {
        "now_epoch": state.now_epoch,
        "oracle_epoch": state.oracle_epoch,
        "oracle_fresh": state.oracle_fresh,
        "permanently_blocked": state.permanently_blocked,
        "risky_op_attempted": state.risky_op_attempted,
    }


def _reachable_graph() -> tuple[set[State], dict[State, dict[str, State]]]:
    initial = _initial_state()
    seen = {initial}
    graph: dict[State, dict[str, State]] = {}
    queue: deque[State] = deque([initial])
    while queue:
        state = queue.popleft()
        transitions = {action: _step(state, action) for action in sorted(_enabled_actions(state))}
        graph[state] = transitions
        for next_state in transitions.values():
            if next_state not in seen:
                seen.add(next_state)
                queue.append(next_state)
    return seen, graph


def _path_to_event(graph: Mapping[State, Mapping[str, State]], event_action: str) -> list[dict[str, Any]] | None:
    initial = _initial_state()
    queue: deque[tuple[State, list[dict[str, Any]]]] = deque([(initial, [])])
    seen = {initial}
    while queue:
        state, path = queue.popleft()
        for action, next_state in graph[state].items():
            next_path = [*path, {"action": action, "state": _state_json(next_state)}]
            if action == event_action:
                return next_path
            if next_state not in seen:
                seen.add(next_state)
                queue.append((next_state, next_path))
    return None


def build_receipt(model_path: Path = MODEL_PATH, goals_path: Path = GOALS_PATH) -> dict[str, Any]:
    errors: list[str] = []
    model = _load_yaml(model_path)
    goals = _load_json(goals_path)

    meta = model.get("meta")
    model_id = meta.get("model_id") if isinstance(meta, Mapping) else None
    if model_id != "oracle_recovery_ltlf_v1":
        errors.append("model_id_mismatch")

    required_actions = {"advance_time", "update_oracle", "block_permanently", "attempt_risky_op", "end"}
    missing_actions = sorted(required_actions - _action_ids(model))
    errors.extend(f"missing_action:{action}" for action in missing_actions)

    required_invariants = {"inv_oracle_not_from_future", "inv_stale_blocks_risky", "inv_blocked_absorbing"}
    missing_invariants = sorted(required_invariants - _invariant_ids(model))
    errors.extend(f"missing_invariant:{invariant}" for invariant in missing_invariants)

    required_goals = {
        "G_stale_eventually_recovers",
        "G_stale_blocks_risky",
        "G_recovery_reachable",
    }
    declared_required_goals = _required_goal_ids(goals)
    missing_required_goals = sorted(required_goals - declared_required_goals)
    missing_goal_defs = sorted(required_goals - _all_goal_ids(goals))
    errors.extend(f"missing_required_goal:{goal}" for goal in missing_required_goals)
    errors.extend(f"missing_goal_definition:{goal}" for goal in missing_goal_defs)

    states, graph = _reachable_graph()
    stale_states = [state for state in states if _is_stale(state)]
    stale_can_recover_or_block = all(
        {"update_oracle", "block_permanently"}.issubset(_enabled_actions(state))
        for state in stale_states
    )
    stale_blocks_risky = all("attempt_risky_op" not in _enabled_actions(state) for state in stale_states)
    recovery_path = _path_to_event(graph, "update_oracle")
    block_path = _path_to_event(graph, "block_permanently")
    end_path = _path_to_event(graph, "end")

    goal_results = [
        {
            "id": "G_stale_eventually_recovers",
            "ok": stale_can_recover_or_block,
            "checked": "every reachable stale state enables update_oracle and block_permanently",
            "stale_state_count": len(stale_states),
        },
        {
            "id": "G_stale_blocks_risky",
            "ok": stale_blocks_risky,
            "checked": "attempt_risky_op is disabled in every reachable stale state",
            "stale_state_count": len(stale_states),
        },
        {
            "id": "G_recovery_reachable",
            "ok": recovery_path is not None,
            "witness": recovery_path or [],
        },
        {
            "id": "G_block_reachable",
            "ok": block_path is not None,
            "witness": block_path or [],
        },
        {
            "id": "G_end_explicit",
            "ok": end_path is not None,
            "witness": end_path or [],
        },
    ]
    failed_goals = [goal for goal in goal_results if goal["ok"] is not True]
    errors.extend(f"goal_failed:{goal['id']}" for goal in failed_goals)

    return {
        "schema": SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "model_id": model_id,
        "state_count": len(states),
        "transition_count": sum(len(transitions) for transitions in graph.values()),
        "required_goal_count": len(required_goals),
        "failed_goal_count": len(failed_goals),
        "errors": errors,
        "goals": goal_results,
        "not_claimed": [
            "does_not_claim_external_esso_synthesis",
            "does_not_claim_unbounded_liveness",
            "does_not_claim_production_oracle_truth",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, default=MODEL_PATH)
    parser.add_argument("--goals", type=Path, default=GOALS_PATH)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_receipt(args.model, args.goals)
    if args.format == "json":
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"status = {receipt['status']}")
        print(f"state_count = {receipt['state_count']}")
        print(f"transition_count = {receipt['transition_count']}")
        print(f"failed_goal_count = {receipt['failed_goal_count']}")
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
