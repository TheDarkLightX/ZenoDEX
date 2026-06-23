#!/usr/bin/env python3
"""Deterministic public replay for the bounded Oracle recovery TLA model."""

from __future__ import annotations

import argparse
import json
import re
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[1]
TLA_PATH = ROOT / "formal" / "tla" / "OracleRecoveryLifecycle.tla"
CFG_PATH = ROOT / "formal" / "tla" / "OracleRecoveryLifecycle.cfg"
SCHEMA = "zenodex.oracle.tla_recovery_lifecycle_replay.v1"

ActionName = str
Predicate = Callable[["State"], bool]


@dataclass(frozen=True)
class State:
    now_epoch: int
    oracle_epoch: int
    sync_aligned: bool
    permanently_blocked: bool
    risky_action_requested: bool
    risky_ops_allowed: bool


@dataclass(frozen=True)
class ModelConstants:
    epoch_max: int
    max_stale: int


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _parse_constant(text: str, name: str) -> int | None:
    match = re.search(rf"(?m)^{re.escape(name)}\s*==\s*(\d+)\s*$", text)
    return None if match is None else int(match.group(1))


def _definition_names(text: str) -> set[str]:
    return set(re.findall(r"(?m)^([A-Za-z][A-Za-z0-9_]*)\s*==", text))


def _cfg_entries(text: str, kind: str) -> set[str]:
    return set(re.findall(rf"(?m)^{re.escape(kind)}\s+([A-Za-z][A-Za-z0-9_]*)\s*$", text))


def _oracle_fresh(state: State, constants: ModelConstants) -> bool:
    return state.now_epoch - state.oracle_epoch <= constants.max_stale


def _healthy_now(state: State, constants: ModelConstants) -> bool:
    return _oracle_fresh(state, constants) and state.sync_aligned and not state.permanently_blocked


def _quiescent(state: State, constants: ModelConstants) -> bool:
    return state.permanently_blocked or (
        _healthy_now(state, constants)
        and (not state.risky_action_requested or state.risky_ops_allowed)
    )


def _type_ok(state: State, constants: ModelConstants) -> bool:
    return (
        0 <= state.now_epoch <= constants.epoch_max
        and 0 <= state.oracle_epoch <= constants.epoch_max
        and state.oracle_epoch <= state.now_epoch
    )


def _blocked_absorbing(state: State, _constants: ModelConstants) -> bool:
    return not state.permanently_blocked or not state.risky_ops_allowed


def _stale_blocks_risky(state: State, constants: ModelConstants) -> bool:
    return _oracle_fresh(state, constants) or state.permanently_blocked or not state.risky_ops_allowed


def _initial_state() -> State:
    return State(
        now_epoch=0,
        oracle_epoch=0,
        sync_aligned=True,
        permanently_blocked=False,
        risky_action_requested=False,
        risky_ops_allowed=False,
    )


def _enabled_transitions(state: State, constants: ModelConstants) -> list[tuple[ActionName, State]]:
    transitions: list[tuple[ActionName, State]] = []
    fresh = _oracle_fresh(state, constants)

    if state.now_epoch < constants.epoch_max and not state.permanently_blocked:
        next_now = state.now_epoch + 1
        next_fresh = (next_now - state.oracle_epoch) <= constants.max_stale
        transitions.append(
            (
                "AdvanceTime",
                State(
                    now_epoch=next_now,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=state.sync_aligned,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=state.risky_ops_allowed
                    if next_fresh and state.sync_aligned
                    else False,
                ),
            )
        )

    if not state.permanently_blocked and state.sync_aligned:
        transitions.append(
            (
                "BreakSync",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=False,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=False,
                ),
            )
        )

    if not state.risky_action_requested and not state.permanently_blocked:
        transitions.append(
            (
                "RequestRiskyAction",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=state.sync_aligned,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=True,
                    risky_ops_allowed=state.risky_ops_allowed,
                ),
            )
        )

    if not state.permanently_blocked and not fresh:
        transitions.append(
            (
                "UpdateOracle",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.now_epoch,
                    sync_aligned=state.sync_aligned,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=False,
                ),
            )
        )

    if not state.permanently_blocked and fresh and not state.sync_aligned:
        transitions.append(
            (
                "RepairSync",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=True,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=False,
                ),
            )
        )

    if state.risky_action_requested and _healthy_now(state, constants) and not state.risky_ops_allowed:
        transitions.append(
            (
                "ReenableRiskyOps",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=state.sync_aligned,
                    permanently_blocked=state.permanently_blocked,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=True,
                ),
            )
        )

    if not state.permanently_blocked and not fresh:
        transitions.append(
            (
                "BlockPermanently",
                State(
                    now_epoch=state.now_epoch,
                    oracle_epoch=state.oracle_epoch,
                    sync_aligned=state.sync_aligned,
                    permanently_blocked=True,
                    risky_action_requested=state.risky_action_requested,
                    risky_ops_allowed=False,
                ),
            )
        )

    if _quiescent(state, constants):
        transitions.append(("Idle", state))

    return transitions


def _reachable_graph(constants: ModelConstants) -> tuple[set[State], dict[State, list[tuple[ActionName, State]]]]:
    initial = _initial_state()
    seen = {initial}
    graph: dict[State, list[tuple[ActionName, State]]] = {}
    queue: deque[State] = deque([initial])
    while queue:
        state = queue.popleft()
        transitions = _enabled_transitions(state, constants)
        graph[state] = transitions
        for _action, next_state in transitions:
            if next_state not in seen:
                seen.add(next_state)
                queue.append(next_state)
    return seen, graph


def _state_json(state: State) -> dict[str, Any]:
    return {
        "now_epoch": state.now_epoch,
        "oracle_epoch": state.oracle_epoch,
        "sync_aligned": state.sync_aligned,
        "permanently_blocked": state.permanently_blocked,
        "risky_action_requested": state.risky_action_requested,
        "risky_ops_allowed": state.risky_ops_allowed,
    }


def _reachable_without_goal(
    start: State,
    graph: Mapping[State, list[tuple[ActionName, State]]],
    goal: Predicate,
) -> set[State]:
    if goal(start):
        return set()
    seen = {start}
    queue: deque[State] = deque([start])
    while queue:
        state = queue.popleft()
        for _action, next_state in graph[state]:
            if next_state not in seen and not goal(next_state):
                seen.add(next_state)
                queue.append(next_state)
    return seen


def _sccs(nodes: set[State], graph: Mapping[State, list[tuple[ActionName, State]]]) -> list[set[State]]:
    index = 0
    indices: dict[State, int] = {}
    lowlinks: dict[State, int] = {}
    stack: list[State] = []
    on_stack: set[State] = set()
    components: list[set[State]] = []

    def strongconnect(state: State) -> None:
        nonlocal index
        indices[state] = index
        lowlinks[state] = index
        index += 1
        stack.append(state)
        on_stack.add(state)

        for _action, next_state in graph[state]:
            if next_state not in nodes:
                continue
            if next_state not in indices:
                strongconnect(next_state)
                lowlinks[state] = min(lowlinks[state], lowlinks[next_state])
            elif next_state in on_stack:
                lowlinks[state] = min(lowlinks[state], indices[next_state])

        if lowlinks[state] == indices[state]:
            component: set[State] = set()
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.add(member)
                if member == state:
                    break
            components.append(component)

    for node in sorted(nodes, key=lambda item: tuple(_state_json(item).values())):
        if node not in indices:
            strongconnect(node)
    return components


def _has_cycle(component: set[State], graph: Mapping[State, list[tuple[ActionName, State]]]) -> bool:
    if len(component) > 1:
        return True
    state = next(iter(component))
    return any(next_state == state for _action, next_state in graph[state])


def _enabled_action_names(state: State, constants: ModelConstants) -> set[ActionName]:
    return {action for action, _next_state in _enabled_transitions(state, constants)}


def _component_takes_action(
    component: set[State],
    graph: Mapping[State, list[tuple[ActionName, State]]],
    action_name: ActionName,
) -> bool:
    return any(
        action == action_name and next_state in component
        for state in component
        for action, next_state in graph[state]
    )


def _component_is_fair(
    component: set[State],
    graph: Mapping[State, list[tuple[ActionName, State]]],
    constants: ModelConstants,
) -> bool:
    weak_fair = {"UpdateOracle", "RepairSync", "BlockPermanently"}
    strong_fair = {"ReenableRiskyOps"}
    enabled_by_state = {state: _enabled_action_names(state, constants) for state in component}

    for action in weak_fair:
        continuously_enabled = all(action in enabled for enabled in enabled_by_state.values())
        if continuously_enabled and not _component_takes_action(component, graph, action):
            return False

    for action in strong_fair:
        enabled_somewhere = any(action in enabled for enabled in enabled_by_state.values())
        if enabled_somewhere and not _component_takes_action(component, graph, action):
            return False

    return True


def _fair_counterexamples(
    *,
    trigger: Predicate,
    goal: Predicate,
    states: set[State],
    graph: Mapping[State, list[tuple[ActionName, State]]],
    constants: ModelConstants,
) -> list[dict[str, Any]]:
    counterexamples: list[dict[str, Any]] = []
    trigger_states = [state for state in states if trigger(state) and not goal(state)]
    for start in trigger_states:
        candidate_nodes = _reachable_without_goal(start, graph, goal)
        for component in _sccs(candidate_nodes, graph):
            if not _has_cycle(component, graph):
                continue
            if _component_is_fair(component, graph, constants):
                counterexamples.append(
                    {
                        "trigger_state": _state_json(start),
                        "fair_scc_size": len(component),
                        "sample_scc_state": _state_json(
                            sorted(component, key=lambda item: tuple(_state_json(item).values()))[0]
                        ),
                    }
                )
                break
    return counterexamples


def build_receipt(tla_path: Path = TLA_PATH, cfg_path: Path = CFG_PATH) -> dict[str, Any]:
    errors: list[str] = []
    tla_text = _read(tla_path)
    cfg_text = _read(cfg_path)

    epoch_max = _parse_constant(tla_text, "EPOCH_MAX")
    max_stale = _parse_constant(tla_text, "MAX_STALE")
    if epoch_max is None:
        errors.append("missing_constant:EPOCH_MAX")
        epoch_max = 4
    if max_stale is None:
        errors.append("missing_constant:MAX_STALE")
        max_stale = 1
    constants = ModelConstants(epoch_max=epoch_max, max_stale=max_stale)

    definitions = _definition_names(tla_text)
    required_actions = {
        "AdvanceTime",
        "BreakSync",
        "RequestRiskyAction",
        "UpdateOracle",
        "RepairSync",
        "ReenableRiskyOps",
        "BlockPermanently",
        "Idle",
    }
    required_invariants = {"TypeOK", "BlockedAbsorbing", "StaleBlocksRisky"}
    required_properties = {
        "FairImpliesEventuallyFreshOrBlocked",
        "FairImpliesHealthyRequestEventuallyResolved",
    }
    missing_actions = sorted(required_actions - definitions)
    missing_invariants = sorted(required_invariants - _cfg_entries(cfg_text, "INVARIANT"))
    missing_properties = sorted(required_properties - _cfg_entries(cfg_text, "PROPERTY"))
    errors.extend(f"missing_action:{action}" for action in missing_actions)
    errors.extend(f"missing_cfg_invariant:{invariant}" for invariant in missing_invariants)
    errors.extend(f"missing_cfg_property:{prop}" for prop in missing_properties)

    states, graph = _reachable_graph(constants)
    invariant_checks = {
        "TypeOK": lambda state: _type_ok(state, constants),
        "BlockedAbsorbing": lambda state: _blocked_absorbing(state, constants),
        "StaleBlocksRisky": lambda state: _stale_blocks_risky(state, constants),
    }
    invariant_violations = [
        {"id": name, "state": _state_json(state)}
        for name, check in invariant_checks.items()
        for state in states
        if not check(state)
    ]
    errors.extend(f"invariant_failed:{row['id']}" for row in invariant_violations)

    properties = [
        {
            "id": "FairImpliesEventuallyFreshOrBlocked",
            "trigger": lambda state: not _oracle_fresh(state, constants) and not state.permanently_blocked,
            "goal": lambda state: _oracle_fresh(state, constants) or state.permanently_blocked,
        },
        {
            "id": "FairImpliesHealthyRequestEventuallyResolved",
            "trigger": lambda state: state.risky_action_requested and _healthy_now(state, constants),
            "goal": lambda state: state.risky_ops_allowed or state.permanently_blocked,
        },
    ]
    property_results = []
    for prop in properties:
        trigger = prop["trigger"]
        goal = prop["goal"]
        assert callable(trigger)
        assert callable(goal)
        trigger_count = sum(1 for state in states if trigger(state))
        counterexamples = _fair_counterexamples(
            trigger=trigger,
            goal=goal,
            states=states,
            graph=graph,
            constants=constants,
        )
        property_results.append(
            {
                "id": prop["id"],
                "ok": not counterexamples,
                "trigger_state_count": trigger_count,
                "fair_counterexample_count": len(counterexamples),
                "counterexamples": counterexamples[:3],
            }
        )
    failed_properties = [prop for prop in property_results if not prop["ok"]]
    errors.extend(f"property_failed:{prop['id']}" for prop in failed_properties)

    return {
        "schema": SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "module": "OracleRecoveryLifecycle",
        "constants": {
            "EPOCH_MAX": constants.epoch_max,
            "MAX_STALE": constants.max_stale,
        },
        "state_count": len(states),
        "transition_count": sum(len(transitions) for transitions in graph.values()),
        "invariant_violation_count": len(invariant_violations),
        "failed_property_count": len(failed_properties),
        "errors": errors,
        "invariant_violations": invariant_violations[:5],
        "properties": property_results,
        "not_claimed": [
            "does_not_claim_external_tlc_model_checking",
            "does_not_claim_unbounded_or_production_liveness",
            "does_not_claim_production_oracle_truth",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", type=Path, default=TLA_PATH)
    parser.add_argument("--config", type=Path, default=CFG_PATH)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_receipt(args.module, args.config)
    if args.format == "json":
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"status = {receipt['status']}")
        print(f"state_count = {receipt['state_count']}")
        print(f"transition_count = {receipt['transition_count']}")
        print(f"invariant_violation_count = {receipt['invariant_violation_count']}")
        print(f"failed_property_count = {receipt['failed_property_count']}")
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
