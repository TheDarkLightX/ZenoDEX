#!/usr/bin/env python3
"""Validate and exhaustively replay the public durable-retraction model subset."""

from __future__ import annotations

import argparse
import copy
import itertools
import json
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final, Mapping, Sequence

import yaml

MODEL_PATH: Final = Path("formal/esso/fcis_durable_retraction_v1.yaml")
EXPECTED_STATE_IDS: Final = (
    "phase",
    "writer_mode",
    "head_authorized",
    "state_published",
    "receipt_published",
    "nullifier_published",
    "replay_published",
    "outbox_published",
    "external_effect",
    "ack_published",
    "commit_seen",
)
EXPECTED_INVARIANT_IDS: Final = (
    "StateIffReceipt",
    "StateIffNullifier",
    "StateIffReplay",
    "StateIffOutbox",
    "EffectRequiresCommittedOutbox",
    "AckRequiresEffectAndOutbox",
    "CommitSeenIffPublication",
    "QuiescedHasNoWriter",
    "PreSwitchUsesLegacyWriter",
    "PostSwitchUsesTargetWriter",
)
EXPECTED_ACTION_IDS: Final = (
    "receive_verified_external_grant",
    "restart_reopen",
    "atomic_publication",
    "retry_same_commit",
    "crash_before_linearization",
    "crash_after_linearization",
    "deliver_committed_effect",
    "acknowledge_delivery",
    "enter_shadow_replay",
    "enter_dual_check",
    "quiesce_writers",
    "switch_authority",
    "validate_post_switch",
    "disable_legacy",
)


class ModelCheckError(ValueError):
    """Closed model-shape or reachable-invariant failure."""


@dataclass(frozen=True, slots=True)
class ModelCheckResult:
    reachable_states: int
    enabled_transitions: int
    action_count: int
    invariant_count: int


def _exact_list(value: object, name: str) -> list[dict[str, Any]]:
    if type(value) is not list or any(type(item) is not dict for item in value):
        raise ModelCheckError(f"{name} must be an exact list of mappings")
    return value


def _unique_ids(items: Sequence[Mapping[str, Any]], name: str) -> tuple[str, ...]:
    identifiers = tuple(item.get("id") for item in items)
    if any(type(identifier) is not str for identifier in identifiers):
        raise ModelCheckError(f"{name} contains a non-string id")
    if len(set(identifiers)) != len(identifiers):
        raise ModelCheckError(f"{name} contains duplicate ids")
    return identifiers  # type: ignore[return-value]


def _type_domain(type_spec: object, name: str) -> tuple[bool | str, ...]:
    if type(type_spec) is not dict:
        raise ModelCheckError(f"{name} type must be a mapping")
    kind = type_spec.get("kind")
    if kind == "bool" and set(type_spec) == {"kind"}:
        return (False, True)
    if kind == "enum" and set(type_spec) == {"kind", "symbols"}:
        symbols = type_spec["symbols"]
        if (
            type(symbols) is not list
            or not symbols
            or any(type(symbol) is not str for symbol in symbols)
            or len(set(symbols)) != len(symbols)
        ):
            raise ModelCheckError(f"{name} enum symbols are not closed and unique")
        return tuple(symbols)
    raise ModelCheckError(f"{name} has an unsupported type")


def _eval_expr(
    expr: object,
    *,
    state: Mapping[str, bool | str],
    params: Mapping[str, bool | str],
    enum_symbols: frozenset[str],
) -> bool | str:
    if type(expr) is not dict:
        raise ModelCheckError("expression must be a mapping")
    keys = set(expr)
    if keys == {"bool"} and type(expr["bool"]) is bool:
        return expr["bool"]
    if keys == {"var"} and type(expr["var"]) is str:
        try:
            return state[expr["var"]]
        except KeyError as error:
            raise ModelCheckError(f"unknown state variable: {expr['var']}") from error
    if keys == {"param"} and type(expr["param"]) is str:
        try:
            return params[expr["param"]]
        except KeyError as error:
            raise ModelCheckError(f"unknown action parameter: {expr['param']}") from error
    if keys == {"enum"} and type(expr["enum"]) is str:
        if expr["enum"] not in enum_symbols:
            raise ModelCheckError(f"unknown enum symbol: {expr['enum']}")
        return expr["enum"]
    if keys != {"op", "args"} or type(expr["op"]) is not str or type(expr["args"]) is not list:
        raise ModelCheckError("expression has an unsupported shape")
    op = expr["op"]
    values = tuple(
        _eval_expr(item, state=state, params=params, enum_symbols=enum_symbols)
        for item in expr["args"]
    )
    if op == "=" and len(values) == 2:
        return values[0] == values[1]
    if op == "not" and len(values) == 1 and type(values[0]) is bool:
        return not values[0]
    if op in {"and", "or"} and values and all(type(value) is bool for value in values):
        return all(values) if op == "and" else any(values)
    if op == "=>" and len(values) == 2 and all(type(value) is bool for value in values):
        return (not values[0]) or values[1]
    raise ModelCheckError(f"unsupported operator or operand types: {op}")


def _state_key(
    state: Mapping[str, bool | str],
    state_ids: tuple[str, ...],
) -> tuple[bool | str, ...]:
    return tuple(state[name] for name in state_ids)


def check_document(document: object) -> ModelCheckResult:
    if type(document) is not dict:
        raise ModelCheckError("model root must be a mapping")
    if document.get("ir_version") != "esso-ir/v1":
        raise ModelCheckError("unexpected model IR version")
    meta = document.get("meta")
    if type(meta) is not dict or meta.get("model_id") != "fcis_durable_retraction_v1":
        raise ModelCheckError("unexpected model identity")

    state_specs = _exact_list(document.get("state_vars"), "state_vars")
    invariant_specs = _exact_list(document.get("invariants"), "invariants")
    action_specs = _exact_list(document.get("actions"), "actions")
    init_specs = _exact_list(document.get("init"), "init")
    state_ids = _unique_ids(state_specs, "state_vars")
    invariant_ids = _unique_ids(invariant_specs, "invariants")
    action_ids = _unique_ids(action_specs, "actions")
    if state_ids != EXPECTED_STATE_IDS:
        raise ModelCheckError("state variable registry is not exact")
    if invariant_ids != EXPECTED_INVARIANT_IDS:
        raise ModelCheckError("invariant registry is not exact")
    if action_ids != EXPECTED_ACTION_IDS:
        raise ModelCheckError("action registry is not exact")

    domains: dict[str, tuple[bool | str, ...]] = {}
    enum_symbols: set[str] = set()
    for state_spec in state_specs:
        identifier = state_spec["id"]
        domain = _type_domain(state_spec.get("type"), f"state {identifier}")
        domains[identifier] = domain
        enum_symbols.update(value for value in domain if type(value) is str)
    init_ids = tuple(init.get("var") for init in init_specs)
    if init_ids != state_ids:
        raise ModelCheckError("initial-state registry is not exact")
    empty_state = {name: domains[name][0] for name in state_ids}
    initial: dict[str, bool | str] = {}
    for init in init_specs:
        identifier = init["var"]
        value = _eval_expr(
            init.get("expr"),
            state=empty_state,
            params={},
            enum_symbols=frozenset(enum_symbols),
        )
        if value not in domains[identifier]:
            raise ModelCheckError(f"initial value has the wrong type: {identifier}")
        initial[identifier] = value

    observables = document.get("observables")
    if type(observables) is not dict or tuple(observables.get("state_vars", ())) != state_ids:
        raise ModelCheckError("observable state registry is not exact")
    if observables.get("effects") != []:
        raise ModelCheckError("public model must not declare external effects")

    frozen_symbols = frozenset(enum_symbols)

    def invariant_failures(state: Mapping[str, bool | str]) -> tuple[str, ...]:
        failures = []
        for invariant in invariant_specs:
            if invariant.get("kind") != "safety":
                raise ModelCheckError("all model invariants must be safety invariants")
            value = _eval_expr(
                invariant.get("expr"),
                state=state,
                params={},
                enum_symbols=frozen_symbols,
            )
            if type(value) is not bool:
                raise ModelCheckError("invariant expression must return a Boolean")
            if not value:
                failures.append(invariant["id"])
        return tuple(failures)

    prepared_actions = []
    for action in action_specs:
        parameters = _exact_list(action.get("params"), f"action {action['id']} params")
        parameter_ids = _unique_ids(parameters, f"action {action['id']} params")
        parameter_domains = tuple(
            _type_domain(parameter.get("type"), f"parameter {parameter['id']}")
            for parameter in parameters
        )
        enum_symbols_for_action = set(frozen_symbols)
        for domain in parameter_domains:
            enum_symbols_for_action.update(value for value in domain if type(value) is str)
        updates = _exact_list(action.get("updates"), f"action {action['id']} updates")
        update_ids = tuple(update.get("var") for update in updates)
        if any(
            type(identifier) is not str or identifier not in domains for identifier in update_ids
        ) or len(set(update_ids)) != len(update_ids):
            raise ModelCheckError(f"action {action['id']} has invalid update targets")
        if action.get("effects") != {}:
            raise ModelCheckError(f"action {action['id']} declares an effect")
        assignments = tuple(
            dict(zip(parameter_ids, values, strict=True))
            for values in itertools.product(*parameter_domains)
        )
        if not assignments:
            assignments = ({},)
        prepared_actions.append((action, assignments, frozenset(enum_symbols_for_action)))

    initial_failures = invariant_failures(initial)
    if initial_failures:
        raise ModelCheckError(f"initial state violates: {initial_failures}")
    reached = {_state_key(initial, state_ids)}
    frontier = deque([initial])
    transitions = 0
    while frontier:
        state = frontier.popleft()
        for action, assignments, action_symbols in prepared_actions:
            for params in assignments:
                enabled = _eval_expr(
                    action.get("guard"),
                    state=state,
                    params=params,
                    enum_symbols=action_symbols,
                )
                if type(enabled) is not bool:
                    raise ModelCheckError("action guard must return a Boolean")
                if not enabled:
                    continue
                target = dict(state)
                for update in action["updates"]:
                    identifier = update["var"]
                    value = _eval_expr(
                        update.get("expr"),
                        state=state,
                        params=params,
                        enum_symbols=action_symbols,
                    )
                    if value not in domains[identifier]:
                        raise ModelCheckError(
                            f"action {action['id']} writes the wrong type to {identifier}"
                        )
                    target[identifier] = value
                transitions += 1
                failures = invariant_failures(target)
                if failures:
                    raise ModelCheckError(
                        f"action {action['id']} reaches invariant violations: {failures}"
                    )
                key = _state_key(target, state_ids)
                if key not in reached:
                    reached.add(key)
                    frontier.append(target)
    return ModelCheckResult(
        reachable_states=len(reached),
        enabled_transitions=transitions,
        action_count=len(action_specs),
        invariant_count=len(invariant_specs),
    )


def _load(path: Path) -> dict[str, Any]:
    document = yaml.safe_load(path.read_text(encoding="utf-8"))
    if type(document) is not dict:
        raise ModelCheckError("model root must be a mapping")
    return document


def _action(document: dict[str, Any], action_id: str) -> dict[str, Any]:
    return next(action for action in document["actions"] if action["id"] == action_id)


def run_self_test(document: dict[str, Any]) -> tuple[str, ...]:
    mutants: list[tuple[str, dict[str, Any]]] = []

    split = copy.deepcopy(document)
    _action(split, "atomic_publication")["updates"] = [
        update
        for update in _action(split, "atomic_publication")["updates"]
        if update["var"] != "receipt_published"
    ]
    mutants.append(("split_publication", split))

    orphan_effect = copy.deepcopy(document)
    _action(orphan_effect, "deliver_committed_effect")["guard"] = {"bool": True}
    mutants.append(("orphan_effect", orphan_effect))

    orphan_ack = copy.deepcopy(document)
    _action(orphan_ack, "acknowledge_delivery")["guard"] = {"bool": True}
    mutants.append(("orphan_ack", orphan_ack))

    wrong_writer = copy.deepcopy(document)
    _action(wrong_writer, "switch_authority")["updates"] = [
        update
        for update in _action(wrong_writer, "switch_authority")["updates"]
        if update["var"] != "writer_mode"
    ]
    mutants.append(("wrong_post_switch_writer", wrong_writer))

    killed = []
    for mutant_id, mutant in mutants:
        try:
            check_document(mutant)
        except ModelCheckError:
            killed.append(mutant_id)
        else:
            raise ModelCheckError(f"self-test mutant survived: {mutant_id}")
    return tuple(killed)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, default=MODEL_PATH)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    document = _load(args.model)
    result = check_document(document)
    killed = run_self_test(document) if args.self_test else ()
    print(
        json.dumps(
            {
                "ok": True,
                "model": args.model.as_posix(),
                "reachable_states": result.reachable_states,
                "enabled_transitions": result.enabled_transitions,
                "actions": result.action_count,
                "invariants": result.invariant_count,
                "self_test_mutants_killed": list(killed),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
