"""Finite ESSO-IR handoff for the real V1/V2 signal migration graph.

The IR carries producer, consumer, queued-schema, and exact metadata-word
state. Its actions encode accepted calls and typed rejects as no-op state
updates with observable decision fields. The verifier interprets a supplied IR
across the finite graph rather than comparing it to a second generator call.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Final, Mapping, cast

from ..model import Evidence
from ..signal_migration import (
    OBSERVATIONS,
    Action,
    CandidateMode,
    ConsumerCapability,
    Effect,
    ParseOutcome,
    ProducerVersion,
    QueuedSchema,
    State,
    TerminalOutcome,
    Transition,
    TransitionCode,
    check_migration,
    controller_invariant,
    safe_transition,
    unsafe_transition,
)

_WORDS: Final[tuple[int, ...]] = tuple(range(128))
_GRAPH_SOURCE_PATH: Final[str] = "src/zenolacuna/ports/signal_graph_esso.py"
_GRAPH_SOURCE_FILE: Final[Path] = Path(__file__).resolve()
_PINNED_GRAPH_SHA256: Final[str] = hashlib.sha256(_GRAPH_SOURCE_FILE.read_bytes()).hexdigest()

P, C, Q, W = "producer", "consumer", "queued_schema", "queued_word"
_STATE_VARIABLES: Final[tuple[str, ...]] = (C, P, Q, W)
_EFFECTS: Final[tuple[str, ...]] = (
    "accepted", "auth_state", "code", "effect", "freshness_state",
    "observation_schema", "parse_outcome", "terminal",
)
_TOP_FIELDS: Final[frozenset[str]] = frozenset(
    {"ir_version", "meta", "observables", "types", "state_vars", "invariants", "init", "actions", "refinement"}
)
_DISCARDED: Final[tuple[str, ...]] = ("normalized_json", "error_type", "error")

P1, P2 = 0, 1
COLD, DUAL, NEW = 0, 1, 2
EMPTY, V1, V2 = 0, 1, 2
_CODE: Final[dict[TransitionCode, int]] = {
    TransitionCode.APPLIED: 0, TransitionCode.ENQUEUED: 1,
    TransitionCode.QUEUE_FULL: 2, TransitionCode.QUEUE_EMPTY: 3,
    TransitionCode.PRODUCER_ALREADY_V2: 4, TransitionCode.PRODUCER_ALREADY_V1: 5,
    TransitionCode.CONSUMER_ALREADY_NEW: 6, TransitionCode.CONSUMER_ALREADY_OLD: 7,
    TransitionCode.GUARD_REJECTED: 8, TransitionCode.HOST_CAPABILITY_REJECTED: 9,
    TransitionCode.ACTUAL_PARSER_REJECTED: 10, TransitionCode.SOURCE_SNAPSHOT_CHANGED: 11,
}
_TERMINAL: Final[dict[TerminalOutcome, int]] = {
    TerminalOutcome.NONE: 0, TerminalOutcome.DELIVERED: 1,
    TerminalOutcome.RETRIED_DELIVERED: 2, TerminalOutcome.CANCELLED: 3,
    TerminalOutcome.PARSER_REJECTED: 4, TerminalOutcome.RETRY_PARSER_REJECTED: 5,
    TerminalOutcome.HOST_CAPABILITY_REJECTED: 6,
    TerminalOutcome.RETRY_HOST_CAPABILITY_REJECTED: 7, TerminalOutcome.NO_MESSAGE: 8,
}
_EFFECT: Final[dict[Effect, int]] = {Effect.NONE: 0, Effect.DELIVERED: 1, Effect.CANCELLED: 2}
_PARSE: Final[dict[ParseOutcome, int]] = {
    ParseOutcome.NOT_ATTEMPTED: 0, ParseOutcome.PARSER_ACCEPT: 1,
    ParseOutcome.PARSER_REJECT: 2, ParseOutcome.HOST_CAPABILITY_REJECT: 3,
}
_SCHEMA: Final[dict[QueuedSchema, int]] = {QueuedSchema.EMPTY: EMPTY, QueuedSchema.V1: V1, QueuedSchema.V2: V2}
# Independently rechecked against the pinned real parser by check_migration.
_ACCEPTING_WORDS: Final[tuple[int, ...]] = (73, 75, 77, 78, 79, 81, 83, 85, 86, 87, 97, 99, 101, 103)


@dataclass(frozen=True, slots=True)
class SignalGraphEssoCheck:
    """Result of independent finite supplied-IR/runtime parity."""

    model_sha256: str
    mode: CandidateMode
    code: str
    evidence: Evidence
    verified: bool
    model_matches: bool
    checked_guard_rows: int
    checked_states: int
    runtime_code: str
    runtime_edges: int
    source_sha256: tuple[tuple[str, str], ...]
    authority: str = "NONE"


class _IrInvalid(ValueError):
    pass


class _IrMismatch(ValueError):
    pass


def _canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _hash(value: object) -> str:
    try:
        return hashlib.sha256(_canonical(value)).hexdigest()
    except (TypeError, ValueError, RecursionError):
        return ""


def _graph_current() -> bool:
    try:
        return hashlib.sha256(_GRAPH_SOURCE_FILE.read_bytes()).hexdigest() == _PINNED_GRAPH_SHA256
    except OSError:
        return False


def _sources(pairs: tuple[tuple[str, str], ...]) -> tuple[tuple[str, str], ...]:
    return tuple(sorted((*pairs, (_GRAPH_SOURCE_PATH, _PINNED_GRAPH_SHA256))))


def _mapping(value: object) -> Mapping[str, object]:
    if type(value) is not dict:
        raise _IrInvalid("mapping")
    return value


def _expr_key(expr: Mapping[str, object]) -> tuple[object, ...]:
    if "var" in expr:
        return ("var", expr["var"])
    if "param" in expr:
        return ("param", expr["param"])
    if "const" in expr:
        return ("const", expr["const"])
    if "bool" in expr:
        return ("bool", expr["bool"])
    if expr.get("op") == "ite":
        return ("ite", _expr_key(_mapping(expr["cond"])), _expr_key(_mapping(expr["then"])), _expr_key(_mapping(expr["else"])))
    args = expr.get("args")
    if type(args) is not list:
        raise _IrInvalid("expr_args")
    return ("op", expr.get("op"), tuple(_expr_key(_mapping(arg)) for arg in args))


def _var(name: str) -> dict[str, object]:
    return {"var": name}


def _param(name: str) -> dict[str, object]:
    return {"param": name}


def _const(value: int) -> dict[str, object]:
    return {"const": value}


def _bool(value: bool) -> dict[str, object]:
    return {"bool": value}


def _canon(expr: Mapping[str, object]) -> dict[str, object]:
    if any(key in expr for key in ("var", "param", "const", "bool")):
        return dict(expr)
    if expr.get("op") == "ite":
        return _ite(_mapping(expr["cond"]), _mapping(expr["then"]), _mapping(expr["else"]))
    op, args = expr.get("op"), expr.get("args")
    if type(op) is not str or type(args) is not list:
        raise _IrInvalid("expr")
    return _op(op, *(_mapping(arg) for arg in args))


def _op(name: str, *args: Mapping[str, object]) -> dict[str, object]:
    if name == "not":
        if len(args) != 1:
            raise _IrInvalid("arity")
    elif len(args) < 2:
        raise _IrInvalid("arity")
    values = [_canon(arg) for arg in args]
    if name in {"and", "or", "xor", "+", "*", "min", "max", "=", "!="}:
        values.sort(key=_expr_key)
    return {"op": name, "args": values}


def _not(value: Mapping[str, object]) -> dict[str, object]:
    return _op("not", value)


def _ite(cond: Mapping[str, object], then: Mapping[str, object], otherwise: Mapping[str, object]) -> dict[str, object]:
    return {"op": "ite", "cond": _canon(cond), "then": _canon(then), "else": _canon(otherwise)}


def _eq(left: Mapping[str, object], right: Mapping[str, object]) -> dict[str, object]:
    return _op("=", left, right)


def _neq(left: Mapping[str, object], right: Mapping[str, object]) -> dict[str, object]:
    return _op("!=", left, right)


def _and(*values: Mapping[str, object]) -> dict[str, object]:
    return _canon(values[0]) if len(values) == 1 else _op("and", *values)


def _or(*values: Mapping[str, object]) -> dict[str, object]:
    return _canon(values[0]) if len(values) == 1 else _op("or", *values)


def _schema(producer: Mapping[str, object]) -> dict[str, object]:
    return _ite(_eq(producer, _const(P1)), _const(V1), _const(V2))


def _supports(consumer: Mapping[str, object], schema: Mapping[str, object]) -> dict[str, object]:
    return _or(
        _eq(schema, _const(EMPTY)), _eq(consumer, _const(DUAL)),
        _and(_eq(consumer, _const(COLD)), _eq(schema, _const(V1))),
        _and(_eq(consumer, _const(NEW)), _eq(schema, _const(V2))),
    )


def _compatibility(producer: Mapping[str, object], consumer: Mapping[str, object], schema: Mapping[str, object]) -> dict[str, object]:
    return _and(_supports(consumer, _schema(producer)), _supports(consumer, schema))


def _canonical_queue(schema: Mapping[str, object], word: Mapping[str, object]) -> dict[str, object]:
    return _or(_neq(schema, _const(EMPTY)), _eq(word, _const(0)))


def _invariant(producer: Mapping[str, object], consumer: Mapping[str, object], schema: Mapping[str, object], word: Mapping[str, object]) -> dict[str, object]:
    return _and(_compatibility(producer, consumer, schema), _canonical_queue(schema, word))


def _accepts(word: Mapping[str, object]) -> dict[str, object]:
    return _or(*(_eq(word, _const(value)) for value in _ACCEPTING_WORDS))


def _word_bool(word: Mapping[str, object], divisor: int) -> dict[str, object]:
    return _eq(_op("mod", _op("div", word, _const(divisor)), _const(2)), _const(1))


def _bool_state(value: Mapping[str, object]) -> dict[str, object]:
    return _ite(value, _const(2), _const(1))


def _cases(branches: tuple[tuple[Mapping[str, object], Mapping[str, object]], ...], default: Mapping[str, object]) -> dict[str, object]:
    result = _canon(default)
    for condition, value in reversed(branches):
        result = _ite(condition, value, result)
    return result

def _empty_effects(allowed: Mapping[str, object], code: Mapping[str, object]) -> dict[str, dict[str, object]]:
    return {
        "accepted": _canon(allowed), "auth_state": _const(0), "code": _canon(code),
        "effect": _const(_EFFECT[Effect.NONE]), "freshness_state": _const(0),
        "observation_schema": _const(EMPTY), "parse_outcome": _const(_PARSE[ParseOutcome.NOT_ATTEMPTED]),
        "terminal": _const(_TERMINAL[TerminalOutcome.NONE]),
    }


def _enqueue_effects(allowed: Mapping[str, object], code: Mapping[str, object], empty: Mapping[str, object], schema: Mapping[str, object], word: Mapping[str, object]) -> dict[str, dict[str, object]]:
    return {
        "accepted": _canon(allowed), "auth_state": _ite(empty, _bool_state(_word_bool(word, 2)), _const(0)),
        "code": _canon(code), "effect": _const(_EFFECT[Effect.NONE]),
        "freshness_state": _ite(empty, _bool_state(_word_bool(word, 4)), _const(0)),
        "observation_schema": _ite(empty, schema, _const(EMPTY)),
        "parse_outcome": _const(_PARSE[ParseOutcome.NOT_ATTEMPTED]), "terminal": _const(_TERMINAL[TerminalOutcome.NONE]),
    }


def _host_or_parser(nonempty: Mapping[str, object], readable: Mapping[str, object], accepts: Mapping[str, object]) -> dict[str, object]:
    return _cases(
        ((nonempty, _cases(((_not(readable), _const(_PARSE[ParseOutcome.HOST_CAPABILITY_REJECT])), (accepts, _const(_PARSE[ParseOutcome.PARSER_ACCEPT]))), _const(_PARSE[ParseOutcome.PARSER_REJECT]))),),
        _const(_PARSE[ParseOutcome.NOT_ATTEMPTED]),
    )


def _cancel_effects(allowed: Mapping[str, object], code: Mapping[str, object], empty: Mapping[str, object], schema: Mapping[str, object], word: Mapping[str, object], consumer: Mapping[str, object]) -> dict[str, dict[str, object]]:
    nonempty = _not(empty)
    return {
        "accepted": _canon(allowed), "auth_state": _ite(nonempty, _bool_state(_word_bool(word, 2)), _const(0)),
        "code": _canon(code), "effect": _ite(allowed, _const(_EFFECT[Effect.CANCELLED]), _const(_EFFECT[Effect.NONE])),
        "freshness_state": _ite(nonempty, _bool_state(_word_bool(word, 4)), _const(0)),
        "observation_schema": _ite(nonempty, schema, _const(EMPTY)),
        "parse_outcome": _host_or_parser(nonempty, _supports(consumer, schema), _accepts(word)),
        "terminal": _cases(((empty, _const(_TERMINAL[TerminalOutcome.NO_MESSAGE])), (allowed, _const(_TERMINAL[TerminalOutcome.CANCELLED]))), _const(_TERMINAL[TerminalOutcome.NONE])),
    }


def _delivery_terminal(action: Action, empty: Mapping[str, object], readable_or_safe: Mapping[str, object], accepts: Mapping[str, object], host_visible: bool) -> dict[str, object]:
    delivered = TerminalOutcome.RETRIED_DELIVERED if action is Action.RETRY else TerminalOutcome.DELIVERED
    parser_rejected = TerminalOutcome.RETRY_PARSER_REJECTED if action is Action.RETRY else TerminalOutcome.PARSER_REJECTED
    host_rejected = TerminalOutcome.RETRY_HOST_CAPABILITY_REJECTED if action is Action.RETRY else TerminalOutcome.HOST_CAPABILITY_REJECTED
    failed_guard = _const(_TERMINAL[host_rejected if host_visible else TerminalOutcome.NONE])
    return _cases(
        ((empty, _const(_TERMINAL[TerminalOutcome.NO_MESSAGE])), (_not(readable_or_safe), failed_guard), (accepts, _const(_TERMINAL[delivered]))),
        _const(_TERMINAL[parser_rejected]),
    )


def _delivery_effects(allowed: Mapping[str, object], code: Mapping[str, object], empty: Mapping[str, object], schema: Mapping[str, object], word: Mapping[str, object], outcome: Mapping[str, object], terminal: Mapping[str, object]) -> dict[str, dict[str, object]]:
    nonempty = _not(empty)
    return {
        "accepted": _canon(allowed), "auth_state": _ite(nonempty, _bool_state(_word_bool(word, 2)), _const(0)),
        "code": _canon(code), "effect": _ite(allowed, _const(_EFFECT[Effect.DELIVERED]), _const(_EFFECT[Effect.NONE])),
        "freshness_state": _ite(nonempty, _bool_state(_word_bool(word, 4)), _const(0)),
        "observation_schema": _ite(nonempty, schema, _const(EMPTY)), "parse_outcome": _canon(outcome), "terminal": _canon(terminal),
    }


def _action_record(action: Action, mode: CandidateMode) -> dict[str, object]:
    producer, consumer, schema, queued_word = map(_var, (P, C, Q, W))
    empty, nonempty = _eq(schema, _const(EMPTY)), _neq(schema, _const(EMPTY))
    current_safe = _invariant(producer, consumer, schema, queued_word)
    params: list[dict[str, object]] = []
    updates: dict[str, dict[str, object]] = {}
    effects: dict[str, dict[str, object]]

    if action is Action.UPGRADE_CONSUMER:
        target = _ite(_eq(consumer, _const(COLD)), _const(DUAL), _const(NEW))
        operational = _neq(consumer, _const(NEW))
        allowed = operational if mode is CandidateMode.UNGUARDED else _and(operational, _invariant(producer, target, schema, queued_word))
        updates[C] = _ite(allowed, target, consumer)
        code = _cases(((_eq(consumer, _const(NEW)), _const(_CODE[TransitionCode.CONSUMER_ALREADY_NEW])), (allowed, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _empty_effects(allowed, code)
    elif action is Action.ROLLBACK_CONSUMER:
        target = _ite(_eq(consumer, _const(DUAL)), _const(COLD), _const(DUAL))
        operational = _neq(consumer, _const(COLD))
        allowed = operational if mode is CandidateMode.UNGUARDED else _and(operational, _invariant(producer, target, schema, queued_word))
        updates[C] = _ite(allowed, target, consumer)
        code = _cases(((_eq(consumer, _const(COLD)), _const(_CODE[TransitionCode.CONSUMER_ALREADY_OLD])), (allowed, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _empty_effects(allowed, code)
    elif action is Action.UPGRADE_PRODUCER:
        operational = _eq(producer, _const(P1))
        allowed = operational if mode is CandidateMode.UNGUARDED else _and(operational, _invariant(_const(P2), consumer, schema, queued_word))
        updates[P] = _ite(allowed, _const(P2), producer)
        code = _cases(((_eq(producer, _const(P2)), _const(_CODE[TransitionCode.PRODUCER_ALREADY_V2])), (allowed, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _empty_effects(allowed, code)
    elif action is Action.ROLLBACK_PRODUCER:
        operational = _eq(producer, _const(P2))
        allowed = operational if mode is CandidateMode.UNGUARDED else _and(operational, _invariant(_const(P1), consumer, schema, queued_word))
        updates[P] = _ite(allowed, _const(P1), producer)
        code = _cases(((_eq(producer, _const(P1)), _const(_CODE[TransitionCode.PRODUCER_ALREADY_V1])), (allowed, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _empty_effects(allowed, code)
    elif action is Action.ENQUEUE:
        word, target_schema = _param("word"), _schema(producer)
        params = [{"id": "word", "type": {"kind": "int", "min": 0, "max": 127}}]
        allowed = empty if mode is CandidateMode.UNGUARDED else _and(empty, _invariant(producer, consumer, target_schema, word))
        updates[Q], updates[W] = _ite(allowed, target_schema, schema), _ite(allowed, word, queued_word)
        code = _cases(((nonempty, _const(_CODE[TransitionCode.QUEUE_FULL])), (allowed, _const(_CODE[TransitionCode.ENQUEUED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _enqueue_effects(allowed, code, empty, target_schema, word)
    elif action is Action.CANCEL:
        allowed = nonempty if mode is CandidateMode.UNGUARDED else _and(nonempty, _invariant(producer, consumer, _const(EMPTY), _const(0)))
        updates[Q], updates[W] = _ite(allowed, _const(EMPTY), schema), _ite(allowed, _const(0), queued_word)
        code = _cases(((empty, _const(_CODE[TransitionCode.QUEUE_EMPTY])), (allowed, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.GUARD_REJECTED]))
        effects = _cancel_effects(allowed, code, empty, schema, queued_word, consumer)
    elif action in (Action.DELIVER, Action.RETRY):
        accepts, readable = _accepts(queued_word), _supports(consumer, schema)
        if mode is CandidateMode.GUARDED:
            allowed = _and(nonempty, current_safe, accepts)
            code = _cases(((empty, _const(_CODE[TransitionCode.QUEUE_EMPTY])), (_not(current_safe), _const(_CODE[TransitionCode.GUARD_REJECTED])), (accepts, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.ACTUAL_PARSER_REJECTED]))
            outcome = _cases(((empty, _const(_PARSE[ParseOutcome.NOT_ATTEMPTED])), (_not(current_safe), _const(_PARSE[ParseOutcome.NOT_ATTEMPTED])), (accepts, _const(_PARSE[ParseOutcome.PARSER_ACCEPT]))), _const(_PARSE[ParseOutcome.PARSER_REJECT]))
            terminal = _delivery_terminal(action, empty, current_safe, accepts, False)
        else:
            allowed = _and(nonempty, readable, accepts)
            code = _cases(((empty, _const(_CODE[TransitionCode.QUEUE_EMPTY])), (_not(readable), _const(_CODE[TransitionCode.HOST_CAPABILITY_REJECTED])), (accepts, _const(_CODE[TransitionCode.APPLIED]))), _const(_CODE[TransitionCode.ACTUAL_PARSER_REJECTED]))
            outcome = _cases(((empty, _const(_PARSE[ParseOutcome.NOT_ATTEMPTED])), (_not(readable), _const(_PARSE[ParseOutcome.HOST_CAPABILITY_REJECT])), (accepts, _const(_PARSE[ParseOutcome.PARSER_ACCEPT]))), _const(_PARSE[ParseOutcome.PARSER_REJECT]))
            terminal = _delivery_terminal(action, empty, readable, accepts, True)
        updates[Q], updates[W] = _ite(allowed, _const(EMPTY), schema), _ite(allowed, _const(0), queued_word)
        effects = _delivery_effects(allowed, code, empty, schema, queued_word, outcome, terminal)
    else:  # pragma: no cover
        raise _IrInvalid("action")
    return {
        "id": action.value, "params": params, "guard": _bool(True),
        "updates": [{"var": name, "expr": updates[name]} for name in sorted(updates)],
        "effects": {name: effects[name] for name in sorted(effects)},
    }

def _exact_words(inputs: object) -> bool:
    return type(inputs) is tuple and all(type(word) is int for word in inputs) and inputs == _WORDS


def signal_graph_esso_model(mode: CandidateMode, inputs: tuple[int, ...] = _WORDS) -> dict[str, object]:
    """Generate canonical closed ESSO-IR for this bounded controller."""
    if type(mode) is not CandidateMode or not _exact_words(inputs):
        raise ValueError("invalid_signal_graph_domain")
    producer, consumer, schema, word = map(_var, (P, C, Q, W))
    return {
        "ir_version": "esso-ir/v1",
        "meta": {
            "authority": "NONE", "candidate_mode": mode.value,
            "model_id": "autotrader_real_signal_migration_" + mode.value.lower(),
            "notes": "One queued real V1/V2 fixed-metadata message; no settlement or release authority.",
        },
        "observables": {"state_vars": list(_STATE_VARIABLES), "effects": list(_EFFECTS)}, "types": [],
        "state_vars": [
            {"id": C, "role": "control", "type": {"kind": "int", "min": 0, "max": 2}},
            {"id": P, "role": "control", "type": {"kind": "int", "min": 0, "max": 1}},
            {"id": Q, "role": "control", "type": {"kind": "int", "min": 0, "max": 2}},
            {"id": W, "role": "data", "type": {"kind": "int", "min": 0, "max": 127}},
        ],
        "invariants": [
            {"id": "active_and_queued_schema_supported", "kind": "safety", "expr": _compatibility(producer, consumer, schema)},
            {"id": "empty_queue_word_canonical", "kind": "canonical", "expr": _canonical_queue(schema, word)},
        ],
        "init": [
            {"var": C, "expr": _const(COLD)}, {"var": P, "expr": _const(P1)},
            {"var": Q, "expr": _const(EMPTY)}, {"var": W, "expr": _const(0)},
        ],
        "actions": [_action_record(action, mode) for action in sorted(Action, key=lambda item: item.value)],
        "refinement": {
            "guard_evaluation": "independent finite evaluator compares supplied guards and updates to mounted runtime transitions",
            "retained_effects": list(_EFFECTS), "retained_state_vars": list(_STATE_VARIABLES),
            "discarded_runtime_observations": list(_DISCARDED),
            "discard_reason": "exact normalized parser result and diagnostics are source-pinned port observations replayed over all 128 words",
        },
    }


def _require(condition: bool, code: str) -> None:
    if not condition:
        raise _IrInvalid(code)


def _closed(value: object, fields: frozenset[str], code: str) -> dict[str, object]:
    _require(type(value) is dict and set(value) == fields, code)
    return cast(dict[str, object], value)


_ExprFn = Callable[[Mapping[str, int], Mapping[str, int]], int | bool]


@dataclass(frozen=True, slots=True)
class _CompiledExpr:
    kind: str
    run: _ExprFn


@dataclass(frozen=True, slots=True)
class _CompiledAction:
    guard: _CompiledExpr
    updates: tuple[tuple[str, _CompiledExpr], ...]
    effects: tuple[tuple[str, _CompiledExpr], ...]


def _state_expr(name: str) -> _ExprFn:
    def run(state: Mapping[str, int], _params: Mapping[str, int]) -> int:
        return state[name]

    return run


def _param_expr(name: str) -> _ExprFn:
    def run(_state: Mapping[str, int], params: Mapping[str, int]) -> int:
        return params[name]

    return run


def _int_literal(value: int) -> _ExprFn:
    def run(_state: Mapping[str, int], _params: Mapping[str, int]) -> int:
        return value

    return run


def _bool_literal(value: bool) -> _ExprFn:
    def run(_state: Mapping[str, int], _params: Mapping[str, int]) -> bool:
        return value

    return run


def _integer_operation(left: int | bool, right: int | bool, operator: str) -> int:
    if type(left) is not int or type(right) is not int or right == 0:
        raise _IrInvalid("arithmetic_runtime")
    return left // right if operator == "div" else left % right


def _compile_expr(expr: object, params: frozenset[str]) -> _CompiledExpr:
    """Type-check the closed expression vocabulary once, before enumeration."""

    value = _mapping(expr)
    keys = frozenset(value)
    if keys == {"var"}:
        name = value["var"]
        _require(type(name) is str and name in _STATE_VARIABLES, "var")
        return _CompiledExpr("int", _state_expr(cast(str, name)))
    if keys == {"param"}:
        name = value["param"]
        _require(type(name) is str and name in params, "param")
        return _CompiledExpr("int", _param_expr(cast(str, name)))
    if keys == {"const"}:
        literal = value["const"]
        _require(type(literal) is int, "const")
        return _CompiledExpr("int", _int_literal(cast(int, literal)))
    if keys == {"bool"}:
        literal = value["bool"]
        _require(type(literal) is bool, "bool")
        return _CompiledExpr("bool", _bool_literal(cast(bool, literal)))
    if value.get("op") == "ite":
        _require(keys == {"op", "cond", "then", "else"}, "ite_shape")
        condition = _compile_expr(value["cond"], params)
        then_value = _compile_expr(value["then"], params)
        else_value = _compile_expr(value["else"], params)
        _require(condition.kind == "bool" and then_value.kind == else_value.kind, "ite_type")
        return _CompiledExpr(
            then_value.kind,
            lambda state, values: then_value.run(state, values) if condition.run(state, values) else else_value.run(state, values),
        )
    _require(keys == {"op", "args"}, "op_shape")
    operator, raw_args = value["op"], value["args"]
    _require(type(operator) is str and type(raw_args) is list, "op")
    arguments = tuple(_compile_expr(argument, params) for argument in cast(list[object], raw_args))
    if operator in {"and", "or"}:
        _require(len(arguments) >= 2 and all(argument.kind == "bool" for argument in arguments), "boolean")
        if operator == "and":
            return _CompiledExpr("bool", lambda state, values: all(argument.run(state, values) for argument in arguments))
        return _CompiledExpr("bool", lambda state, values: any(argument.run(state, values) for argument in arguments))
    if operator == "not":
        _require(len(arguments) == 1 and arguments[0].kind == "bool", "not")
        return _CompiledExpr("bool", lambda state, values: not arguments[0].run(state, values))
    if operator in {"=", "!="}:
        _require(len(arguments) == 2 and arguments[0].kind == arguments[1].kind, "equality")
        if operator == "=":
            return _CompiledExpr("bool", lambda state, values: arguments[0].run(state, values) == arguments[1].run(state, values))
        return _CompiledExpr("bool", lambda state, values: arguments[0].run(state, values) != arguments[1].run(state, values))
    if operator in {"div", "mod"}:
        _require(len(arguments) == 2 and all(argument.kind == "int" for argument in arguments), "arithmetic")
        if operator == "div":
            return _CompiledExpr("int", lambda state, values: _integer_operation(arguments[0].run(state, values), arguments[1].run(state, values), "div"))
        return _CompiledExpr("int", lambda state, values: _integer_operation(arguments[0].run(state, values), arguments[1].run(state, values), "mod"))
    raise _IrInvalid("operator")


def _compile_action(raw: Mapping[str, object], action: Action) -> _CompiledAction:
    expected_params = [{"id": "word", "type": {"kind": "int", "min": 0, "max": 127}}] if action is Action.ENQUEUE else []
    _require(raw["params"] == expected_params, "params_shape")
    params = frozenset({"word"} if action is Action.ENQUEUE else ())
    guard = _compile_expr(raw["guard"], params)
    _require(guard.kind == "bool", "guard_type")
    raw_updates = raw["updates"]
    _require(type(raw_updates) is list, "updates")
    updates: list[tuple[str, _CompiledExpr]] = []
    seen: set[str] = set()
    for raw_update in cast(list[object], raw_updates):
        _require(type(raw_update) is dict and set(raw_update) == {"var", "expr"}, "update_shape")
        update = cast(dict[str, object], raw_update)
        variable = update["var"]
        _require(type(variable) is str and variable in _STATE_VARIABLES and variable not in seen, "update_var")
        variable = cast(str, variable)
        compiled = _compile_expr(update["expr"], params)
        _require(compiled.kind == "int", "update_type")
        seen.add(variable)
        updates.append((variable, compiled))
    raw_effects = raw["effects"]
    _require(type(raw_effects) is dict and set(raw_effects) == set(_EFFECTS), "effect_shape")
    effects: list[tuple[str, _CompiledExpr]] = []
    for name in _EFFECTS:
        compiled = _compile_expr(cast(dict[str, object], raw_effects)[name], params)
        _require(compiled.kind == ("bool" if name == "accepted" else "int"), "effect_type")
        effects.append((name, compiled))
    return _CompiledAction(guard, tuple(updates), tuple(effects))


def _parse_model(model: object, mode: CandidateMode) -> tuple[dict[str, dict[str, object]], dict[str, dict[str, object]]]:
    value = _closed(model, _TOP_FIELDS, "top_fields")
    _require(value["ir_version"] == "esso-ir/v1", "ir_version")
    meta, observables = value["meta"], value["observables"]
    _require(type(meta) is dict and meta.get("authority") == "NONE" and meta.get("candidate_mode") == mode.value, "meta")
    _require(type(observables) is dict and observables.get("state_vars") == list(_STATE_VARIABLES) and observables.get("effects") == list(_EFFECTS), "observables")
    _require(value["types"] == [], "types")
    expected_vars = [
        {"id": C, "role": "control", "type": {"kind": "int", "min": 0, "max": 2}},
        {"id": P, "role": "control", "type": {"kind": "int", "min": 0, "max": 1}},
        {"id": Q, "role": "control", "type": {"kind": "int", "min": 0, "max": 2}},
        {"id": W, "role": "data", "type": {"kind": "int", "min": 0, "max": 127}},
    ]
    _require(value["state_vars"] == expected_vars, "state_vars")
    _require(value["init"] == [{"var": C, "expr": {"const": COLD}}, {"var": P, "expr": {"const": P1}}, {"var": Q, "expr": {"const": EMPTY}}, {"var": W, "expr": {"const": 0}}], "init")
    refinement = value["refinement"]
    if type(refinement) is not dict:
        raise _IrInvalid("refinement_state")
    _require(refinement.get("retained_state_vars") == list(_STATE_VARIABLES), "refinement_state")
    _require(refinement.get("retained_effects") == list(_EFFECTS) and refinement.get("discarded_runtime_observations") == list(_DISCARDED), "refinement_effects")
    raw_invariants = value["invariants"]
    if type(raw_invariants) is not list or len(raw_invariants) != 2:
        raise _IrInvalid("invariants")
    invariants: dict[str, dict[str, object]] = {}
    for item in raw_invariants:
        _require(type(item) is dict and type(item.get("id")) is str and item["id"] not in invariants, "invariant_item")
        _require(item.get("kind") in {"safety", "canonical"} and type(item.get("expr")) is dict, "invariant_shape")
        invariants[item["id"]] = item
    _require(set(invariants) == {"active_and_queued_schema_supported", "empty_queue_word_canonical"}, "invariant_ids")
    raw_actions = value["actions"]
    if type(raw_actions) is not list or len(raw_actions) != len(Action):
        raise _IrInvalid("actions")
    actions: dict[str, dict[str, object]] = {}
    for item in raw_actions:
        _require(type(item) is dict and type(item.get("id")) is str and item["id"] not in actions, "action_item")
        _require(type(item.get("params")) is list and type(item.get("guard")) is dict and type(item.get("updates")) is list and type(item.get("effects")) is dict, "action_shape")
        actions[item["id"]] = item
    _require(set(actions) == {action.value for action in Action}, "action_ids")
    return invariants, actions

def _raw_states() -> tuple[dict[str, int], ...]:
    return tuple({P: producer, C: consumer, Q: schema, W: word} for producer in range(2) for consumer in range(3) for schema in range(3) for word in _WORDS)


def _canonical_states() -> tuple[State, ...]:
    states: list[State] = []
    for producer in ProducerVersion:
        for consumer in ConsumerCapability:
            states.append(State(producer, consumer))
            for schema in (QueuedSchema.V1, QueuedSchema.V2):
                states.extend(State(producer, consumer, schema, word) for word in _WORDS)
    return tuple(states)


def _state_row(state: State) -> dict[str, int]:
    return {
        P: P1 if state.producer is ProducerVersion.V1 else P2,
        C: {ConsumerCapability.OLD: COLD, ConsumerCapability.DUAL: DUAL, ConsumerCapability.NEW: NEW}[state.consumer],
        Q: _SCHEMA[state.queued_schema], W: 0 if state.queued_word is None else state.queued_word,
    }


def _expected_invariants(row: Mapping[str, int]) -> tuple[bool, bool]:
    schema, word = row[Q], row[W]
    producer = ProducerVersion.V1 if row[P] == P1 else ProducerVersion.V2
    consumer = (ConsumerCapability.OLD, ConsumerCapability.DUAL, ConsumerCapability.NEW)[row[C]]
    state = State(producer, consumer) if schema == EMPTY else State(producer, consumer, QueuedSchema.V1 if schema == V1 else QueuedSchema.V2, word)
    return controller_invariant(state), schema != EMPTY or word == 0


def _params(action: Action, word: int) -> dict[str, int]:
    return {"word": word} if action is Action.ENQUEUE else {}


def _eval_action(action: _CompiledAction, state: Mapping[str, int], params: Mapping[str, int]) -> tuple[dict[str, int], dict[str, int | bool]]:
    _require(action.guard.run(state, params) is True, "guard_not_total")
    post = dict(state)
    for variable, update in action.updates:
        result = update.run(state, params)
        _require(type(result) is int, "update_value")
        post[variable] = result
    _require(0 <= post[P] <= 1 and 0 <= post[C] <= 2 and 0 <= post[Q] <= 2 and 0 <= post[W] <= 127, "post_domain")
    effects: dict[str, int | bool] = {}
    for name, effect in action.effects:
        result = effect.run(state, params)
        _require(type(result) is bool if name == "accepted" else type(result) is int, "effect_type")
        effects[name] = result
    return post, effects


def _transition_effects(transition: Transition) -> dict[str, int | bool]:
    observation = transition.observation
    return {
        "accepted": transition.accepted,
        "auth_state": 0 if observation.auth_ok is None else (2 if observation.auth_ok else 1),
        "code": _CODE[transition.code], "effect": _EFFECT[transition.effect],
        "freshness_state": 0 if observation.freshness_ok is None else (2 if observation.freshness_ok else 1),
        "observation_schema": _SCHEMA[observation.schema], "parse_outcome": _PARSE[observation.outcome],
        "terminal": _TERMINAL[transition.terminal],
    }


def _verify_semantics(model: object, mode: CandidateMode) -> tuple[int, int]:
    invariants, raw_actions = _parse_model(model, mode)
    compatibility = _compile_expr(invariants["active_and_queued_schema_supported"]["expr"], frozenset())
    canonical = _compile_expr(invariants["empty_queue_word_canonical"]["expr"], frozenset())
    _require(compatibility.kind == "bool" and canonical.kind == "bool", "invariant_type")
    actions = {action: _compile_action(raw_actions[action.value], action) for action in Action}
    for row in _raw_states():
        expected_compatibility, expected_canonical = _expected_invariants(row)
        if compatibility.run(row, {}) is not expected_compatibility or canonical.run(row, {}) is not expected_canonical:
            raise _IrMismatch("invariant_relation")
    states, edges = _canonical_states(), 0
    runtime_step = safe_transition if mode is CandidateMode.GUARDED else unsafe_transition
    for state in states:
        row = _state_row(state)
        for action in Action:
            for word in (_WORDS if action is Action.ENQUEUE else (0,)):
                supplied_post, supplied_effects = _eval_action(actions[action], row, _params(action, word))
                runtime = runtime_step(state, action, word)
                if supplied_post != _state_row(runtime.post_state) or supplied_effects != _transition_effects(runtime):
                    raise _IrMismatch("transition_relation")
                edges += 1
    return len(states), edges


def _result(model: object, mode: CandidateMode, code: str, evidence: Evidence, verified: bool, matches: bool, rows: int = 0, states: int = 0, runtime_code: str = "NOT_RUN", runtime_edges: int = 0, pairs: tuple[tuple[str, str], ...] = ()) -> SignalGraphEssoCheck:
    return SignalGraphEssoCheck(_hash(model), mode, code, evidence, verified, matches, rows, states, runtime_code, runtime_edges, pairs)


def verify_signal_graph_esso(model: object, mode: CandidateMode, inputs: tuple[int, ...] = _WORDS) -> SignalGraphEssoCheck:
    """Independently evaluate supplied ESSO IR over its complete finite domain.

    It evaluates 2,304 raw IR states for the named invariants and 208,170
    canonical controller edges, including rejected no-op calls and effects.
    The exact normalized parser result remains checked by the source-pinned
    128-word runtime projection after this relation parity succeeds.
    """
    if type(mode) is not CandidateMode or not _exact_words(inputs):
        return _result(model, mode, "INVALID_GRAPH_DOMAIN", Evidence.UNKNOWN, False, False)
    if not _graph_current():
        return _result(model, mode, "ESSO_GRAPH_SOURCE_SNAPSHOT_CHANGED", Evidence.UNKNOWN, False, False)
    try:
        states, edges = _verify_semantics(model, mode)
    except _IrInvalid:
        return _result(model, mode, "ESSO_IR_INVALID", Evidence.UNKNOWN, False, False)
    except _IrMismatch:
        return _result(model, mode, "ESSO_GRAPH_RUNTIME_MISMATCH", Evidence.UNKNOWN, False, False)
    if not _graph_current():
        return _result(model, mode, "ESSO_GRAPH_SOURCE_SNAPSHOT_CHANGED", Evidence.UNKNOWN, False, True, edges, states)
    runtime = check_migration(mode=mode, inputs=inputs, declared_observations=OBSERVATIONS)
    if not _graph_current():
        return _result(model, mode, "ESSO_GRAPH_SOURCE_SNAPSHOT_CHANGED", Evidence.UNKNOWN, False, True, edges, states, runtime.code, runtime.checked_edges)
    pairs = _sources(runtime.source_sha256)
    if runtime.evidence is not Evidence.EXHAUSTIVE_FINITE:
        return _result(model, mode, "ESSO_GRAPH_RUNTIME_UNKNOWN", Evidence.UNKNOWN, False, True, edges, states, runtime.code, runtime.checked_edges, pairs)
    if mode is CandidateMode.GUARDED and runtime.code == "SIGNAL_MIGRATION_CHECKED":
        return _result(model, mode, "ESSO_GRAPH_RUNTIME_PARITY", Evidence.EXHAUSTIVE_FINITE, True, True, edges, states, runtime.code, runtime.checked_edges, pairs)
    return _result(model, mode, "ESSO_GRAPH_UNSAFE_COUNTEREXAMPLE", Evidence.EXHAUSTIVE_FINITE, False, True, edges, states, runtime.code, runtime.checked_edges, pairs)


__all__ = ["SignalGraphEssoCheck", "signal_graph_esso_model", "verify_signal_graph_esso"]
