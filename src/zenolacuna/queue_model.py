"""Complete finite queue model and maximal one-step invariant guard.

The alpha map retains producer/consumer/message versions and queue occupancy.
Its codec premise must separately be checked over every concrete byte value.
All actions in this model pass through the declared admission guard.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, replace
from enum import Enum
from itertools import product

from .model import LacunaError, exact_int


class QueueAction(str, Enum):
    PRODUCER_OLD = "producer_old"
    PRODUCER_NEW = "producer_new"
    CONSUMER_OLD = "consumer_old"
    CONSUMER_NEW = "consumer_new"
    ENQUEUE = "enqueue"
    DELIVER = "deliver"
    CANCEL = "cancel"
    RETRY = "retry"


class Admission(str, Enum):
    UNGUARDED = "UNGUARDED"
    PRESERVE_DECODING = "PRESERVE_DECODING"


@dataclass(frozen=True, slots=True)
class QueueState:
    producer: int = 0
    consumer: int = 0
    queued: int = 0
    message_version: int = 0

    def __post_init__(self) -> None:
        for value in (self.producer, self.consumer, self.queued, self.message_version):
            exact_int(value, 0, 1)
        if self.queued == 0 and self.message_version != 0:
            raise LacunaError("NONCANONICAL_EMPTY_QUEUE")


@dataclass(frozen=True, slots=True)
class QueueStep:
    state: QueueState
    code: str
    delivered: int = 0


def preserves_decoding(state: QueueState) -> bool:
    return state.queued == 0 or state.message_version == state.consumer


def propose_step(state: QueueState, action: QueueAction) -> QueueStep:
    if type(state) is not QueueState or type(action) is not QueueAction:
        raise LacunaError("INVALID_QUEUE_INPUT")
    match action:
        case QueueAction.PRODUCER_OLD | QueueAction.PRODUCER_NEW:
            return QueueStep(replace(state, producer=int(action is QueueAction.PRODUCER_NEW)), "ACCEPT")
        case QueueAction.CONSUMER_OLD | QueueAction.CONSUMER_NEW:
            return QueueStep(replace(state, consumer=int(action is QueueAction.CONSUMER_NEW)), "ACCEPT")
        case QueueAction.ENQUEUE:
            if state.queued:
                return QueueStep(state, "QUEUE_FULL")
            return QueueStep(replace(state, queued=1, message_version=state.producer), "ACCEPT")
        case QueueAction.DELIVER | QueueAction.CANCEL:
            if not state.queued:
                return QueueStep(state, "NO_MESSAGE")
            delivered = int(action is QueueAction.DELIVER)
            code = "MISDECODE" if delivered and not preserves_decoding(state) else "ACCEPT"
            return QueueStep(replace(state, queued=0, message_version=0), code, delivered)
        case QueueAction.RETRY:
            return QueueStep(state, "ACCEPT")
    raise LacunaError("UNKNOWN_QUEUE_ACTION")


def queue_step(state: QueueState, action: QueueAction, admission: Admission) -> QueueStep:
    if type(admission) is not Admission:
        raise LacunaError("INVALID_ADMISSION")
    proposed = propose_step(state, action)
    if admission is Admission.PRESERVE_DECODING and (
        not preserves_decoding(proposed.state) or proposed.code == "MISDECODE"
    ):
        return QueueStep(state, "MIGRATION_REQUIRES_DRAIN_OR_MATCH")
    return proposed


@dataclass(frozen=True, slots=True)
class QueueAudit:
    admission: Admission
    states: int
    transitions: int
    invariant_violations: int
    misdecode_edges: int
    shortest_counterexample: tuple[str, ...]
    complete_graph: bool
    authority: str = "NONE"


def audit_queue(admission: Admission, *, max_states: int = 32) -> QueueAudit:
    exact_int(max_states, 1, 32)
    initial = QueueState()
    paths: dict[QueueState, tuple[str, ...]] = {initial: ()}
    pending = deque([initial])
    edges = violations = misdecodes = 0
    witness: tuple[str, ...] = ()
    while pending:
        state = pending.popleft()
        for action in QueueAction:
            step = queue_step(state, action, admission)
            edges += 1
            misdecodes += int(step.code == "MISDECODE")
            if not preserves_decoding(step.state):
                violations += 1
                if not witness:
                    witness = paths[state] + (action.value,)
            if step.state not in paths:
                if len(paths) >= max_states:
                    return QueueAudit(admission, len(paths), edges, violations, misdecodes, witness, False)
                paths[step.state] = paths[state] + (action.value,)
                pending.append(step.state)
    return QueueAudit(admission, len(paths), edges, violations, misdecodes, witness, True)


def guard_table() -> tuple[tuple[QueueState, tuple[QueueAction, ...]], ...]:
    """All safe initial states and all legal steps retaining the invariant."""
    result = []
    for p, c, q, v in product(range(2), repeat=4):
        if q == 0 and v != 0:
            continue
        state = QueueState(p, c, q, v)
        if not preserves_decoding(state):
            continue
        allowed = tuple(action for action in QueueAction
                        if queue_step(state, action, Admission.PRESERVE_DECODING).code == "ACCEPT")
        result.append((state, allowed))
    return tuple(result)


def esso_model(admission: Admission) -> dict[str, object]:
    """Generate ESSO-IR from explicit abstract transition equations for parity checking."""
    def var(name: str) -> dict:
        return {"var": name}

    def const(value: int) -> dict:
        return {"const": value}

    def op(name: str, *args: dict) -> dict:
        return {"op": name, "args": list(args)}

    def eq(left: dict, right: dict) -> dict:
        return op("=", left, right)

    empty, full = eq(var("queued"), const(0)), eq(var("queued"), const(1))
    matching = eq(var("message_version"), var("consumer"))
    invariant = op("or", empty, matching)
    guarded = admission is Admission.PRESERVE_DECODING
    actions = []
    for action in QueueAction:
        updates: dict[str, dict] = {}
        guard: dict = {"bool": True}
        delivered = 0
        if action in (QueueAction.PRODUCER_OLD, QueueAction.PRODUCER_NEW):
            updates["producer"] = const(int(action is QueueAction.PRODUCER_NEW))
        elif action in (QueueAction.CONSUMER_OLD, QueueAction.CONSUMER_NEW):
            target = const(int(action is QueueAction.CONSUMER_NEW))
            updates["consumer"] = target
            if guarded:
                guard = op("or", empty, eq(var("message_version"), target))
        elif action is QueueAction.ENQUEUE:
            guard = op("and", empty, eq(var("producer"), var("consumer"))) if guarded else empty
            updates = {"queued": const(1), "message_version": var("producer")}
        elif action in (QueueAction.DELIVER, QueueAction.CANCEL):
            guard = op("and", full, matching) if guarded and action is QueueAction.DELIVER else full
            updates = {"queued": const(0), "message_version": const(0)}
            delivered = int(action is QueueAction.DELIVER)
        actions.append({"id": action.value, "params": [], "guard": guard,
                        "updates": [{"var": name, "expr": expr} for name, expr in updates.items()],
                        "effects": {"delivered": const(delivered)}})
    names = ("producer", "consumer", "queued", "message_version")
    return {
        "ir_version": "esso-ir/v1",
        "meta": {"model_id": "zenolacuna_queue_" + admission.value.lower(), "created_by": "zenolacuna",
                 "notes": "Single queued metadata message; all version actions pass through admission. No liveness claim."},
        "observables": {"state_vars": list(names), "effects": ["delivered"]}, "types": [],
        "state_vars": [{"id": name, "role": "control", "type": {"kind": "int", "min": 0, "max": 1}}
                       for name in names],
        "init": [{"var": name, "expr": const(0)} for name in names],
        "invariants": [
            {"id": "queued_message_remains_decodable", "kind": "safety", "expr": invariant},
            {"id": "empty_queue_is_canonical", "kind": "safety",
             "expr": op("or", full, eq(var("message_version"), const(0)))},
        ],
        "actions": actions,
    }
