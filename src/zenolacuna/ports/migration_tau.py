"""Tau preimage elimination for the real two-schema consumer migration guard."""

from src.tau_composition.runtime import TauRuntime

from ..model import LacunaError
from ..signal_migration import (
    ConsumerCapability,
    ProducerVersion,
    QueuedSchema,
    State,
    controller_invariant,
)


def project_consumer_guard(runtime: TauRuntime) -> dict[str, object]:
    """Eliminate post-consumer capabilities, then check the concrete truth table.

    p/v encode the new schema; q means occupied. a/b are the proposed reader's
    old/new capabilities. The guard protects both the next producer message
    and the already queued message. Host schema and parser observations remain
    checked by the finite runtime graph; this theorem is the compatibility part.
    """
    invariant = "(((p & cn) | (p' & co)) & (q' | (v & cn) | (v' & co))) = 1"
    query = f"ex co ex cn ((co = a) && (cn = b) && ({invariant}))"
    expected = "(((p & b) | (p' & a)) & (q' | (v & b) | (v' & a))) = 1"
    guard = runtime.project(query)
    if not runtime.valid(f"(({guard}) <-> ({expected}))"):
        raise LacunaError("SOLVER_DISAGREEMENT")
    checked = 0
    for producer in ProducerVersion:
        for consumer in ConsumerCapability:
            a = consumer in (ConsumerCapability.OLD, ConsumerCapability.DUAL)
            b = consumer in (ConsumerCapability.NEW, ConsumerCapability.DUAL)
            p = producer is ProducerVersion.V2
            for queued in QueuedSchema:
                q, v = queued is not QueuedSchema.EMPTY, queued is QueuedSchema.V2
                state = State(producer, consumer, queued, 0 if q else None)
                table = ((p and b) or (not p and a)) and (not q or (v and b) or (not v and a))
                if table != controller_invariant(state):
                    raise LacunaError("TAU_RUNTIME_GUARD_MISMATCH")
                checked += 1
    return {"code": "TAU_CONSUMER_GUARD_PROJECTED", "query": query, "guard": guard,
            "expected": expected, "checked_capability_states": checked,
            "binary_sha256": runtime.binary_sha256, "authority": "NONE"}
