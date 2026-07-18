"""State construction and serialization for `perp_v2` and the shared v4 ABI.

`initial_state()` returns the canonical initial state (matches the YAML `init`
block).  Wire decoding is exact for fields and primitive types.  Named phase
values remain an explicit compatibility input because the v2-to-v3 adapter
reconstructs that legacy field before entering the versioned core.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from ..perp_state_domain import state_domain_violations
from .types import EpochPhase, PerpState

# Auto-derived from PerpState field definitions (single source of truth).
STATE_VAR_NAMES: tuple[str, ...] = tuple(PerpState.__dataclass_fields__)
_STATE_VAR_NAME_SET = frozenset(STATE_VAR_NAMES)

_BOOL_STATE_VAR_NAMES = frozenset(
    {
        "breaker_active",
        "clearing_price_seen",
        "oracle_seen",
        "liquidated_this_step",
    }
)

_EPOCH_PHASE_INT_MAP: dict[int, EpochPhase] = {
    0: EpochPhase.OPEN,
    1: EpochPhase.PRICE_PUBLISHED,
    2: EpochPhase.SETTLED,
}

_EPOCH_PHASE_TO_INT: dict[EpochPhase, int] = {
    EpochPhase.OPEN: 0,
    EpochPhase.PRICE_PUBLISHED: 1,
    EpochPhase.SETTLED: 2,
}


def _coerce_epoch_phase(val: Any) -> EpochPhase:
    if type(val) is EpochPhase:
        return val
    if type(val) is str:
        return EpochPhase(val)
    if type(val) is int:
        if val in _EPOCH_PHASE_INT_MAP:
            return _EPOCH_PHASE_INT_MAP[val]
        raise ValueError(f"state var 'epoch_phase' int value {val} out of range [0,2]")
    raise TypeError(
        "state var 'epoch_phase' must be an exact EpochPhase, named legacy phase, "
        f"or canonical int, got {type(val).__name__}"
    )


def _coerce_state_bool(name: str, val: Any) -> bool:
    if type(val) is not bool:
        raise TypeError(
            f"state var {name!r} must be an exact bool, got {type(val).__name__}"
        )
    return val


def _coerce_state_int(name: str, val: Any) -> int:
    if type(val) is not int:
        raise TypeError(f"state var {name!r} must be an exact int, got {type(val).__name__}")
    return val


def initial_state() -> PerpState:
    """Return the canonical PerpState matching the YAML init block."""
    return PerpState()


def state_to_dict(state: PerpState) -> dict[str, bool | int | str]:
    """Serialize one exact domain-valid state to the canonical integer ABI."""
    violations = state_domain_violations(state)
    if violations:
        raise ValueError("invalid PerpState domain: " + ",".join(violations))

    encoded: dict[str, bool | int | str] = {}
    for name in STATE_VAR_NAMES:
        val = getattr(state, name)
        if type(val) is EpochPhase:
            encoded[name] = _EPOCH_PHASE_TO_INT[val]
        else:
            encoded[name] = val
    return encoded


def state_from_dict(d: Mapping[str, Any]) -> PerpState:
    """Deserialize an exact state object.

    The parser rejects unknown and missing fields before decoding.  Boolean
    fields require JSON booleans and integer fields reject Python booleans.
    Accepted output is always the exact frozen base value used by the core.
    """
    if not isinstance(d, Mapping):
        raise TypeError("perps state must be a mapping")
    obj = dict(d)
    actual = frozenset(obj)
    if actual != _STATE_VAR_NAME_SET:
        missing = sorted(_STATE_VAR_NAME_SET - actual)
        unknown = sorted(actual - _STATE_VAR_NAME_SET)
        raise ValueError(
            "perps state fields must match exactly "
            f"(missing={missing}, unknown={unknown})"
        )

    kwargs: dict[str, Any] = {}
    for name in STATE_VAR_NAMES:
        val = obj[name]
        if name == "epoch_phase":
            kwargs[name] = _coerce_epoch_phase(val)
        elif name in _BOOL_STATE_VAR_NAMES:
            kwargs[name] = _coerce_state_bool(name, val)
        else:
            kwargs[name] = _coerce_state_int(name, val)

    state = PerpState(**kwargs)
    domain_violations = state_domain_violations(state)
    if domain_violations:
        raise ValueError("invalid perps state domain: " + ",".join(domain_violations))
    return state
