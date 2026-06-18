"""State construction and serialization for `perp_v2`.

`initial_state()` returns the canonical initial state (matches the YAML `init` block).

Round-trip property (tested): `state_from_dict(state_to_dict(s)) == s` for all valid states.
"""

from __future__ import annotations

from typing import Any, Mapping

from .types import EpochPhase, PerpState

# Auto-derived from PerpState field definitions (single source of truth).
STATE_VAR_NAMES: tuple[str, ...] = tuple(PerpState.__dataclass_fields__)

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
    if isinstance(val, EpochPhase):
        return val
    if isinstance(val, str):
        return EpochPhase(val)
    if isinstance(val, int) and not isinstance(val, bool):
        if val in _EPOCH_PHASE_INT_MAP:
            return _EPOCH_PHASE_INT_MAP[val]
        raise ValueError(f"state var 'epoch_phase' int value {val} out of range [0,2]")
    raise TypeError(f"state var 'epoch_phase' must be EpochPhase|str|int, got {type(val).__name__}")


def _coerce_state_bool(name: str, val: Any) -> bool:
    if isinstance(val, bool):
        return bool(val)
    if isinstance(val, int) and val in (0, 1):
        return bool(val)
    raise TypeError(f"state var {name!r} must be bool or 0/1 int, got {type(val).__name__}")


def _coerce_state_int(name: str, val: Any) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise TypeError(f"state var {name!r} must be int, got {type(val).__name__}")
    return int(val)


def initial_state() -> PerpState:
    """Return the canonical initial PerpState matching the YAML init block.

    All dataclass defaults match the YAML init block, so ``PerpState()``
    is the correct initial state.
    """
    return PerpState()


def state_to_dict(state: PerpState) -> dict[str, bool | int | str]:
    """Serialize a PerpState to a plain dict (kernel-state dict format)."""
    d: dict[str, bool | int | str] = {}
    for name in STATE_VAR_NAMES:
        val = getattr(state, name)
        if isinstance(val, EpochPhase):
            # Kernel spec uses int encoding for enums: Open=0, PricePublished=1, Settled=2.
            d[name] = int(_EPOCH_PHASE_TO_INT[val])
        else:
            d[name] = val
    return d


def state_from_dict(d: Mapping[str, Any]) -> PerpState:
    """Deserialize a dict to a PerpState. Raises KeyError on missing fields."""
    kwargs: dict[str, Any] = {}
    for name in STATE_VAR_NAMES:
        val = d[name]
        if name == "epoch_phase":
            kwargs[name] = _coerce_epoch_phase(val)
        elif name in _BOOL_STATE_VAR_NAMES:
            kwargs[name] = _coerce_state_bool(name, val)
        else:
            kwargs[name] = _coerce_state_int(name, val)
    return PerpState(**kwargs)
