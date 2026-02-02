"""State construction and serialization for `perp_v2`.

`initial_state()` returns the canonical initial state (matches the YAML `init` block).

Round-trip property (tested): `state_from_dict(state_to_dict(s)) == s` for all valid states.
"""

from __future__ import annotations

from typing import Any, Mapping

from .types import PerpState

# Auto-derived from PerpState field definitions (single source of truth).
STATE_VAR_NAMES: tuple[str, ...] = tuple(PerpState.__dataclass_fields__)


def initial_state() -> PerpState:
    """Return the canonical initial PerpState matching the YAML init block.

    All dataclass defaults match the YAML init block, so ``PerpState()``
    is the correct initial state.
    """
    return PerpState()


def state_to_dict(state: PerpState) -> dict[str, bool | int]:
    """Serialize a PerpState to a plain dict (kernel-state dict format)."""
    return {name: getattr(state, name) for name in STATE_VAR_NAMES}


def state_from_dict(d: Mapping[str, Any]) -> PerpState:
    """Deserialize a dict to a PerpState. Raises KeyError on missing fields."""
    kwargs: dict[str, Any] = {}
    for name in STATE_VAR_NAMES:
        val = d[name]
        if isinstance(val, bool):
            kwargs[name] = val
        elif isinstance(val, int):
            kwargs[name] = int(val)  # normalize int subclasses (e.g. numpy)
        else:
            raise TypeError(f"state var {name!r} must be bool|int, got {type(val).__name__}")
    return PerpState(**kwargs)
