"""`perp_v2`: pure-Python implementation of the `perp_epoch_isolated_v2` risk kernel.

This package mirrors the semantics of `src/kernels/dex/perp_epoch_isolated_v2.yaml`:
- deterministic, integer-only transitions,
- immutable state (frozen dataclasses),
- fail-closed guards and invariant checks.

The YAML spec remains the source of truth; this code exists for fast execution and
auditable, unit-tested behavior.

Public API:
- `initial_state() -> PerpState`
- `step(state, params) -> StepResult`
- `step_or_raise(state, params) -> StepResult` (raises on rejection)
"""

from .engine import step, step_or_raise
from .errors import PerpGuardError, PerpInvariantError, PerpOverflowError
from .state import initial_state, state_from_dict, state_to_dict
from .types import Action, ActionParams, Effect, Event, PerpState, StepResult

__all__ = [
    "step",
    "step_or_raise",
    "initial_state",
    "state_from_dict",
    "state_to_dict",
    "Action",
    "ActionParams",
    "Effect",
    "Event",
    "PerpState",
    "StepResult",
    "PerpGuardError",
    "PerpInvariantError",
    "PerpOverflowError",
]
