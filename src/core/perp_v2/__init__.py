"""`perp_v2`: pure-Python implementation of the `perp_epoch_isolated_v3` risk kernel.

This package mirrors the generated actions in
`src/kernels/dex/perp_epoch_isolated_v3.yaml`:
- deterministic, integer-only transitions,
- immutable state (frozen dataclasses),
- fail-closed guards and invariant checks.

The native ``partial_liquidate`` extension is not yet in that YAML model.  It is
tracked by ``PERP-PARTIAL-LIQUIDATION-FORMAL-001`` and receives no generated
parity or formal-promotion credit.

Public API:
- `initial_state() -> PerpState`
- `step(state, params) -> StepResult`
- `step_or_raise(state, params) -> StepResult` (raises on rejection)
"""

from .engine import (
    PARTIAL_LIQUIDATION_FORMAL_PROMOTION_BLOCKER,
    step,
    step_or_raise,
)
from .errors import PerpGuardError, PerpInvariantError, PerpOverflowError
from .state import initial_state, state_from_dict, state_to_dict
from .types import Action, ActionParams, Effect, EpochPhase, Event, PerpState, StepResult

__all__ = [
    "step",
    "step_or_raise",
    "initial_state",
    "state_from_dict",
    "state_to_dict",
    "Action",
    "ActionParams",
    "Effect",
    "EpochPhase",
    "Event",
    "PerpState",
    "StepResult",
    "PerpGuardError",
    "PerpInvariantError",
    "PerpOverflowError",
    "PARTIAL_LIQUIDATION_FORMAL_PROMOTION_BLOCKER",
]
