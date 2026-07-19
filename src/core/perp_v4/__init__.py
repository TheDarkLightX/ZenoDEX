"""Native implementation of `perp_epoch_isolated_v4`.

v4 preserves the generated v3 state and command ABI while using ceiling-rounded
initial and maintenance risk margins. Shared immutable state and command types
remain defined in `perp_v2`; the transition, guard, effect, invariant, and
arithmetic modules are versioned here.  The native ``partial_liquidate``
extension is tracked by ``PERP-PARTIAL-LIQUIDATION-FORMAL-001`` until it is
promoted into an authoritative generated model.
"""

from ..perp_v2.errors import PerpGuardError, PerpInvariantError, PerpOverflowError
from ..perp_v2.state import initial_state, state_from_dict, state_to_dict
from ..perp_v2.types import (
    Action,
    ActionParams,
    Effect,
    EpochPhase,
    Event,
    PerpState,
    StepResult,
)
from .engine import (
    PARTIAL_LIQUIDATION_FORMAL_PROMOTION_BLOCKER,
    step,
    step_or_raise,
)

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
