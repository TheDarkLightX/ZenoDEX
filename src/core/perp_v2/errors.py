"""Exception types for the perp_v2 risk engine.

Used by ``step_or_raise()`` in ``engine.py`` for callers
that prefer exceptions over ``StepResult`` inspection.
"""

from __future__ import annotations


class PerpGuardError(Exception):
    """Raised when an action's guard condition is not satisfied."""


class PerpInvariantError(Exception):
    """Raised when a post-state violates one or more invariants."""

    def __init__(self, violations: list[str]) -> None:
        self.violations = violations
        super().__init__(f"invariant violations: {', '.join(violations)}")


class PerpOverflowError(Exception):
    """Raised when a parameter exceeds its YAML-defined domain bounds."""
