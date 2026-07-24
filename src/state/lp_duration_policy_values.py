"""Owned leaf values for the LP duration-risk policy.

This module intentionally has no transition, committed-state, or core imports.
Authority admission and transition evaluation may both depend on this value
without creating an import path from value definitions back into runtime code.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import final


@final
@dataclass(frozen=True, slots=True)
class LPDurationRiskPolicyV1:
    """Data-only exact policy context for accepted LP lifecycle events."""

    base_age_seconds: int = 0
    max_age_seconds: int = 0
    churn_window_seconds: int = 0
    decay_seconds: int = 0
    multiplier: int = 2
    max_churn_tier: int = 0

    def __post_init__(self) -> None:
        for field_name in (
            "base_age_seconds",
            "max_age_seconds",
            "churn_window_seconds",
            "decay_seconds",
            "max_churn_tier",
        ):
            value = object.__getattribute__(self, field_name)
            if type(value) is not int:
                raise TypeError(f"{field_name} must be an exact integer")
            if value < 0:
                raise ValueError(f"{field_name} must be an exact nonnegative int")
        if type(self.multiplier) is not int:
            raise TypeError("multiplier must be an exact integer")
        if self.multiplier < 1:
            raise ValueError("multiplier must be an exact int >= 1")
        if self.max_age_seconds and self.base_age_seconds > self.max_age_seconds:
            raise ValueError("base_age_seconds must be <= max_age_seconds")


__all__ = ("LPDurationRiskPolicyV1",)
