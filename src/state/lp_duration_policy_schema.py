"""Declarative schema for the explicit LP duration-risk context."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from .lp_duration_transitions import LPDurationRiskPolicyV1
from .snapshot_combinators import (
    DeclaredFieldV1,
    ExactInt,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
)

LP_DURATION_POLICY_SCHEMA_REVISION_V1 = "zenodex/fcis/context/lp-duration-policy/v1"
LP_DURATION_POLICY_SCHEMA_ID_V1 = "zenodex/fcis/context/lp-duration-policy-value/v1"
LP_DURATION_POLICY_FIELD_NAMES_V1 = (
    "base_age_seconds",
    "max_age_seconds",
    "churn_window_seconds",
    "decay_seconds",
    "multiplier",
    "max_churn_tier",
)


class LPDurationPolicyEnumTagV1(Enum):
    """This closed profile intentionally has no enum variants."""


class LPDurationPolicyRecordTagV1(Enum):
    LP_DURATION_POLICY = "lp_duration_policy"


@final
@dataclass(frozen=True, slots=True)
class LPDurationPolicyAdmissionSourceV1:
    """Exact non-authoritative carrier for projected legacy policy fields."""

    base_age_seconds: object
    max_age_seconds: object
    churn_window_seconds: object
    decay_seconds: object
    multiplier: object
    max_churn_tier: object


LP_DURATION_POLICY_RECORD_SCHEMA_V1 = RecordOf(
    LPDurationPolicyRecordTagV1.LP_DURATION_POLICY,
    (
        DeclaredFieldV1("base_age_seconds", ExactInt(0, None)),
        DeclaredFieldV1("max_age_seconds", ExactInt(0, None)),
        DeclaredFieldV1("churn_window_seconds", ExactInt(0, None)),
        DeclaredFieldV1("decay_seconds", ExactInt(0, None)),
        DeclaredFieldV1("multiplier", ExactInt(1, None)),
        DeclaredFieldV1("max_churn_tier", ExactInt(0, None)),
    ),
)

LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(
        LPDurationPolicyRecordTagV1.LP_DURATION_POLICY,
        LPDurationPolicyAdmissionSourceV1,
        LPDurationRiskPolicyV1,
    ),
)

LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(
        LP_DURATION_POLICY_SCHEMA_ID_V1,
        OptionalValue(LP_DURATION_POLICY_RECORD_SCHEMA_V1),
    ),
)

__all__ = (
    "LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1",
    "LP_DURATION_POLICY_FIELD_NAMES_V1",
    "LP_DURATION_POLICY_SCHEMA_ID_V1",
    "LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1",
    "LP_DURATION_POLICY_SCHEMA_REVISION_V1",
    "LP_DURATION_POLICY_RECORD_SCHEMA_V1",
    "LPDurationPolicyAdmissionSourceV1",
    "LPDurationPolicyEnumTagV1",
    "LPDurationPolicyRecordTagV1",
)
