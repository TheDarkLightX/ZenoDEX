"""Caller-safe bindings for the closed LP duration-policy admission profile."""

from __future__ import annotations

from typing import cast

from . import snapshot_combinators
from .lp_duration_policy_admission import admit as _admit_policy_profile
from .lp_duration_policy_schema import (
    LP_DURATION_POLICY_SCHEMA_ID_V1,
    LP_DURATION_POLICY_SCHEMA_REVISION_V1,
    LPDurationPolicyAdmissionSourceV1,
)
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)

_LP_DURATION_POLICY_ADMISSION_LIMITS_V1 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=snapshot_combinators.MAX_ADMISSION_DEPTH_V1,
        max_nodes=snapshot_combinators.MAX_ADMISSION_NODES_V1,
        max_canonical_bytes=snapshot_combinators.MAX_CANONICAL_BYTES_V1,
        max_collection_items=snapshot_combinators.MAX_COLLECTION_ITEMS_V1,
    )
)
if type(_LP_DURATION_POLICY_ADMISSION_LIMITS_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("LP duration-policy admission limits are invalid")


def admit_lp_duration_policy_fields_v1(
    *,
    base_age_seconds: object,
    max_age_seconds: object,
    churn_window_seconds: object,
    decay_seconds: object,
    multiplier: object,
    max_churn_tier: object,
) -> AdmitOk[LPDurationRiskPolicyV1] | AdmitReject:
    """Admit projected legacy fields through the fixed closed profile."""

    result = _admit_policy_profile(
        LP_DURATION_POLICY_SCHEMA_REVISION_V1,
        LP_DURATION_POLICY_SCHEMA_ID_V1,
        _LP_DURATION_POLICY_ADMISSION_LIMITS_V1,
        LPDurationPolicyAdmissionSourceV1(
            base_age_seconds=base_age_seconds,
            max_age_seconds=max_age_seconds,
            churn_window_seconds=churn_window_seconds,
            decay_seconds=decay_seconds,
            multiplier=multiplier,
            max_churn_tier=max_churn_tier,
        ),
    )
    return cast(AdmitOk[LPDurationRiskPolicyV1] | AdmitReject, result)


def admit_optional_lp_duration_policy_v1(
    source: object,
) -> AdmitOk[LPDurationRiskPolicyV1 | None] | AdmitReject:
    """Revalidate an exact owned policy or admit ``None`` through the profile."""

    result = _admit_policy_profile(
        LP_DURATION_POLICY_SCHEMA_REVISION_V1,
        LP_DURATION_POLICY_SCHEMA_ID_V1,
        _LP_DURATION_POLICY_ADMISSION_LIMITS_V1,
        source,
    )
    return cast(AdmitOk[LPDurationRiskPolicyV1 | None] | AdmitReject, result)


__all__ = (
    "admit_lp_duration_policy_fields_v1",
    "admit_optional_lp_duration_policy_v1",
)
