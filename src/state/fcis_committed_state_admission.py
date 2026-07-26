"""Caller-safe facade for the closed eight-field FCIS state aggregate."""

from __future__ import annotations

from typing import cast

from .fcis_committed_state_values import (
    FCIS_COMMITTED_STATE_SCHEMA_ID_V1,
    FCISCommittedStateV1,
)
from .snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
    MAX_COLLECTION_ITEMS_V1,
    AdmissionLimitsV1,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from .state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1

_FCIS_COMMITTED_STATE_ADMISSION_LIMITS_V1 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_nodes=MAX_ADMISSION_NODES_V1,
        max_canonical_bytes=MAX_CANONICAL_BYTES_V1,
        max_collection_items=MAX_COLLECTION_ITEMS_V1,
    )
)
if type(_FCIS_COMMITTED_STATE_ADMISSION_LIMITS_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("FCIS committed-state admission limits are invalid")


def admit_fcis_committed_state_v1(
    source: object,
) -> AdmitOk[FCISCommittedStateV1] | AdmitReject:
    """Admit or re-admit one complete state through the sole closed profile."""

    from .state_admission_profile import admit

    result = admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        FCIS_COMMITTED_STATE_SCHEMA_ID_V1,
        _FCIS_COMMITTED_STATE_ADMISSION_LIMITS_V1,
        source,
    )
    return cast(AdmitOk[FCISCommittedStateV1] | AdmitReject, result)


__all__ = ("admit_fcis_committed_state_v1",)
