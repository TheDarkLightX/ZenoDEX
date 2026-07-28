from __future__ import annotations

import pytest

from src.core.fcis_fee_apportionment_admission import admit
from src.core.fcis_fee_apportionment_codec import encode_fcis_fee_apportionment_v2
from src.core.fcis_fee_apportionment_values import (
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
    CommittedFeeApportionmentStateSourceV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateSourceV2,
    FeeApportionmentKeySourceV2,
    FeeDeficitEntrySourceV2,
)
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)


def _limits() -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=20_000,
            max_canonical_bytes=1_000_000,
            max_collection_items=20_000,
        )
    )
    if type(result) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test limits must be valid")
    return result


def test_candidate_batch_is_closed_owned_and_byte_pinned() -> None:
    source = (
        FeeAmountCandidateSourceV2(
            FeeApportionmentKeySourceV2("domain-a", "asset-a"),
            10,
        ),
        FeeAmountCandidateSourceV2(
            FeeApportionmentKeySourceV2("domain-a", "asset-c"),
            1,
        ),
    )

    result = admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
        _limits(),
        source,
    )

    assert type(result) is AdmitOk
    assert encode_fcis_fee_apportionment_v2(
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
        result.value,
    ) == (
        b'{"schema":"zenodex/fcis/fee-apportionment/amount-candidate-batch/v2",'
        b'"value":[{"amount":10,"key":{"asset":"asset-a",'
        b'"fee_distribution_domain_id":"domain-a"}},{"amount":1,'
        b'"key":{"asset":"asset-c","fee_distribution_domain_id":"domain-a"}}]}'
    )


def test_candidate_batch_rejects_coercible_list_and_boolean_amount() -> None:
    assert admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
        _limits(),
        [],
    ) == AdmitReject(AdmitCode.WRONG_CONTAINER, ())

    result = admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
        _limits(),
        (
            FeeAmountCandidateSourceV2(
                FeeApportionmentKeySourceV2("domain", "asset"),
                True,
            ),
        ),
    )
    assert result == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, (0, "amount"))


def test_state_admission_rejects_retained_zero_and_noncanonical_order() -> None:
    retained_zero = CommittedFeeApportionmentStateSourceV2(
        "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        (
            FeeDeficitEntrySourceV2(
                FeeApportionmentKeySourceV2("domain", "asset"),
                0,
                0,
            ),
        ),
    )
    assert admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        _limits(),
        retained_zero,
    ) == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ("entries", 0))

    wrong_order = CommittedFeeApportionmentStateSourceV2(
        "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        (
            FeeDeficitEntrySourceV2(
                FeeApportionmentKeySourceV2("domain", "asset-z"),
                1,
                0,
            ),
            FeeDeficitEntrySourceV2(
                FeeApportionmentKeySourceV2("domain", "asset-a"),
                1,
                0,
            ),
        ),
    )
    assert admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        _limits(),
        wrong_order,
    ) == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


def test_empty_state_is_the_unique_canonical_zero() -> None:
    result = admit(
        FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        _limits(),
        CommittedFeeApportionmentStateSourceV2(
            "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
            (),
        ),
    )

    assert result == AdmitOk(
        CommittedFeeApportionmentStateV2(
            "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
            (),
        )
    )


def test_codec_revalidates_hostile_state_mutation() -> None:
    state = CommittedFeeApportionmentStateV2(
        "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        (),
    )
    object.__setattr__(state, "algorithm_version", "CURSOR_V0")

    with pytest.raises(ValueError, match="algorithm version"):
        encode_fcis_fee_apportionment_v2(
            COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
            state,
        )
