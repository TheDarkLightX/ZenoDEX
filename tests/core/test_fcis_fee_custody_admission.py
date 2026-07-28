from __future__ import annotations

import pytest

from src.core.fcis_fee_custody import (
    admit_fee_accumulator_v2,
    admit_fee_distribution_policy_v2,
    admit_protocol_fee_credit_batch_v2,
)
from src.core.fcis_fee_custody_codec import encode_fcis_fee_custody_v2
from src.core.fcis_fee_custody_values import (
    PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
    CommittedFeeAccumulatorStateV2,
    FeeAccumulatorSourceV2,
    FeeDistributionPolicySourceV2,
    FeeDustEntrySourceV2,
    ProtocolFeeCreditSourceV2,
    ProtocolFeeCreditV2,
)
from src.state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject


def test_credit_batch_is_owned_by_the_closed_combinator() -> None:
    source = (
        ProtocolFeeCreditSourceV2("source-a", "asset-a", 10),
        ProtocolFeeCreditSourceV2("source-c", "asset-c", 1),
    )

    result = admit_protocol_fee_credit_batch_v2(source)

    assert result == AdmitOk(
        (
            ProtocolFeeCreditV2("source-a", "asset-a", 10),
            ProtocolFeeCreditV2("source-c", "asset-c", 1),
        )
    )
    assert type(result) is AdmitOk
    assert encode_fcis_fee_custody_v2(
        PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
        result.value,
    ) == (
        b'{"schema":"zenodex/fcis/fee-custody/protocol-credit-batch/v2",'
        b'"value":[{"amount":10,"asset":"asset-a",'
        b'"source_custody_pubkey":"source-a"},{"amount":1,"asset":"asset-c",'
        b'"source_custody_pubkey":"source-c"}]}'
    )


def test_credit_batch_rejects_a_coercible_list() -> None:
    source = [ProtocolFeeCreditSourceV2("source", "asset", 1)]

    assert admit_protocol_fee_credit_batch_v2(source) == AdmitReject(
        AdmitCode.WRONG_CONTAINER,
        (),
    )


def test_policy_constructor_invariant_fails_closed() -> None:
    source = FeeDistributionPolicySourceV2(
        2_000,
        3_000,
        4_999,
        "buyback",
        "treasury",
        "rewards",
    )

    result = admit_fee_distribution_policy_v2(source)

    assert result == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


def test_accumulator_rejects_duplicate_custody_keys() -> None:
    source = FeeAccumulatorSourceV2(
        (
            FeeDustEntrySourceV2("source", "asset", 1),
            FeeDustEntrySourceV2("source", "asset", 2),
        )
    )

    result = admit_fee_accumulator_v2(source)

    assert result == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


def test_accumulator_admission_returns_exact_owned_state() -> None:
    source = FeeAccumulatorSourceV2(
        (
            FeeDustEntrySourceV2("source-a", "asset-a", 1),
            FeeDustEntrySourceV2("source-c", "asset-c", 2),
        )
    )

    result = admit_fee_accumulator_v2(source)

    assert type(result) is AdmitOk
    assert type(result.value) is CommittedFeeAccumulatorStateV2
    assert tuple(
        (entry.source_custody_pubkey, entry.asset, entry.amount) for entry in result.value.entries
    ) == (("source-a", "asset-a", 1), ("source-c", "asset-c", 2))


def test_codec_revalidates_a_hostile_mutation() -> None:
    credit = ProtocolFeeCreditV2("source", "asset", 1)
    object.__setattr__(credit, "amount", 0)

    with pytest.raises(TypeError, match="bounded integer"):
        encode_fcis_fee_custody_v2(
            PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
            (credit,),
        )
