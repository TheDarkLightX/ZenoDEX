from __future__ import annotations

from itertools import permutations

import pytest

from src.core.fcis_fee_custody_codec import encode_fcis_fee_custody_v2
from src.core.fcis_fee_custody_transition import (
    FeeCustodyTransitionCodeV2,
    FeeCustodyTransitionOkV2,
    FeeCustodyTransitionRejectV2,
    apply_protocol_fee_distribution_v2,
    migrate_fee_accumulator_v1_to_v2,
)
from src.core.fcis_fee_custody_values import (
    FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FeeDistributionPolicyV2,
    FeeDustEntryV2,
    ProtocolFeeCreditV2,
)
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitOk,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from src.state.state_admission_profile import admit
from src.state.state_snapshot_schema import BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1
from src.state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    _BalanceSourceV1,
)


def _pubkey(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 48


def _asset(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 32


SOURCE_A = _pubkey(0x11)
SOURCE_C = _pubkey(0x12)
BUYBACK = _pubkey(0x21)
TREASURY = _pubkey(0x22)
REWARDS = _pubkey(0x23)
ASSET_A = _asset(0xA1)
ASSET_C = _asset(0xC1)


def _limits() -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=200_000,
            max_canonical_bytes=4_000_000,
            max_collection_items=200_000,
        )
    )
    if type(result) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test admission limits must be valid")
    return result


def _balances(*entries: tuple[tuple[str, str], int]) -> CommittedBalanceTableV1:
    admitted = admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        _limits(),
        _BalanceSourceV1({key: amount for key, amount in entries}),
    )
    if type(admitted) is not AdmitOk or type(admitted.value) is not CommittedBalanceTableV1:
        raise AssertionError(f"test balance admission failed: {admitted!r}")
    return admitted.value


def _policy(
    *,
    buyback_bps: int = 3_333,
    treasury_bps: int = 3_333,
    rewards_bps: int = 3_334,
    buyback: str = BUYBACK,
    treasury: str = TREASURY,
    rewards: str = REWARDS,
) -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(
        buyback_bps=buyback_bps,
        treasury_bps=treasury_bps,
        rewards_bps=rewards_bps,
        buyback_custody_pubkey=buyback,
        treasury_custody_pubkey=treasury,
        rewards_custody_pubkey=rewards,
    )


def _amount(state: CommittedBalanceTableV1, owner: str, asset: str) -> int:
    return state.get(owner, asset)


def _accepted(
    *,
    credits: tuple[ProtocolFeeCreditV2, ...],
    policy: FeeDistributionPolicyV2,
    accumulator: CommittedFeeAccumulatorStateV2,
    balances: CommittedBalanceTableV1,
) -> FeeCustodyTransitionOkV2:
    result = apply_protocol_fee_distribution_v2(
        credits=credits,
        policy=policy,
        accumulator=accumulator,
        balances=balances,
    )
    assert type(result) is FeeCustodyTransitionOkV2
    return result


def test_mixed_asset_protocol_fees_remain_dimensionally_separate() -> None:
    result = _accepted(
        credits=(
            ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 100),
            ProtocolFeeCreditV2(SOURCE_C, ASSET_C, 1),
        ),
        policy=_policy(),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances(((SOURCE_A, ASSET_A), 100), ((SOURCE_C, ASSET_C), 1)),
    )

    assert tuple((item.source_custody_pubkey, item.asset) for item in result.distributions) == (
        (SOURCE_A, ASSET_A),
        (SOURCE_C, ASSET_C),
    )
    assert tuple(
        (
            item.buyback_amount,
            item.treasury_amount,
            item.rewards_amount,
            item.dust_carried,
        )
        for item in result.distributions
    ) == ((33, 33, 33, 1), (0, 0, 0, 1))
    assert result.accumulator.entries == (
        FeeDustEntryV2(SOURCE_A, ASSET_A, 1),
        FeeDustEntryV2(SOURCE_C, ASSET_C, 1),
    )


def test_distribution_uses_only_protocol_owned_credit_amount() -> None:
    # The corresponding total LP fee may be 100. The fee-custody machine sees
    # only the exact 10-unit protocol credit produced by validated replay.
    result = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 10),),
        policy=_policy(buyback_bps=2_000, treasury_bps=3_000, rewards_bps=5_000),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances(((SOURCE_A, ASSET_A), 10)),
    )

    assert result.distributions == (
        AssetFeeDistributionV2(
            source_custody_pubkey=SOURCE_A,
            asset=ASSET_A,
            buyback_custody_pubkey=BUYBACK,
            treasury_custody_pubkey=TREASURY,
            rewards_custody_pubkey=REWARDS,
            buyback_amount=2,
            treasury_amount=3,
            rewards_amount=5,
            dust_carried=0,
        ),
    )
    assert _amount(result.balances, SOURCE_A, ASSET_A) == 0
    assert _amount(result.balances, BUYBACK, ASSET_A) == 2
    assert _amount(result.balances, TREASURY, ASSET_A) == 3
    assert _amount(result.balances, REWARDS, ASSET_A) == 5


def test_each_custody_key_conserves_fresh_credit_plus_prior_dust() -> None:
    result = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 12_345),),
        policy=_policy(buyback_bps=1, treasury_bps=5_999, rewards_bps=4_000),
        accumulator=CommittedFeeAccumulatorStateV2((FeeDustEntryV2(SOURCE_A, ASSET_A, 7),)),
        balances=_balances(((SOURCE_A, ASSET_A), 12_352)),
    )
    allocation = result.distributions[0]

    assert (
        allocation.buyback_amount
        + allocation.treasury_amount
        + allocation.rewards_amount
        + allocation.dust_carried
        == 12_345 + 7
    )
    assert _amount(result.balances, SOURCE_A, ASSET_A) == allocation.dust_carried


def test_disjoint_custody_keys_are_partition_invariant() -> None:
    policy = _policy()
    initial = _balances(((SOURCE_A, ASSET_A), 101), ((SOURCE_C, ASSET_C), 205))
    combined = _accepted(
        credits=(
            ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 100),
            ProtocolFeeCreditV2(SOURCE_C, ASSET_C, 200),
        ),
        policy=policy,
        accumulator=CommittedFeeAccumulatorStateV2(
            (
                FeeDustEntryV2(SOURCE_A, ASSET_A, 1),
                FeeDustEntryV2(SOURCE_C, ASSET_C, 5),
            )
        ),
        balances=initial,
    )
    first = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 100),),
        policy=policy,
        accumulator=CommittedFeeAccumulatorStateV2((FeeDustEntryV2(SOURCE_A, ASSET_A, 1),)),
        balances=initial,
    )
    second = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_C, ASSET_C, 200),),
        policy=policy,
        accumulator=CommittedFeeAccumulatorStateV2((FeeDustEntryV2(SOURCE_C, ASSET_C, 5),)),
        balances=first.balances,
    )

    assert second.balances == combined.balances
    assert first.distributions + second.distributions == combined.distributions
    assert first.accumulator.entries + second.accumulator.entries == combined.accumulator.entries


def test_credit_input_order_cannot_change_result() -> None:
    credits = (
        ProtocolFeeCreditV2(SOURCE_C, ASSET_C, 2),
        ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 3),
        ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 7),
    )
    results = tuple(
        _accepted(
            credits=ordering,
            policy=_policy(),
            accumulator=CommittedFeeAccumulatorStateV2(()),
            balances=_balances(((SOURCE_A, ASSET_A), 10), ((SOURCE_C, ASSET_C), 2)),
        )
        for ordering in permutations(credits)
    )

    assert all(result == results[0] for result in results)


@pytest.mark.parametrize(
    ("buyback_bps", "treasury_bps", "rewards_bps"),
    ((0, 0, 10_000), (1, 0, 9_999), (9_999, 1, 0), (10_000, 0, 0)),
)
def test_distribution_basis_point_boundaries(
    buyback_bps: int,
    treasury_bps: int,
    rewards_bps: int,
) -> None:
    result = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 10_000),),
        policy=_policy(
            buyback_bps=buyback_bps,
            treasury_bps=treasury_bps,
            rewards_bps=rewards_bps,
        ),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances(((SOURCE_A, ASSET_A), 10_000)),
    )
    allocation = result.distributions[0]

    assert (
        allocation.buyback_amount,
        allocation.treasury_amount,
        allocation.rewards_amount,
        allocation.dust_carried,
    ) == (buyback_bps, treasury_bps, rewards_bps, 0)


def test_source_and_destination_aliases_use_one_canonical_balance_patch() -> None:
    result = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 10_000),),
        policy=_policy(buyback=SOURCE_A, treasury=TREASURY, rewards=TREASURY),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances(((SOURCE_A, ASSET_A), 10_000)),
    )

    assert _amount(result.balances, SOURCE_A, ASSET_A) == 3_333
    assert _amount(result.balances, TREASURY, ASSET_A) == 6_667
    assert result.balance_patch is not None
    assert tuple(write.key for write in result.balance_patch.writes) == (
        (SOURCE_A, ASSET_A),
        (TREASURY, ASSET_A),
    )


def test_complete_alias_is_valid_and_emits_no_balance_patch() -> None:
    result = _accepted(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 10_000),),
        policy=_policy(buyback=SOURCE_A, treasury=SOURCE_A, rewards=SOURCE_A),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances(((SOURCE_A, ASSET_A), 10_000)),
    )

    assert result.balances == _balances(((SOURCE_A, ASSET_A), 10_000))
    assert result.balance_patch is None
    assert result.distributions[0].dust_carried == 0


def test_insufficient_source_custody_rejects_without_partial_candidate() -> None:
    result = apply_protocol_fee_distribution_v2(
        credits=(ProtocolFeeCreditV2(SOURCE_A, ASSET_A, 10),),
        policy=_policy(),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        # The policy distributes nine units and retains one unit of dust. A
        # nine-unit balance could fund the visible debits while leaving the
        # retained dust unbacked, so the complete ten-unit custody claim must
        # be checked.
        balances=_balances(((SOURCE_A, ASSET_A), 9)),
    )

    assert type(result) is FeeCustodyTransitionRejectV2
    assert result.code is FeeCustodyTransitionCodeV2.INSUFFICIENT_CUSTODY
    assert not hasattr(result, "balances")
    assert not hasattr(result, "balance_patch")
    assert not hasattr(result, "distributions")
    assert not hasattr(result, "accumulator")


def test_distribution_value_rejects_integer_domain_overflow() -> None:
    maximum = (1 << 256) - 1

    with pytest.raises(ValueError, match="distribution total"):
        AssetFeeDistributionV2(
            source_custody_pubkey=SOURCE_A,
            asset=ASSET_A,
            buyback_custody_pubkey=BUYBACK,
            treasury_custody_pubkey=TREASURY,
            rewards_custody_pubkey=REWARDS,
            buyback_amount=maximum,
            treasury_amount=1,
            rewards_amount=0,
            dust_carried=0,
        )


def test_nonzero_scalar_dust_has_no_safe_v2_migration() -> None:
    rejected = migrate_fee_accumulator_v1_to_v2(CommittedFeeAccumulatorStateV1(dust=1))
    accepted = migrate_fee_accumulator_v1_to_v2(CommittedFeeAccumulatorStateV1(dust=0))

    assert type(rejected) is FeeCustodyTransitionRejectV2
    assert rejected.code is FeeCustodyTransitionCodeV2.UNOWNED_LEGACY_DUST
    assert accepted == CommittedFeeAccumulatorStateV2(())


def test_mutated_accumulator_rejects_before_balance_reads() -> None:
    accumulator = CommittedFeeAccumulatorStateV2(())
    object.__setattr__(
        accumulator,
        "entries",
        (FeeDustEntryV2(SOURCE_A, ASSET_A, 1), FeeDustEntryV2(SOURCE_A, ASSET_A, 1)),
    )

    result = apply_protocol_fee_distribution_v2(
        credits=(),
        policy=_policy(),
        accumulator=accumulator,
        balances=_balances(((SOURCE_A, ASSET_A), 1)),
    )

    assert type(result) is FeeCustodyTransitionRejectV2
    assert result.code is FeeCustodyTransitionCodeV2.INVALID_PRESTATE


def test_complete_transition_result_has_one_canonical_encoding() -> None:
    result = _accepted(
        credits=(ProtocolFeeCreditV2("source", "asset", 10),),
        policy=_policy(
            buyback_bps=2_000,
            treasury_bps=3_000,
            rewards_bps=5_000,
            buyback="buyback",
            treasury="treasury",
            rewards="rewards",
        ),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=_balances((("source", "asset"), 10)),
    )

    assert encode_fcis_fee_custody_v2(
        FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2,
        result,
    ) == (
        b'{"schema":"zenodex/fcis/fee-custody/transition-result/v2","value":{'
        b'"accumulator":{"entries":[]},"balance_patch":{"writes":['
        b'{"expected_old":0,"key":["buyback","asset"],"replacement":2},'
        b'{"expected_old":0,"key":["rewards","asset"],"replacement":5},'
        b'{"expected_old":10,"key":["source","asset"],"replacement":null},'
        b'{"expected_old":0,"key":["treasury","asset"],"replacement":3}]},'
        b'"balances":[{"amount":2,"asset":"asset","pubkey":"buyback"},'
        b'{"amount":5,"asset":"asset","pubkey":"rewards"},'
        b'{"amount":3,"asset":"asset","pubkey":"treasury"}],'
        b'"distributions":[{"asset":"asset","buyback_amount":2,'
        b'"buyback_custody_pubkey":"buyback","dust_carried":0,'
        b'"rewards_amount":5,"rewards_custody_pubkey":"rewards",'
        b'"source_custody_pubkey":"source","treasury_amount":3,'
        b'"treasury_custody_pubkey":"treasury"}]}}'
    )
