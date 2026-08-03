from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_fee_custody_transition import (
    FeeCustodyTransitionOkV2,
    apply_protocol_fee_distribution_v2,
)
from src.core.fcis_fee_custody_values import (
    CommittedFeeAccumulatorStateV2,
    FeeDistributionPolicyV2,
    ProtocolFeeCreditV2,
)
from src.core.zusd_protocol_fee_claim import (
    ZUSDProtocolFeeClaimTransitionV1,
    ZUSDProtocolFeeClaimV1,
    accrue_zusd_protocol_fee_claim_v1,
    empty_zusd_protocol_fee_claim_v1,
)
from src.core.zusd_protocol_fee_claim_realization import (
    ZUSDProtocolFeeClaimRealizationRejectCodeV1,
    ZUSDProtocolFeeClaimRealizationRejectV1,
    ZUSDProtocolFeeClaimRealizationSourceV1,
    ZUSDProtocolFeeClaimRealizationV1,
    derive_zusd_protocol_fee_claim_realization_v1,
    verify_zusd_protocol_fee_claim_realization_v1,
)
from src.state.balances import BalanceTable
from src.state.state_snapshot_values import CommittedBalanceTableV1
from src.state.state_snapshots import snapshot_balance_table

E8 = 100_000_000
U256_MAX = (1 << 256) - 1
ASSET = "0x" + "aa" * 32
OTHER_ASSET = "0x" + "dd" * 32
ESCROW = "0x" + "bb" * 48
FOREIGN_ESCROW = "0x" + "cc" * 48
ALICE = "0x" + "11" * 48
TREASURY = "0x" + "22" * 48


def _balances(*entries: tuple[str, str, int]) -> CommittedBalanceTableV1:
    source = BalanceTable()
    for pubkey, asset, amount in entries:
        source.set(pubkey, asset, amount)
    return snapshot_balance_table(source)


def _accrued_claim(amount_e8: int) -> ZUSDProtocolFeeClaimV1:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    accrued = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=amount_e8,
    )
    assert type(accrued) is ZUSDProtocolFeeClaimTransitionV1
    return accrued.post_state


def _source(
    *,
    claim: object,
    balances: object,
    debt_e8: object,
    amount_e8: object,
    custody_pubkey: object = ESCROW,
) -> ZUSDProtocolFeeClaimRealizationSourceV1:
    return ZUSDProtocolFeeClaimRealizationSourceV1(
        asset_id=ASSET,
        custody_pubkey=custody_pubkey,
        pre_claim=claim,
        pre_balances=balances,
        debt_e8=debt_e8,
        amount_e8=amount_e8,
    )


def test_realization_atomically_pairs_claim_reduction_with_exact_escrow_credit() -> None:
    pre_claim = _accrued_claim(3 * E8)
    pre_balances = _balances(
        (ALICE, ASSET, 5),
        (ESCROW, ASSET, 2),
        (ALICE, OTHER_ASSET, 9),
    )
    pre_entries = pre_balances.entries

    source = _source(
        claim=pre_claim,
        balances=pre_balances,
        debt_e8=10 * E8,
        amount_e8=2 * E8,
    )
    result = derive_zusd_protocol_fee_claim_realization_v1(source)

    assert type(result) is ZUSDProtocolFeeClaimRealizationV1
    assert result.claim_transition.post_state.outstanding_e8 == E8
    assert result.claim_transition.post_state.accrued_cumulative_e8 == 3 * E8
    assert result.post_balances.get(ESCROW, ASSET) == 4
    assert result.post_balances.get(ALICE, ASSET) == 5
    assert result.post_balances.get(ALICE, OTHER_ASSET) == 9
    assert result.protocol_fee_credit == ProtocolFeeCreditV2(ESCROW, ASSET, 2)
    assert result.amount_e8 == 2 * E8
    assert result.amount_units == 2
    assert result.balance_patch.writes[0].key == (ESCROW, ASSET)
    assert result.balance_patch.writes[0].expected_old == 2
    assert result.balance_patch.writes[0].replacement == 4
    assert result.supply_claim_certificate.debt_delta_e8 == 0
    assert result.supply_claim_certificate.ledger_supply_delta_e8 == 2 * E8
    assert result.supply_claim_certificate.outstanding_claim_delta_e8 == -(2 * E8)
    assert pre_balances.entries == pre_entries

    verified = verify_zusd_protocol_fee_claim_realization_v1(
        source=source,
        realization=result,
    )
    assert verified is result


def test_realization_retains_subledger_residue_in_the_exact_claim() -> None:
    source = _source(
        claim=_accrued_claim(E8 + 1),
        balances=_balances((ALICE, ASSET, 5)),
        debt_e8=6 * E8 + 1,
        amount_e8=E8,
    )

    result = derive_zusd_protocol_fee_claim_realization_v1(source)

    assert type(result) is ZUSDProtocolFeeClaimRealizationV1
    assert result.claim_transition.post_state.outstanding_e8 == 1
    assert result.post_balances.get(ESCROW, ASSET) == 1
    assert (
        result.supply_claim_certificate.ledger_supply_post_e8
        + result.claim_transition.post_state.outstanding_e8
        == result.supply_claim_certificate.debt_post_e8
    )


def test_realized_credit_composes_with_existing_fee_custody_distribution() -> None:
    source = _source(
        claim=_accrued_claim(3 * E8),
        balances=_balances((ALICE, ASSET, 5), (ESCROW, ASSET, 2)),
        debt_e8=10 * E8,
        amount_e8=2 * E8,
    )
    realization = derive_zusd_protocol_fee_claim_realization_v1(source)
    assert type(realization) is ZUSDProtocolFeeClaimRealizationV1

    distributed = apply_protocol_fee_distribution_v2(
        credits=(realization.protocol_fee_credit,),
        policy=FeeDistributionPolicyV2(
            buyback_bps=0,
            treasury_bps=10_000,
            rewards_bps=0,
            buyback_custody_pubkey=TREASURY,
            treasury_custody_pubkey=TREASURY,
            rewards_custody_pubkey=TREASURY,
        ),
        accumulator=CommittedFeeAccumulatorStateV2(()),
        balances=realization.post_balances,
    )

    assert type(distributed) is FeeCustodyTransitionOkV2
    assert distributed.balances.get(ESCROW, ASSET) == 2
    assert distributed.balances.get(TREASURY, ASSET) == 2
    assert (
        sum(amount for (_owner, asset), amount in distributed.balances.entries if asset == ASSET)
        == 9
    )


def test_realization_rejects_invalid_absolute_economic_prestate() -> None:
    result = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=_accrued_claim(2 * E8),
            balances=_balances((ALICE, ASSET, 5)),
            debt_e8=8 * E8,
            amount_e8=E8,
        )
    )

    assert result == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_PRESTATE,
        ("economic_identity",),
    )


@pytest.mark.parametrize(
    ("amount_e8", "code"),
    [
        (False, ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE),
        (-1, ZUSDProtocolFeeClaimRealizationRejectCodeV1.NEGATIVE_VALUE),
        (0, ZUSDProtocolFeeClaimRealizationRejectCodeV1.ZERO_AMOUNT),
        (1, ZUSDProtocolFeeClaimRealizationRejectCodeV1.NON_WHOLE_AMOUNT),
        (4 * E8, ZUSDProtocolFeeClaimRealizationRejectCodeV1.AMOUNT_EXCEEDS_OUTSTANDING),
        (1 << 256, ZUSDProtocolFeeClaimRealizationRejectCodeV1.VALUE_EXCEEDS_U256),
    ],
)
def test_realization_rejects_invalid_amount_without_authority_outputs(
    amount_e8: object,
    code: ZUSDProtocolFeeClaimRealizationRejectCodeV1,
) -> None:
    result = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=_accrued_claim(3 * E8),
            balances=_balances((ALICE, ASSET, 5)),
            debt_e8=10 * E8,
            amount_e8=amount_e8,
        )
    )

    assert type(result) is ZUSDProtocolFeeClaimRealizationRejectV1
    assert result.code is code
    assert not hasattr(result, "post_balances")
    assert not hasattr(result, "balance_patch")
    assert not hasattr(result, "protocol_fee_credit")


def test_realization_rejects_unowned_or_hostile_sources() -> None:
    pre_claim = _accrued_claim(2 * E8)
    mutable_balances = BalanceTable()
    mutable_balances.set(ALICE, ASSET, 5)

    wrong_balance_type = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=pre_claim,
            balances=mutable_balances,
            debt_e8=10 * E8,
            amount_e8=E8,
        )
    )
    crossed_identity = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=pre_claim,
            balances=_balances((ALICE, ASSET, 5)),
            debt_e8=10 * E8,
            amount_e8=E8,
            custody_pubkey=FOREIGN_ESCROW,
        )
    )
    hostile_claim = _accrued_claim(2 * E8)
    object.__setattr__(hostile_claim, "outstanding_e8", 3 * E8)
    invalid_claim = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=hostile_claim,
            balances=_balances((ALICE, ASSET, 5)),
            debt_e8=10 * E8,
            amount_e8=E8,
        )
    )
    wrong_source_type = derive_zusd_protocol_fee_claim_realization_v1(object())

    assert wrong_balance_type == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
        ("pre_balances",),
    )
    assert crossed_identity == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("identity",),
    )
    assert invalid_claim == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_CLAIM_STATE,
        ("pre_claim",),
    )
    assert wrong_source_type == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
        ("source",),
    )


def test_realization_rejects_ledger_supply_overflow_before_emitting_patch() -> None:
    max_units = U256_MAX // E8
    result = derive_zusd_protocol_fee_claim_realization_v1(
        _source(
            claim=_accrued_claim(E8),
            balances=_balances((ALICE, ASSET, max_units)),
            debt_e8=U256_MAX,
            amount_e8=E8,
        )
    )

    assert result == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.LEDGER_SUPPLY_OVERFLOW,
        ("ledger_supply",),
    )


def test_realization_verifier_rejects_crossed_prestate_and_closed_result_mutation() -> None:
    claim = _accrued_claim(2 * E8)
    balances = _balances((ALICE, ASSET, 5))
    source = _source(
        claim=claim,
        balances=balances,
        debt_e8=7 * E8,
        amount_e8=E8,
    )
    result = derive_zusd_protocol_fee_claim_realization_v1(source)
    assert type(result) is ZUSDProtocolFeeClaimRealizationV1

    crossed = verify_zusd_protocol_fee_claim_realization_v1(
        source=_source(
            claim=claim,
            balances=_balances((ALICE, ASSET, 6)),
            debt_e8=8 * E8,
            amount_e8=E8,
        ),
        realization=result,
    )
    assert crossed == ZUSDProtocolFeeClaimRealizationRejectV1(
        ZUSDProtocolFeeClaimRealizationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("instance",),
    )

    with pytest.raises(TypeError, match="controlled derivation"):
        replace(result, protocol_fee_credit=ProtocolFeeCreditV2(ESCROW, ASSET, 2))


def test_realization_bounded_family_preserves_supply_claim_identity() -> None:
    for initial_supply_units in range(4):
        pre_balances = _balances((ALICE, ASSET, initial_supply_units))
        for outstanding_units in range(1, 6):
            claim = _accrued_claim(outstanding_units * E8)
            for realized_units in range(1, outstanding_units + 1):
                result = derive_zusd_protocol_fee_claim_realization_v1(
                    _source(
                        claim=claim,
                        balances=pre_balances,
                        debt_e8=(initial_supply_units + outstanding_units) * E8,
                        amount_e8=realized_units * E8,
                    )
                )
                assert type(result) is ZUSDProtocolFeeClaimRealizationV1
                certificate = result.supply_claim_certificate
                assert certificate.debt_delta_e8 == 0
                assert (
                    certificate.ledger_supply_delta_e8 + certificate.outstanding_claim_delta_e8 == 0
                )
                assert (
                    result.post_balances.get(ESCROW, ASSET)
                    == pre_balances.get(ESCROW, ASSET) + realized_units
                )
