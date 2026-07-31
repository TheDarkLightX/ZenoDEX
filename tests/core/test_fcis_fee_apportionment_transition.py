from __future__ import annotations

from itertools import product

import pytest

from src.core import fcis_fee_apportionment_allocator as allocator
from src.core.fcis_fee_apportionment_transition import (
    FeeQuotaRejectCodeV2,
    FeeQuotaRejectV2,
    FeeQuotaV2,
    compute_fee_quota_v2,
)
from src.core.fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionCodeV2,
    FeeApportionmentTransitionRejectV2,
    FeeDistributionPolicyV2,
)


def test_u256_boundary_vectors_preserve_the_euclidean_relation() -> None:
    amounts = (
        0,
        1,
        BPS_DENOMINATOR_V2 - 1,
        BPS_DENOMINATOR_V2,
        BPS_DENOMINATOR_V2 + 1,
        MAX_FEE_AMOUNT_V2 - 1,
        MAX_FEE_AMOUNT_V2,
    )
    weights = (0, 1, 5_000, BPS_DENOMINATOR_V2 - 1, BPS_DENOMINATOR_V2)

    for amount, weight in product(amounts, weights):
        result = compute_fee_quota_v2(amount=amount, weight=weight)
        assert type(result) is FeeQuotaV2
        assert result.amount == amount
        assert result.weight == weight
        assert result.quotient * BPS_DENOMINATOR_V2 + result.residual == amount
        residual_product = result.residual * weight
        assert result.base == (
            result.quotient * weight
            + residual_product // BPS_DENOMINATOR_V2
        )
        assert result.remainder == residual_product % BPS_DENOMINATOR_V2
        assert result.quotient * weight <= amount
        assert residual_product < BPS_DENOMINATOR_V2 * BPS_DENOMINATOR_V2
        assert 0 <= result.remainder < BPS_DENOMINATOR_V2
        assert 0 <= result.base <= amount


@pytest.mark.parametrize(
    ("amount", "weight", "denominator", "code", "path"),
    (
        (
            True,
            1,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("amount",),
        ),
        (
            1,
            False,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("weight",),
        ),
        (
            1,
            1,
            True,
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("denominator",),
        ),
        (
            -1,
            1,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.AMOUNT_OUT_OF_RANGE,
            ("amount",),
        ),
        (
            MAX_FEE_AMOUNT_V2 + 1,
            1,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.AMOUNT_OUT_OF_RANGE,
            ("amount",),
        ),
        (
            1,
            -1,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.WEIGHT_OUT_OF_RANGE,
            ("weight",),
        ),
        (
            1,
            BPS_DENOMINATOR_V2 + 1,
            BPS_DENOMINATOR_V2,
            FeeQuotaRejectCodeV2.WEIGHT_OUT_OF_RANGE,
            ("weight",),
        ),
        (
            1,
            1,
            BPS_DENOMINATOR_V2 + 1,
            FeeQuotaRejectCodeV2.UNSUPPORTED_DENOMINATOR,
            ("denominator",),
        ),
    ),
)
def test_invalid_width_type_and_profile_inputs_reject_closed(
    amount: object,
    weight: object,
    denominator: object,
    code: FeeQuotaRejectCodeV2,
    path: tuple[str, ...],
) -> None:
    result = compute_fee_quota_v2(
        amount=amount,
        weight=weight,
        denominator=denominator,
    )
    assert result == FeeQuotaRejectV2(code, path)


def test_allocator_uses_the_quota_primitive(monkeypatch: pytest.MonkeyPatch) -> None:
    key = FeeApportionmentKeyV2("protocol-fees", "asset-a")
    policy = FeeDistributionPolicyV2(
        3_333,
        3_333,
        3_334,
        "buyback",
        "treasury",
        "rewards",
    )

    def reject_quota(
        *,
        amount: object,
        weight: object,
        denominator: object = BPS_DENOMINATOR_V2,
    ) -> FeeQuotaRejectV2:
        del amount, weight, denominator
        return FeeQuotaRejectV2(
            FeeQuotaRejectCodeV2.INTERNAL_RELATION_FAILURE,
            ("test",),
        )

    monkeypatch.setattr(allocator, "compute_fee_quota_v2", reject_quota)
    result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 1),),
        policy=policy,
        state=CommittedFeeApportionmentStateV2(
            "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
            (),
        ),
    )

    assert result == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
        ("relation", "quota"),
    )
