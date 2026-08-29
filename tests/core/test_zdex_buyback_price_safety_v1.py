from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import MAX_ATOMS_V1
from src.core.zdex_buyback_price_safety_v1 import (
    VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXBuybackPriceSafetyRejectCodeV1,
    ZDEXBuybackPriceSafetyRejectedV1,
    verify_zdex_buyback_price_safety_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy() -> ZDEXBuybackPriceSafetyPolicyV1:
    return ZDEXBuybackPriceSafetyPolicyV1(
        oracle_id="zdex-buyback-oracle",
        maximum_oracle_age_blocks=3,
        minimum_quote_reserve_atoms=500,
        minimum_zdex_reserve_atoms=200,
        maximum_pool_oracle_deviation_bps=500,
        maximum_execution_impact_bps=500,
        maximum_oracle_execution_deviation_bps=1_000,
        maximum_quote_reserve_spend_bps=2_000,
    )


def _observation() -> ZDEXBuybackPriceSafetyObservationV1:
    return ZDEXBuybackPriceSafetyObservationV1(
        oracle_occurrence_root=_root(1),
        current_height=77,
        oracle_observed_height=76,
        oracle_quote_numerator_atoms=4,
        oracle_zdex_denominator_atoms=1,
        quote_reserve_atoms=1_000,
        zdex_reserve_atoms=250,
        quote_amount_in_atoms=100,
        purchased_zdex_atoms=24,
        claimed_route_safe_quote_limit_atoms=200,
        claimed_minimum_output_atoms=23,
    )


def _code(observation: ZDEXBuybackPriceSafetyObservationV1):
    result = verify_zdex_buyback_price_safety_v1(_policy(), observation)
    assert isinstance(result, ZDEXBuybackPriceSafetyRejectedV1)
    return result.code


def test_exact_integer_price_envelope_accepts_and_matches_rust_roots() -> None:
    # Arrange / Act.
    policy = _policy()
    observation = _observation()
    result = verify_zdex_buyback_price_safety_v1(policy, observation)

    # Assert.
    assert isinstance(result, VerifiedZDEXBuybackPriceSafetyV1)
    assert result.route_safe_quote_limit_atoms == 200
    assert result.minimum_output_atoms == 23
    assert policy.policy_root == (
        "0xa0bad2275012b07b60962ef5fc75cf0c02c46e95772062c9b8c3c98a95b95d69"
    )
    assert observation.observation_root == (
        "0xcaee810d431a967702c20a76df988014dde2b063c7fab375a1ae972f80b8b915"
    )


@pytest.mark.parametrize(
    ("change", "expected"),
    (
        ({"oracle_observed_height": 78}, ZDEXBuybackPriceSafetyRejectCodeV1.HEIGHT_REGRESSION),
        ({"oracle_observed_height": 73}, ZDEXBuybackPriceSafetyRejectCodeV1.STALE_ORACLE),
        ({"quote_reserve_atoms": 499}, ZDEXBuybackPriceSafetyRejectCodeV1.INSUFFICIENT_DEPTH),
        ({"zdex_reserve_atoms": 199}, ZDEXBuybackPriceSafetyRejectCodeV1.INSUFFICIENT_DEPTH),
        ({"zdex_reserve_atoms": 300}, ZDEXBuybackPriceSafetyRejectCodeV1.POOL_ORACLE_DEVIATION),
        (
            {"purchased_zdex_atoms": 22},
            ZDEXBuybackPriceSafetyRejectCodeV1.MINIMUM_OUTPUT_NOT_MET,
        ),
        (
            {"quote_amount_in_atoms": 201, "purchased_zdex_atoms": 49},
            ZDEXBuybackPriceSafetyRejectCodeV1.QUOTE_LIMIT_EXCEEDED,
        ),
        (
            {"purchased_zdex_atoms": 251},
            ZDEXBuybackPriceSafetyRejectCodeV1.OUTPUT_EXCEEDS_RESERVE,
        ),
        (
            {"claimed_route_safe_quote_limit_atoms": 199},
            ZDEXBuybackPriceSafetyRejectCodeV1.DERIVED_LIMIT_MISMATCH,
        ),
        (
            {"claimed_minimum_output_atoms": 24},
            ZDEXBuybackPriceSafetyRejectCodeV1.DERIVED_MINIMUM_OUTPUT_MISMATCH,
        ),
    ),
)
def test_one_defect_rejects_with_typed_reason(
    change: dict[str, int],
    expected: ZDEXBuybackPriceSafetyRejectCodeV1,
) -> None:
    assert _code(replace(_observation(), **change)) is expected  # type: ignore[arg-type]


def test_pool_oracle_and_execution_boundaries_accept_at_equality() -> None:
    # The nominal fixture uses an exact pool/Oracle price equality, and its
    # minimum output is the exact Oracle-envelope ceiling.
    result = verify_zdex_buyback_price_safety_v1(_policy(), _observation())
    assert isinstance(result, VerifiedZDEXBuybackPriceSafetyV1)


def test_execution_impact_is_independently_enforced() -> None:
    policy = replace(_policy(), maximum_execution_impact_bps=100)

    result = verify_zdex_buyback_price_safety_v1(policy, _observation())

    assert isinstance(result, ZDEXBuybackPriceSafetyRejectedV1)
    assert result.code is ZDEXBuybackPriceSafetyRejectCodeV1.EXECUTION_IMPACT


def test_checked_cross_multiplication_rejects_overflow() -> None:
    observation = replace(
        _observation(),
        oracle_quote_numerator_atoms=MAX_ATOMS_V1,
    )
    assert _code(observation) is ZDEXBuybackPriceSafetyRejectCodeV1.ARITHMETIC_OVERFLOW


def test_policy_bva_rejects_unbounded_bps_and_zero_depth() -> None:
    with pytest.raises(ValueError, match="below 10000"):
        replace(_policy(), maximum_execution_impact_bps=10_000)
    with pytest.raises(ValueError, match="positive"):
        replace(_policy(), minimum_quote_reserve_atoms=0)


def test_verified_price_witness_is_opaque_and_immutable() -> None:
    result = verify_zdex_buyback_price_safety_v1(_policy(), _observation())
    assert isinstance(result, VerifiedZDEXBuybackPriceSafetyV1)
    with pytest.raises(TypeError, match="core-constructed"):
        VerifiedZDEXBuybackPriceSafetyV1(object(), object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        result._fields = object()  # type: ignore[assignment]
