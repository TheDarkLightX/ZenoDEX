"""Governed market-identity obligations for the SHADOW perps margin leaf."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.lane_module_release_route_binding_v1 import (
    bind_perps_margin_lane_output_to_release_route_v1,
)
from src.core.perps_market_policy_v1 import PerpsMarketPolicyV1
from tests.core.test_perps_margin_release_receipt_binding_v1 import (
    BASE_ASSET,
    MARKET_ID,
    ORACLE_ID,
    QUOTE_ASSET,
    _binding_candidate,
    _fixture,
)


def test_market_policy_root_is_canonical_and_base_asset_substitution_rejects() -> None:
    # Arrange.
    policy = PerpsMarketPolicyV1(
        MARKET_ID,
        BASE_ASSET,
        QUOTE_ASSET,
        ORACLE_ID,
    )
    substituted = _fixture(with_position=True, base_asset="WBTC")

    # Act / Assert.
    assert policy.policy_root == (
        "0xa41728c33880ba70f198f632be3f9677ef683a710ffe999b281689127edd505a"
    )
    with pytest.raises(ValueError, match="market policy base asset mismatch"):
        bind_perps_margin_lane_output_to_release_route_v1(
            _binding_candidate(substituted, substituted.verified_price)
        )


def test_market_policy_root_and_profile_registry_substitutions_reject() -> None:
    fixture = _fixture(with_position=True)
    candidate = _binding_candidate(fixture, fixture.verified_price)
    wrong_policy = replace(candidate.market_policy, base_asset="WBTC")

    with pytest.raises(ValueError, match="market policy root mismatch"):
        bind_perps_margin_lane_output_to_release_route_v1(
            replace(candidate, market_policy=wrong_policy)
        )

    wrong_registry = replace(
        candidate.policy_registry,
        bindings=candidate.policy_registry.bindings[:-1],
    )
    with pytest.raises(ValueError, match="policy registry is outside the profile"):
        bind_perps_margin_lane_output_to_release_route_v1(
            replace(candidate, policy_registry=wrong_registry)
        )


@pytest.mark.parametrize(
    "field",
    ("market_id", "base_asset", "quote_asset", "oracle_id"),
)
def test_market_policy_rejects_empty_identifiers(field: str) -> None:
    values = {
        "market_id": MARKET_ID,
        "base_asset": BASE_ASSET,
        "quote_asset": QUOTE_ASSET,
        "oracle_id": ORACLE_ID,
    }
    values[field] = ""

    with pytest.raises(ValueError):
        PerpsMarketPolicyV1(**values)


def test_market_policy_rejects_same_base_and_quote_asset() -> None:
    with pytest.raises(ValueError, match="distinct"):
        PerpsMarketPolicyV1(MARKET_ID, QUOTE_ASSET, QUOTE_ASSET, ORACLE_ID)


def test_market_policy_identifier_length_bva_accepts_160_and_rejects_161_bytes() -> None:
    # Arrange.
    at_limit = "M" * 160
    over_limit = "M" * 161

    # Act.
    accepted = PerpsMarketPolicyV1(at_limit, BASE_ASSET, QUOTE_ASSET, ORACLE_ID)

    # Assert.
    assert accepted.market_id == at_limit
    with pytest.raises(ValueError, match="exceeds 160 UTF-8 bytes"):
        PerpsMarketPolicyV1(over_limit, BASE_ASSET, QUOTE_ASSET, ORACLE_ID)
