"""Obligation evidence for typed price payloads under finalized Oracle roots.

RIPR target: a perps consumer must never accept a caller-selected price merely
because the command also names a finalized generic Oracle occurrence.  The
payload root is an independent fixed-vector oracle for the exact market, asset,
quote, price-e8, and observation height consumed by the route-bound authority.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_oracle_occurrence_authority_v1 import (
    GlobalOracleOccurrenceAuthorityCandidateV1,
    GlobalOracleOccurrencePolicyV1,
    verify_global_oracle_occurrence_authority_v1,
)
from src.core.global_oracle_price_occurrence_v1 import (
    GlobalOraclePriceOccurrenceV1,
    VerifiedGlobalOraclePriceV1,
    verify_global_oracle_price_occurrence_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ReleaseStatusV1,
    RouteReleaseV1,
)

ORACLE_ID = "zenodex.oracle.perps-index-price.v1"
MARKET_ID = "BTC-ZUSD-PERP"
BASE_ASSET = "BTC"
QUOTE_ASSET = "zUSD"
PRICE_E8 = 6_500_000_000_000


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _payload(
    *,
    price_e8: int = PRICE_E8,
    observed_height: int = 40,
) -> GlobalOraclePriceOccurrenceV1:
    return GlobalOraclePriceOccurrenceV1(
        oracle_id=ORACLE_ID,
        market_id=MARKET_ID,
        base_asset=BASE_ASSET,
        quote_asset=QUOTE_ASSET,
        price_e8=price_e8,
        observed_height=observed_height,
    )


def _authority(payload: GlobalOraclePriceOccurrenceV1):
    policy = GlobalOracleOccurrencePolicyV1(ORACLE_ID, 1)
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-price-occurrence-test",
        command_kind="perps_margin_withdraw",
        ordered_lanes=(LaneIdV1.PERPS_MARKET,),
        module_release_ids=(_root(101),),
        dependency_roles=("PERPS_MARGIN",),
        port_schema_roots=(_root(102),),
        guest_image_id=_root(103),
        specification_root=_root(104),
        source_root=_root(105),
        toolchain_root=_root(106),
        oracle_policy_root=policy.policy_root,
        issue_burn_policy_root=_root(107),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    state = GlobalEconomicStateV1(
        chain_id="zeno-oracle-price-test",
        deployment_root=_root(201),
        writer_epoch=7,
        height=41,
        profile_root=_root(202),
        lane_roots=tuple(
            LaneStateRootV1(
                lane_id=lane_id,
                module_release_id=_root(300 + index),
                enabled=lane_id is LaneIdV1.PERPS_MARKET,
                state_root=_root(400 + index),
            )
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
        oracle_occurrences=(
            OracleOccurrenceStateV1(
                oracle_id=ORACLE_ID,
                occurrence_root=payload.occurrence_root,
                observed_height=payload.observed_height,
                finalized=True,
            ),
        ),
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        height=42,
        tx_index=0,
        op_index=0,
        command_kind=route.command_kind,
        command_body_hash=_root(501),
        route_release_id=route.route_release_id,
        subject_id="alice",
        grant_root=_root(502),
        nonce=1,
        profile_root=state.profile_root,
        pre_state_root=state.state_root,
        consumed_object_ids=(ORACLE_ID,),
    )
    return verify_global_oracle_occurrence_authority_v1(
        GlobalOracleOccurrenceAuthorityCandidateV1(
            pre_state=state,
            route=route,
            occurrence=occurrence,
            policy=policy,
        )
    )


def test_given_finalized_root_when_payload_matches_then_exact_price_is_verified() -> None:
    # Arrange.
    payload = _payload()
    authority = _authority(payload)

    # Act.
    verified = verify_global_oracle_price_occurrence_v1(authority, payload)

    # Assert.
    assert verified.oracle_authority_root == authority.authority_root
    assert verified.command_occurrence_id == authority.command_occurrence_id
    assert verified.occurrence_root == payload.occurrence_root
    assert verified.market_id == MARKET_ID
    assert verified.base_asset == BASE_ASSET
    assert verified.quote_asset == QUOTE_ASSET
    assert verified.price_e8 == PRICE_E8
    assert payload.occurrence_root == (
        "0x9805b6e0554b0b824cb35c5e5e9ef23bd6951a1d9ca0a6fa996ed36a94060729"
    )


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("oracle_id", "zenodex.oracle.other-price.v1"),
        ("market_id", "ETH-ZUSD-PERP"),
        ("base_asset", "ETH"),
        ("quote_asset", "USDC"),
        ("price_e8", PRICE_E8 + 1),
        ("observed_height", 39),
    ),
)
def test_one_field_payload_substitution_rejects_before_price_authority(
    field: str,
    replacement: object,
) -> None:
    # Arrange: authority commits the unmodified payload root.
    payload = _payload()
    authority = _authority(payload)
    substituted = replace(payload, **{field: replacement})

    # Act / Assert.
    with pytest.raises(ValueError, match="occurrence root|observed height|oracle id"):
        verify_global_oracle_price_occurrence_v1(authority, substituted)


@pytest.mark.parametrize("price_e8", (0, 1, MAX_ATOMS_V1))
def test_price_e8_boundary_contract(price_e8: int) -> None:
    if price_e8 == 0:
        with pytest.raises(ValueError, match="positive"):
            _payload(price_e8=price_e8)
        return
    payload = _payload(price_e8=price_e8)
    verified = verify_global_oracle_price_occurrence_v1(
        _authority(payload),
        payload,
    )
    assert verified.price_e8 == price_e8


def test_verified_price_constructor_and_object_new_are_fail_closed() -> None:
    with pytest.raises(TypeError, match="checker-constructed"):
        VerifiedGlobalOraclePriceV1(object(), object())
    forged = object.__new__(VerifiedGlobalOraclePriceV1)
    with pytest.raises(TypeError, match="checker-registered"):
        _ = forged.price_e8
