"""Route-owned asset-lane rejection codes at the V2 wire boundary."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
    _reject_code_type_for_route_v2,
)
from src.core.asset_lane_state_v2 import ASSET_LANE_PROFILE_AUTHENTICATION_V2
from src.core.asset_transfer_types_v2 import AssetTransferRejectCodeV2
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
)
from src.core.global_settlement_wire_codec_v2 import (
    GlobalSettlementWireCodecErrorV2,
    decode_global_settlement_wire_record_v2,
    encode_global_settlement_wire_record_v2,
)
from src.core.global_settlement_wire_records_v2 import (
    AssetLaneRejectedWireV2,
    wire_record_from_domain_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleRejectCodeV2

_ROOT = Path(__file__).resolve().parents[2]

_NONZERO_ROOT = "0x" + "11" * 32
_EMPTY_EFFECTS = GlobalEconomicEffectPlanV2.empty()
_ROUTE_CODE_TYPES = (
    (AssetLaneRouteV2.COORDINATOR, AssetLaneCoordinatorRejectCodeV2),
    (AssetLaneRouteV2.TRANSFER, AssetTransferRejectCodeV2),
    (AssetLaneRouteV2.MANAGED_LIFECYCLE, ManagedAssetLifecycleRejectCodeV2),
)


def _wire_rejection(
    route: AssetLaneRouteV2,
    code: object,
    *,
    effects: GlobalEconomicEffectPlanV2 = _EMPTY_EFFECTS,
    production_authority: str = "NONE",
    profile_authentication: str = ASSET_LANE_PROFILE_AUTHENTICATION_V2,
) -> AssetLaneRejectedWireV2:
    return AssetLaneRejectedWireV2(
        route,
        code,
        _NONZERO_ROOT,
        _NONZERO_ROOT,
        effects,
        production_authority,
        profile_authentication,
    )


def _raw_rejection(**changes: object) -> bytes:
    payload = _wire_rejection(
        AssetLaneRouteV2.COORDINATOR,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    ).to_canonical()
    payload.update(changes)
    return canonical_global_bytes_v2(payload)


def test_route_helper_and_wire_round_trip_preserve_exact_code_identity() -> None:
    for route, code_type in _ROUTE_CODE_TYPES:
        assert _reject_code_type_for_route_v2(route) is code_type
        for code in code_type:
            domain = AssetLaneRejectedV2(
                route,
                code,
                _NONZERO_ROOT,
                _NONZERO_ROOT,
                _EMPTY_EFFECTS,
            )
            record = wire_record_from_domain_v2(domain)
            encoded = encode_global_settlement_wire_record_v2(record)
            assert encoded == canonical_global_bytes_v2(record.to_canonical())

            decoded = decode_global_settlement_wire_record_v2(encoded)
            assert type(decoded) is AssetLaneRejectedWireV2
            assert decoded.route is route
            assert type(decoded.code) is code_type
            assert decoded.code is code
            assert encode_global_settlement_wire_record_v2(decoded) == encoded


def test_all_three_state_resource_limit_codes_remain_route_owned() -> None:
    for route, code_type in _ROUTE_CODE_TYPES:
        code = code_type.STATE_RESOURCE_LIMIT
        encoded = encode_global_settlement_wire_record_v2(_wire_rejection(route, code))
        decoded = decode_global_settlement_wire_record_v2(encoded)
        assert decoded.route is route
        assert type(decoded.code) is code_type
        assert decoded.code is code


def test_historical_transfer_rejection_bytes_remain_stable() -> None:
    golden_path = _ROOT / "tests" / "data" / "global_settlement_abi_v2_wire_records_golden.json"
    fixture = json.loads(golden_path.read_text(encoding="utf-8"))
    payload = fixture["records"]["AssetLaneRejectedWireV2"]
    raw = canonical_global_bytes_v2(payload["canonical"])

    assert hashlib.sha256(raw).hexdigest() == payload["canonical_bytes_sha256"]
    decoded = decode_global_settlement_wire_record_v2(raw)
    assert decoded.route is AssetLaneRouteV2.TRANSFER
    assert type(decoded.code) is AssetTransferRejectCodeV2
    assert decoded.code is AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT
    assert encode_global_settlement_wire_record_v2(decoded) == raw


@pytest.mark.parametrize(
    ("route", "wrong_code_type"),
    (
        (AssetLaneRouteV2.COORDINATOR, AssetTransferRejectCodeV2),
        (AssetLaneRouteV2.COORDINATOR, ManagedAssetLifecycleRejectCodeV2),
        (AssetLaneRouteV2.TRANSFER, AssetLaneCoordinatorRejectCodeV2),
        (AssetLaneRouteV2.TRANSFER, ManagedAssetLifecycleRejectCodeV2),
        (AssetLaneRouteV2.MANAGED_LIFECYCLE, AssetLaneCoordinatorRejectCodeV2),
        (AssetLaneRouteV2.MANAGED_LIFECYCLE, AssetTransferRejectCodeV2),
    ),
)
def test_domain_and_wire_rejections_reject_cross_route_enum_types(
    route: AssetLaneRouteV2,
    wrong_code_type: type[object],
) -> None:
    wrong_code = next(iter(wrong_code_type))
    with pytest.raises(TypeError, match="asset lane rejection is not closed"):
        AssetLaneRejectedV2(route, wrong_code, _NONZERO_ROOT, _NONZERO_ROOT, _EMPTY_EFFECTS)
    with pytest.raises(TypeError, match="wire asset lane rejection is not closed"):
        _wire_rejection(route, wrong_code)


@pytest.mark.parametrize("bad_route", ("TRANSFER", None, object()))
def test_route_helper_rejects_non_enum_routes(bad_route: object) -> None:
    with pytest.raises(TypeError, match="asset lane route"):
        _reject_code_type_for_route_v2(bad_route)


@pytest.mark.parametrize(
    ("bad_route", "message"),
    (
        ("NOT_A_ROUTE", "asset lane route is unknown"),
        (None, "asset lane route must be exact text"),
    ),
)
def test_decoder_rejects_unknown_or_malformed_routes(bad_route: object, message: str) -> None:
    with pytest.raises(GlobalSettlementWireCodecErrorV2, match=message):
        decode_global_settlement_wire_record_v2(_raw_rejection(route=bad_route))


def test_decoder_rejects_unknown_code_after_route_selection() -> None:
    with pytest.raises(
        GlobalSettlementWireCodecErrorV2,
        match="asset lane reject code is unknown",
    ):
        decode_global_settlement_wire_record_v2(_raw_rejection(code="NOT_A_REJECT_CODE"))


@pytest.mark.parametrize(
    ("field", "value", "message"),
    (
        ("production_authority", "VERIFIED", "must remain NONE"),
        ("profile_authentication", "VERIFIED", "must remain SHADOW"),
    ),
)
def test_rejection_wire_preserves_none_shadow_boundary(
    field: str,
    value: str,
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        _wire_rejection(
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
            **{field: value},
        )
    with pytest.raises(GlobalSettlementWireCodecErrorV2, match=message):
        decode_global_settlement_wire_record_v2(_raw_rejection(**{field: value}))


def test_rejection_domain_and_wire_require_empty_effects() -> None:
    nonempty_effects = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (LaneWriteV2(LaneIdV2.ASSET_TRANSFER, _NONZERO_ROOT, _NONZERO_ROOT),),
        (),
        (),
    )
    with pytest.raises(ValueError, match="exact no-op"):
        AssetLaneRejectedV2(
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
            _NONZERO_ROOT,
            _NONZERO_ROOT,
            nonempty_effects,
        )
    with pytest.raises(ValueError, match="exact no-op"):
        _wire_rejection(
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
            effects=nonempty_effects,
        )


def test_wire_rejection_roots_are_nonzero_even_for_an_empty_effect() -> None:
    with pytest.raises(ValueError, match="must be nonzero"):
        AssetLaneRejectedV2(
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
            ZERO_ROOT_V2,
            ZERO_ROOT_V2,
            _EMPTY_EFFECTS,
        )
    with pytest.raises(ValueError, match="must be nonzero"):
        AssetLaneRejectedWireV2(
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
            ZERO_ROOT_V2,
            ZERO_ROOT_V2,
            _EMPTY_EFFECTS,
            "NONE",
            ASSET_LANE_PROFILE_AUTHENTICATION_V2,
        )
