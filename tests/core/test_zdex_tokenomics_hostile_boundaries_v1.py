from __future__ import annotations

from collections.abc import Iterator
from typing import NoReturn

import pytest

from src.core.zdex_fee_allocation_profile_binding_v1 import (
    bind_zdex_fee_allocation_shadow_profile_v1,
)
from src.core.zdex_tokenomics_fee_lane_coordinator_v1 import (
    compose_zdex_tokenomics_fee_allocation_lane_v1,
)
from src.core.zdex_tokenomics_fee_lane_receipt_verification_v1 import (
    verify_zdex_tokenomics_fee_lane_receipt_v1,
)
from src.core.zdex_tokenomics_lane_coordinator_v1 import (
    compose_zdex_tokenomics_burn_lane_v1,
)
from src.core.zdex_tokenomics_lane_receipt_verification_v1 import (
    bind_zdex_tokenomics_shadow_profile_v1,
    verify_zdex_tokenomics_lane_receipt_v1,
)
from tests.core.test_zdex_purchase_burn_route_v1 import _fee_lane_receipt_fixture
from tests.core.test_zdex_purchase_burn_route_v1 import (
    _Verifier as _FeeVerifier,
)
from tests.core.test_zdex_tokenomics_lane_coordinator_v1 import _receipt_fixture
from tests.core.test_zdex_tokenomics_lane_coordinator_v1 import (
    _Verifier as _BurnVerifier,
)


class _BehaviorBombStr(str):
    events: list[str] = []

    @classmethod
    def _explode(cls, event: str) -> NoReturn:
        cls.events.append(event)
        raise AssertionError(f"hostile {event} hook ran")

    def __eq__(self, other: object) -> bool:
        del other
        return self._explode("eq")

    def __ne__(self, other: object) -> bool:
        del other
        return self._explode("ne")

    def __hash__(self) -> int:
        return self._explode("hash")


class _BehaviorBombTuple(tuple[object, ...]):
    events: list[str] = []

    def __iter__(self) -> Iterator[object]:
        type(self).events.append("iter")
        raise AssertionError("hostile iterator ran")


class _BehaviorBombFields:
    def __init__(self) -> None:
        object.__setattr__(self, "events", [])

    def __getattribute__(self, name: str) -> object:
        if name == "events":
            return object.__getattribute__(self, name)
        events = object.__getattribute__(self, "events")
        events.append(name)
        raise AssertionError("hostile attribute hook ran")


def _reset_events() -> None:
    _BehaviorBombStr.events.clear()
    _BehaviorBombTuple.events.clear()


@pytest.mark.parametrize("lane", ("burn", "fee"))
def test_profile_binder_rejects_hostile_route_tuple_without_behavior(
    lane: str,
) -> None:
    # Arrange
    _reset_events()
    if lane == "burn":
        _, governed, _ = _receipt_fixture()
        fields = governed._fields
        bind = lambda: bind_zdex_tokenomics_shadow_profile_v1(  # noqa: E731
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=fields.profile,
        )
    else:
        _, governed = _fee_lane_receipt_fixture()
        fields = governed._fields
        bind = lambda: bind_zdex_fee_allocation_shadow_profile_v1(  # noqa: E731
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=fields.profile,
            policy_registry=fields.policy_registry,
        )
    object.__setattr__(
        fields.profile.route_registry,
        "routes",
        _BehaviorBombTuple(fields.profile.route_registry.routes),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="route registry routes must be an exact tuple"):
        bind()
    assert _BehaviorBombTuple.events == []


@pytest.mark.parametrize("lane", ("burn", "fee"))
def test_receipt_rejects_hostile_governed_fields_before_attribute_or_callback(
    lane: str,
) -> None:
    # Arrange
    hostile = _BehaviorBombFields()
    if lane == "burn":
        candidate, governed, _ = _receipt_fixture()
        verifier = _BurnVerifier()
        invoke = lambda: verify_zdex_tokenomics_lane_receipt_v1(  # noqa: E731
            candidate,
            governed,
            verifier,
        )
    else:
        candidate, governed = _fee_lane_receipt_fixture()
        verifier = _FeeVerifier()
        invoke = lambda: verify_zdex_tokenomics_fee_lane_receipt_v1(  # noqa: E731
            candidate,
            governed,
            verifier,
        )
    object.__setattr__(governed, "_fields", hostile)

    # Act / Assert
    with pytest.raises(TypeError, match="governed fields must be exact typed data"):
        invoke()
    assert hostile.events == []
    assert verifier.calls == []


@pytest.mark.parametrize("lane", ("burn", "fee"))
def test_receipt_rejects_hostile_context_scalar_before_behavior_or_callback(
    lane: str,
) -> None:
    # Arrange
    _reset_events()
    if lane == "burn":
        candidate, governed, _ = _receipt_fixture()
        verifier = _BurnVerifier()
        invoke = lambda: verify_zdex_tokenomics_lane_receipt_v1(  # noqa: E731
            candidate,
            governed,
            verifier,
        )
    else:
        candidate, governed = _fee_lane_receipt_fixture()
        verifier = _FeeVerifier()
        invoke = lambda: verify_zdex_tokenomics_fee_lane_receipt_v1(  # noqa: E731
            candidate,
            governed,
            verifier,
        )
    context = candidate.lane_candidate.context
    object.__setattr__(
        context,
        "profile_root",
        _BehaviorBombStr(context.profile_root),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        invoke()
    assert _BehaviorBombStr.events == []
    assert verifier.calls == []


@pytest.mark.parametrize("lane", ("burn", "fee"))
def test_composer_rejects_hostile_effect_tuple_without_behavior(lane: str) -> None:
    # Arrange
    _reset_events()
    if lane == "burn":
        candidate = _receipt_fixture()[0].lane_candidate
        effects = candidate.module_effects
        invoke = lambda: compose_zdex_tokenomics_burn_lane_v1(candidate)  # noqa: E731
    else:
        candidate = _fee_lane_receipt_fixture()[0].lane_candidate
        effects = candidate.allocation.effects
        invoke = lambda: compose_zdex_tokenomics_fee_allocation_lane_v1(  # noqa: E731
            candidate
        )
    object.__setattr__(effects, "rows", _BehaviorBombTuple(effects.rows))

    # Act / Assert
    with pytest.raises(TypeError, match="exact tuple"):
        invoke()
    assert _BehaviorBombTuple.events == []


@pytest.mark.parametrize("lane", ("burn", "fee"))
def test_composer_owns_accepted_state_and_effects(lane: str) -> None:
    # Arrange / Act
    if lane == "burn":
        candidate = _receipt_fixture()[0].lane_candidate
        result = compose_zdex_tokenomics_burn_lane_v1(candidate)
        source_effects = candidate.module_effects
    else:
        candidate = _fee_lane_receipt_fixture()[0].lane_candidate
        result = compose_zdex_tokenomics_fee_allocation_lane_v1(candidate)
        source_effects = candidate.allocation.effects
    state_root = result.post_state.staking_state_root
    effect_asset = result.effects.rows[0].asset

    # Mutate the caller-owned inputs after composition.
    object.__setattr__(candidate.post_state, "staking_state_root", "0x" + "f" * 64)
    object.__setattr__(source_effects.rows[0], "asset", "0x" + "e" * 64)

    # Assert
    assert result.post_state.staking_state_root == state_root
    assert result.effects.rows[0].asset == effect_asset
