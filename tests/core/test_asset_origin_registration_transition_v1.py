"""AAA/RIPR evidence for profile-gated asset-origin registration."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_origin_registration_transition_v1 import (
    ASSET_ATOM_DECIMALS_V1,
    AssetOriginKindV1,
    AssetOriginRegistrationAcceptedV1,
    AssetOriginRegistrationContextV1,
    AssetOriginRegistrationPolicyV1,
    AssetOriginRegistrationRejectCodeV1,
    AssetOriginRegistrationRejectedV1,
    AssetOriginRegistrationStateV1,
    RegisterAssetOriginV1,
    transition_asset_origin_registration_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy() -> AssetOriginRegistrationPolicyV1:
    return AssetOriginRegistrationPolicyV1(
        authority_subject="governance",
        authority_grant_root=_root(10),
        allow_native=True,
        allow_tau_originated=True,
    )


def _state() -> AssetOriginRegistrationStateV1:
    return AssetOriginRegistrationStateV1(_root(20), _policy(), ())


def _context(**changes: object) -> AssetOriginRegistrationContextV1:
    values: dict[str, object] = {
        "chain_id": "asset-origin-test",
        "deployment_root": _root(1),
        "profile_root": _root(2),
        "writer_epoch": 3,
        "module_release_id": _root(20),
        "command_occurrence_id": _root(30),
        "subject_id": "governance",
        "grant_root": _root(10),
    }
    values.update(changes)
    return AssetOriginRegistrationContextV1(**values)  # type: ignore[arg-type]


def _command(**changes: object) -> RegisterAssetOriginV1:
    values: dict[str, object] = {
        "command_kind": "register_asset_origin",
        "asset": "TAU",
        "origin_kind": AssetOriginKindV1.TAU_ORIGINATED,
        "origin_root": _root(40),
        "transfer_policy_root": _root(41),
        "issue_policy_root": _root(42),
        "decimals": ASSET_ATOM_DECIMALS_V1,
    }
    values.update(changes)
    return RegisterAssetOriginV1(**values)  # type: ignore[arg-type]


def test_tau_origin_registration_is_zero_issue_and_exactly_bound() -> None:
    # Arrange
    state = _state()

    # Act
    result = transition_asset_origin_registration_v1(_context(), state, _command())

    # Assert
    assert isinstance(result, AssetOriginRegistrationAcceptedV1)
    assert result.post_state.assets[0].asset == "TAU"
    assert result.post_state.assets[0].origin_kind is AssetOriginKindV1.TAU_ORIGINATED
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.occurrence_consumptions == (_root(30),)
    assert result.effects.lane_writes[0].pre_root == state.state_root
    assert result.effects.lane_writes[0].post_root == result.post_state.state_root


@pytest.mark.parametrize(
    ("context", "command", "expected"),
    (
        (_context(module_release_id=_root(21)), _command(), AssetOriginRegistrationRejectCodeV1.RELEASE_MISMATCH),
        (_context(subject_id="mallory"), _command(), AssetOriginRegistrationRejectCodeV1.UNAUTHORIZED_SUBJECT),
        (_context(grant_root=_root(11)), _command(), AssetOriginRegistrationRejectCodeV1.GRANT_MISMATCH),
        (_context(), _command(command_kind="unknown"), AssetOriginRegistrationRejectCodeV1.UNKNOWN_COMMAND),
        (_context(), _command(decimals=7), AssetOriginRegistrationRejectCodeV1.DECIMAL_SCALE_MISMATCH),
    ),
)
def test_registration_rejections_are_exact_noops(
    context: AssetOriginRegistrationContextV1,
    command: RegisterAssetOriginV1,
    expected: AssetOriginRegistrationRejectCodeV1,
) -> None:
    # Arrange
    state = _state()

    # Act
    result = transition_asset_origin_registration_v1(context, state, command)

    # Assert
    assert isinstance(result, AssetOriginRegistrationRejectedV1)
    assert result.code is expected
    assert result.pre_state == result.post_state == state
    assert result.effects.is_empty


def test_duplicate_asset_and_origin_are_each_rejected_without_effects() -> None:
    # Arrange
    first = transition_asset_origin_registration_v1(_context(), _state(), _command())
    assert isinstance(first, AssetOriginRegistrationAcceptedV1)

    # Act
    duplicate_asset = transition_asset_origin_registration_v1(
        _context(command_occurrence_id=_root(31)),
        first.post_state,
        _command(origin_root=_root(43)),
    )
    duplicate_origin = transition_asset_origin_registration_v1(
        _context(command_occurrence_id=_root(32)),
        first.post_state,
        _command(asset="TAU-ALIAS"),
    )

    # Assert
    assert isinstance(duplicate_asset, AssetOriginRegistrationRejectedV1)
    assert duplicate_asset.code is AssetOriginRegistrationRejectCodeV1.DUPLICATE_ASSET
    assert isinstance(duplicate_origin, AssetOriginRegistrationRejectedV1)
    assert duplicate_origin.code is AssetOriginRegistrationRejectCodeV1.DUPLICATE_ORIGIN
    assert duplicate_asset.effects.is_empty and duplicate_origin.effects.is_empty


def test_native_registration_is_policy_gated_and_unique() -> None:
    # Arrange
    disabled = replace(_state(), policy=replace(_policy(), allow_native=False))
    native = _command(
        asset="ZENO-NATIVE",
        origin_kind=AssetOriginKindV1.NATIVE,
        origin_root=_root(50),
    )

    # Act
    rejected = transition_asset_origin_registration_v1(_context(), disabled, native)
    accepted = transition_asset_origin_registration_v1(_context(), _state(), native)

    # Assert
    assert isinstance(rejected, AssetOriginRegistrationRejectedV1)
    assert rejected.code is AssetOriginRegistrationRejectCodeV1.DISABLED_ORIGIN_KIND
    assert isinstance(accepted, AssetOriginRegistrationAcceptedV1)
    assert accepted.post_state.assets[0].origin_kind is AssetOriginKindV1.NATIVE
