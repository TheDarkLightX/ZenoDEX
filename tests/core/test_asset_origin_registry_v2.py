from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace

import pytest

from src.core.asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
    AssetOriginKindV2,
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import (
    managed_asset_policy_root_v2,
    transition_asset_origin_registration_v2,
    validate_asset_transfer_policy_origin_v2,
    validate_managed_asset_policy_origin_v2,
)
from src.core.asset_transfer_types_v2 import (
    ASSET_ATOM_DECIMALS_V2,
    AssetClassV2,
    AssetTransferPolicyV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import ZERO_ROOT_V2, hash_global_v2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecyclePolicyV2


def _root(label: str) -> str:
    return hash_global_v2("asset-origin-test-root-v2", {"label": label})


def _transfer_policy(asset: str = "USD") -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset=asset,
        fee_owner="treasury",
        transfer_fee_atoms=2,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(f"origin:{asset}"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )


def _command(
    *,
    asset: str = "USD",
    origin_kind: AssetOriginKindV2 = AssetOriginKindV2.TAU_ORIGINATED,
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    origin_root: str | None = None,
    transfer_policy_root: str | None = None,
    issue_policy_root: str = ZERO_ROOT_V2,
) -> AssetOriginRegistrationCommandV2:
    selected_transfer_policy_root = transfer_policy_root
    if selected_transfer_policy_root is None:
        selected_transfer_policy_root = (
            hash_global_v2("asset-transfer-policy-v2", _transfer_policy(asset))
            if asset_class is AssetClassV2.REGISTERED_ORDINARY_TOKEN
            else _root(f"transfer-policy:{asset}:{asset_class.value}")
        )
    return AssetOriginRegistrationCommandV2(
        command_kind=ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
        asset=asset,
        origin_kind=origin_kind,
        origin_root=origin_root or _root(f"origin:{asset}"),
        transfer_policy_root=selected_transfer_policy_root,
        issue_policy_root=issue_policy_root,
        decimals=ASSET_ATOM_DECIMALS_V2,
        asset_class=asset_class,
    )


def _state() -> AssetOriginRegistryStateV2:
    return AssetOriginRegistryStateV2(
        module_release_id=_root("module-release"),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root("grant"),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=(),
    )


def _context(
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
    *,
    subject: str = "governance",
    grant_root: str | None = None,
    nonce: int = 1,
) -> AssetOriginRegistrationContextV2:
    global_pre_state_root = _root(f"global-pre:{nonce}")
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="asset-origin-test",
        deployment_root=_root("deployment"),
        height=8,
        tx_index=0,
        op_index=0,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root("route-release"),
        subject_id=subject,
        grant_root=grant_root or _root("grant"),
        nonce=nonce,
        profile_root=_root("profile"),
        pre_state_root=global_pre_state_root,
        consumed_object_ids=(),
    )
    return AssetOriginRegistrationContextV2(
        writer_epoch=3,
        module_release_id=state.module_release_id,
        global_pre_state_root=global_pre_state_root,
        occurrence=occurrence,
    )


def _assert_noop(
    result: AssetOriginRegistrationRejectedV2,
    expected: AssetOriginRegistrationRejectCodeV2,
    state: AssetOriginRegistryStateV2,
) -> None:
    assert result.code is expected
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty


def test_registration_binds_transfer_policy_without_issuing_value() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)

    result = transition_asset_origin_registration_v2(context, state, command)

    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    assert result.post_state.assets[0].asset == "USD"
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.occurrence_consumptions == (context.occurrence.occurrence_id,)
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V2
    assert result.module_journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
    assert result.production_authority == "NONE"
    assert (
        validate_asset_transfer_policy_origin_v2(
            result.post_state,
            _transfer_policy(),
        )
        == result.post_state.assets[0]
    )


@pytest.mark.parametrize(
    "root_field",
    (
        "private_port_root",
        "terminal_obligations_root",
        "oracle_occurrence_plan_root",
    ),
)
def test_accepted_registration_requires_zero_external_roots(root_field: str) -> None:
    state = _state()
    command = _command()
    result = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)

    with pytest.raises(ValueError, match="unrelated plan"):
        AssetOriginRegistrationAcceptedV2(
            result.post_state,
            result.effects,
            replace(result.module_journal, **{root_field: _root(root_field)}),
        )


def test_transfer_policy_drift_fails_registry_admission() -> None:
    state = _state()
    command = _command()
    result = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)

    with pytest.raises(ValueError, match="transfer policy root"):
        validate_asset_transfer_policy_origin_v2(
            result.post_state,
            replace(_transfer_policy(), transfer_fee_atoms=3),
        )


def test_managed_issue_policy_is_bound_to_the_same_origin_record() -> None:
    managed_policy = ManagedAssetLifecyclePolicyV2(
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root("origin:USD"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject="issuer",
        issue_authorization_root=_root("managed-issue"),
        burn_authorization_root=_root("managed-burn"),
        enabled=True,
    )
    state = _state()
    command = _command(issue_policy_root=managed_asset_policy_root_v2(managed_policy))
    result = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)

    assert validate_managed_asset_policy_origin_v2(
        result.post_state,
        managed_policy,
    ) == result.post_state.assets[0]
    with pytest.raises(ValueError, match="issue policy root"):
        validate_managed_asset_policy_origin_v2(
            result.post_state,
            replace(managed_policy, enabled=False),
        )


@pytest.mark.parametrize(
    ("mutate", "expected"),
    (
        (
            lambda context: replace(context, occurrence=None),
            AssetOriginRegistrationRejectCodeV2.MISSING_OCCURRENCE,
        ),
        (
            lambda context: replace(
                context,
                global_pre_state_root=_root("wrong-global-pre"),
            ),
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            lambda context: replace(
                context,
                occurrence=replace(
                    context.occurrence,
                    command_body_hash=_root("wrong-command"),
                ),
            ),
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH,
        ),
    ),
)
def test_occurrence_failures_are_exact_noops(
    mutate: Callable[
        [AssetOriginRegistrationContextV2],
        AssetOriginRegistrationContextV2,
    ],
    expected: AssetOriginRegistrationRejectCodeV2,
) -> None:
    state = _state()
    command = _command()
    context = _context(state, command)

    result = transition_asset_origin_registration_v2(
        mutate(context),
        state,
        command,
    )

    assert isinstance(result, AssetOriginRegistrationRejectedV2)
    _assert_noop(result, expected, state)


def test_subject_grant_and_decimal_rejections_are_exact_noops() -> None:
    state = _state()
    command = _command()
    cases = (
        (
            _context(state, command, subject="mallory"),
            command,
            AssetOriginRegistrationRejectCodeV2.UNAUTHORIZED_SUBJECT,
        ),
        (
            _context(state, command, grant_root=_root("wrong-grant")),
            command,
            AssetOriginRegistrationRejectCodeV2.GRANT_MISMATCH,
        ),
        (
            _context(state, replace(command, decimals=7)),
            replace(command, decimals=7),
            AssetOriginRegistrationRejectCodeV2.DECIMAL_SCALE_MISMATCH,
        ),
    )
    for context, selected_command, expected in cases:
        result = transition_asset_origin_registration_v2(
            context,
            state,
            selected_command,
        )
        assert isinstance(result, AssetOriginRegistrationRejectedV2)
        _assert_noop(result, expected, state)


def test_duplicate_asset_and_origin_are_distinct_noop_rejections() -> None:
    state = _state()
    command = _command()
    first = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(first, AssetOriginRegistrationAcceptedV2)

    duplicate_asset = replace(command, origin_root=_root("other-origin"))
    asset_result = transition_asset_origin_registration_v2(
        _context(first.post_state, duplicate_asset, nonce=2),
        first.post_state,
        duplicate_asset,
    )
    duplicate_origin = _command(asset="EUR", origin_root=command.origin_root)
    origin_result = transition_asset_origin_registration_v2(
        _context(first.post_state, duplicate_origin, nonce=3),
        first.post_state,
        duplicate_origin,
    )

    assert isinstance(asset_result, AssetOriginRegistrationRejectedV2)
    _assert_noop(
        asset_result,
        AssetOriginRegistrationRejectCodeV2.DUPLICATE_ASSET,
        first.post_state,
    )
    assert isinstance(origin_result, AssetOriginRegistrationRejectedV2)
    _assert_noop(
        origin_result,
        AssetOriginRegistrationRejectCodeV2.DUPLICATE_ORIGIN,
        first.post_state,
    )


def test_native_origin_remains_fail_closed() -> None:
    state = _state()
    native = _command(
        asset="TAU",
        origin_kind=AssetOriginKindV2.NATIVE,
        asset_class=AssetClassV2.TAU_NATIVE_COIN,
    )

    result = transition_asset_origin_registration_v2(
        _context(state, native),
        state,
        native,
    )

    assert isinstance(result, AssetOriginRegistrationRejectedV2)
    _assert_noop(
        result,
        AssetOriginRegistrationRejectCodeV2.NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
        state,
    )


def test_registry_state_owns_record_snapshots() -> None:
    state = _state()
    command = _command()
    result = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    record = result.post_state.assets[0]
    owned = AssetOriginRegistryStateV2(
        result.post_state.module_release_id,
        result.post_state.policy,
        (record,),
    )
    root = owned.state_root

    object.__setattr__(record, "origin_root", _root("mutated-origin"))

    assert owned.state_root == root
    assert owned.assets[0].origin_root == command.origin_root


def test_transition_rejects_hostile_command_subclass() -> None:
    class HostileCommand(AssetOriginRegistrationCommandV2):
        pass

    state = _state()
    command = _command()
    hostile = HostileCommand(
        command.command_kind,
        command.asset,
        command.origin_kind,
        command.origin_root,
        command.transfer_policy_root,
        command.issue_policy_root,
        command.decimals,
        command.asset_class,
    )

    with pytest.raises(TypeError, match="exact typed value"):
        transition_asset_origin_registration_v2(
            _context(state, command),
            state,
            hostile,
        )
