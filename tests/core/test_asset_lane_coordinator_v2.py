"""Semantic obligations for the bounded V2 asset-lane coordinator."""

from __future__ import annotations

import pytest

import src.core.asset_lane_coordinator_v2 as coordinator_module
from src.core.asset_lane_coordinator_v2 import (
    AssetLaneAcceptedV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
    transition_asset_lane_v2,
)
from src.core.asset_lane_state_v2 import (
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
    ASSET_LANE_PROFILE_AUTHENTICATION_V2,
    AssetLaneContextV2,
    AssetLaneStateV2,
)
from src.core.asset_origin_registry_types_v2 import (
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import (
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferCommandV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    LaneIdV2,
    LaneWriteV2,
    hash_global_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
)


def _root(label: str) -> str:
    return hash_global_v2("asset-lane-coordinator-test-v2", {"label": label})


def _transfer_policy(
    *,
    asset: str = "USD",
    fee_owner: str = "treasury",
    fee_atoms: int = 2,
) -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset=asset,
        fee_owner=fee_owner,
        transfer_fee_atoms=fee_atoms,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(f"origin:{asset}"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )


def _managed_policy(*, asset: str = "USD") -> ManagedAssetLifecyclePolicyV2:
    return ManagedAssetLifecyclePolicyV2(
        asset=asset,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(f"origin:{asset}"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject="issuer",
        issue_authorization_root=_root(f"issue:{asset}"),
        burn_authorization_root=_root(f"burn:{asset}"),
        enabled=True,
    )


def _registry(
    transfer_policies: tuple[AssetTransferPolicyV2, ...],
    managed_policies: tuple[ManagedAssetLifecyclePolicyV2, ...],
    *,
    drift_transfer_asset: str | None = None,
) -> AssetOriginRegistryStateV2:
    managed_by_asset = {policy.asset: policy for policy in managed_policies}
    records = []
    for policy in transfer_policies:
        transfer_root = asset_transfer_policy_root_v2(policy)
        if drift_transfer_asset == policy.asset:
            transfer_root = _root(f"drift:{policy.asset}")
        managed = managed_by_asset.get(policy.asset)
        records.append(
            AssetOriginRecordV2(
                asset=policy.asset,
                origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
                origin_root=policy.asset_origin_root or _root("absent-origin"),
                transfer_policy_root=transfer_root,
                issue_policy_root=(
                    ZERO_ROOT_V2
                    if managed is None
                    else managed_asset_policy_root_v2(managed)
                ),
                decimals=policy.atom_decimals,
                asset_class=policy.asset_class,
            )
        )
    return AssetOriginRegistryStateV2(
        module_release_id=_root("module-release"),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root("governance-grant"),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=tuple(sorted(records, key=lambda row: row.asset)),
    )


def _state(
    *,
    transfer_policy: AssetTransferPolicyV2 | None = None,
    managed_policy: ManagedAssetLifecyclePolicyV2 | None = None,
    balances: tuple[EconomicAmountV2, ...] | None = None,
    supply_atoms: int = 1_000,
    registry_drift: bool = False,
) -> AssetLaneStateV2:
    transfer = transfer_policy or _transfer_policy()
    managed = managed_policy or _managed_policy()
    transfer_policies = (transfer,)
    managed_policies = (managed,)
    return AssetLaneStateV2(
        module_release_id=_root("module-release"),
        origin_registry=_registry(
            transfer_policies,
            managed_policies,
            drift_transfer_asset=transfer.asset if registry_drift else None,
        ),
        transfer_policies=transfer_policies,
        managed_policies=managed_policies,
        balances=(
            EconomicAmountV2(
                "alice",
                transfer.asset,
                ACCOUNT_CUSTODY_DOMAIN_V2,
                supply_atoms,
            ),
        )
        if balances is None and supply_atoms
        else (() if balances is None else balances),
        supplies=(AssetSupplyV2(transfer.asset, supply_atoms),),
    )


def _transfer_command(
    *,
    sender: str = "alice",
    recipient: str = "bob",
    amount_atoms: int = 100,
    max_fee_atoms: int = 2,
) -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="USD",
        sender=sender,
        recipient=recipient,
        amount_atoms=amount_atoms,
        max_fee_atoms=max_fee_atoms,
        asset_origin_root=_root("origin:USD"),
    )


def _managed_command(
    *,
    kind: str = MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    owner: str = "alice",
    amount_atoms: int = 50,
) -> ManagedAssetLifecycleCommandV2:
    authorization = "issue" if kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2 else "burn"
    return ManagedAssetLifecycleCommandV2(
        command_kind=kind,
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root("origin:USD"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        authorization_root=_root(f"{authorization}:USD"),
        account_owner=owner,
        amount_atoms=amount_atoms,
    )


def _context(
    command: AssetTransferCommandV2 | ManagedAssetLifecycleCommandV2,
    *,
    subject: str | None = None,
    grant_root: str | None = None,
    nonce: int = 1,
) -> AssetLaneContextV2:
    if type(command) is AssetTransferCommandV2:
        selected_subject = command.sender if subject is None else subject
        selected_grant = _root("transfer-grant") if grant_root is None else grant_root
    else:
        is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
        selected_subject = (
            "issuer" if is_issue else command.account_owner
        ) if subject is None else subject
        selected_grant = _root(
            f"{'issue' if is_issue else 'burn'}:USD"
        ) if grant_root is None else grant_root
    global_pre_root = _root(f"global-pre:{nonce}")
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="asset-lane-v2-test",
        deployment_root=_root("deployment"),
        height=8 + nonce,
        tx_index=0,
        op_index=0,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root("route-release"),
        subject_id=selected_subject,
        grant_root=selected_grant,
        nonce=nonce,
        profile_root=_root("profile"),
        pre_state_root=global_pre_root,
        consumed_object_ids=(),
    )
    return AssetLaneContextV2(
        writer_epoch=4,
        module_release_id=_root("module-release"),
        global_pre_state_root=global_pre_root,
        occurrence=occurrence,
    )


def _assert_noop(
    result: object,
    state: AssetLaneStateV2,
    code: object,
) -> AssetLaneRejectedV2:
    assert isinstance(result, AssetLaneRejectedV2)
    assert result.code is code
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.production_authority == ASSET_LANE_PRODUCTION_AUTHORITY_V2
    assert result.profile_authentication == ASSET_LANE_PROFILE_AUTHENTICATION_V2
    return result


def test_transfer_is_rebound_to_the_single_aggregate_lane_root() -> None:
    state = _state()
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)

    assert isinstance(result, AssetLaneAcceptedV2)
    assert result.route is AssetLaneRouteV2.TRANSFER
    assert result.post_state.balance_atoms("alice", "USD") == 898
    assert result.post_state.balance_atoms("bob", "USD") == 100
    assert result.post_state.balance_atoms("treasury", "USD") == 2
    assert result.post_state.supply_atoms("USD") == 1_000
    assert result.effects.lane_writes == (
        LaneWriteV2(
            LaneIdV2.ASSET_TRANSFER,
            state.state_root,
            result.post_state.state_root,
        ),
    )
    assert result.module_journal.pre_lane_root == state.state_root
    assert result.module_journal.post_lane_root == result.post_state.state_root
    assert result.module_journal.private_port_root == ZERO_ROOT_V2
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V2
    assert result.module_journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
    assert result.effects.external_outbox_enqueue == ()
    assert result.production_authority == "NONE"
    assert result.profile_authentication == "SHADOW"


@pytest.mark.parametrize("fee_owner", ("alice", "bob"))
def test_fee_owner_aliases_preserve_conservation(fee_owner: str) -> None:
    policy = _transfer_policy(fee_owner=fee_owner)
    state = _state(transfer_policy=policy)
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)

    assert isinstance(result, AssetLaneAcceptedV2)
    expected_alice = 900 if fee_owner == "alice" else 898
    expected_bob = 100 if fee_owner == "alice" else 102
    assert result.post_state.balance_atoms("alice", "USD") == expected_alice
    assert result.post_state.balance_atoms("bob", "USD") == expected_bob
    conservation = result.effects.asset_conservation[0]
    assert conservation.owned_and_custodied_pre_atoms == 1_000
    assert conservation.owned_and_custodied_post_atoms == 1_000
    assert conservation.supply_pre_atoms == conservation.supply_post_atoms == 1_000


def test_issue_and_burn_are_rebound_with_exact_supply_effects() -> None:
    state = _state()
    issue = _managed_command(amount_atoms=50)
    issued = transition_asset_lane_v2(_context(issue), state, issue)
    assert isinstance(issued, AssetLaneAcceptedV2)
    assert issued.route is AssetLaneRouteV2.MANAGED_LIFECYCLE
    assert issued.post_state.balance_atoms("alice", "USD") == 1_050
    assert issued.post_state.supply_atoms("USD") == 1_050
    assert {(row.kind, row.delta_atoms) for row in issued.effects.rows} == {
        (EconomicEffectKindV2.ACCOUNT_MOVEMENT, 50),
        (EconomicEffectKindV2.ISSUE, 50),
    }

    burn = _managed_command(
        kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        amount_atoms=25,
    )
    burned = transition_asset_lane_v2(
        _context(burn, nonce=2),
        issued.post_state,
        burn,
    )
    assert isinstance(burned, AssetLaneAcceptedV2)
    assert burned.post_state.balance_atoms("alice", "USD") == 1_025
    assert burned.post_state.supply_atoms("USD") == 1_025
    assert burned.effects.asset_conservation[0].authorized_burn_atoms == 25


def test_stateful_issue_transfer_burn_preserves_owned_equals_supply() -> None:
    state = _state()
    issue = _managed_command(amount_atoms=50)
    first = transition_asset_lane_v2(_context(issue), state, issue)
    assert isinstance(first, AssetLaneAcceptedV2)

    transfer = _transfer_command(amount_atoms=100)
    second = transition_asset_lane_v2(
        _context(transfer, nonce=2),
        first.post_state,
        transfer,
    )
    assert isinstance(second, AssetLaneAcceptedV2)

    burn = _managed_command(
        kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        owner="bob",
        amount_atoms=40,
    )
    third = transition_asset_lane_v2(
        _context(burn, nonce=3),
        second.post_state,
        burn,
    )
    assert isinstance(third, AssetLaneAcceptedV2)
    assert third.post_state.balance_atoms("alice", "USD") == 948
    assert third.post_state.balance_atoms("bob", "USD") == 60
    assert third.post_state.balance_atoms("treasury", "USD") == 2
    assert third.post_state.supply_atoms("USD") == 1_010
    assert sum(row.amount_atoms for row in third.post_state.balances) == 1_010


def test_managed_projection_preserves_a_transfer_only_asset() -> None:
    eur = _transfer_policy(asset="EUR", fee_atoms=0)
    usd = _transfer_policy()
    managed = _managed_policy()
    transfers = (eur, usd)
    state = AssetLaneStateV2(
        _root("module-release"),
        _registry(transfers, (managed,)),
        transfers,
        (managed,),
        (
            EconomicAmountV2("carol", "EUR", ACCOUNT_CUSTODY_DOMAIN_V2, 500),
            EconomicAmountV2("alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 1_000),
        ),
        (AssetSupplyV2("EUR", 500), AssetSupplyV2("USD", 1_000)),
    )
    assert tuple(row.asset for row in state.managed_leaf_state().supplies) == ("USD",)

    issue = _managed_command(amount_atoms=50)
    result = transition_asset_lane_v2(_context(issue), state, issue)

    assert isinstance(result, AssetLaneAcceptedV2)
    assert result.post_state.balance_atoms("carol", "EUR") == 500
    assert result.post_state.supply_atoms("EUR") == 500
    assert result.post_state.balance_atoms("alice", "USD") == 1_050
    assert result.post_state.supply_atoms("USD") == 1_050


def test_transfer_authorization_failure_is_an_aggregate_noop() -> None:
    state = _state()
    command = _transfer_command()
    result = transition_asset_lane_v2(
        _context(command, subject="mallory"),
        state,
        command,
    )
    rejected = _assert_noop(result, state, AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT)
    assert rejected.route is AssetLaneRouteV2.TRANSFER


@pytest.mark.parametrize(
    ("command", "subject", "grant", "code"),
    (
        (
            _managed_command(),
            "mallory",
            None,
            ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT,
        ),
        (
            _managed_command(),
            None,
            _root("wrong-grant"),
            ManagedAssetLifecycleRejectCodeV2.AUTHORIZATION_ROOT_MISMATCH,
        ),
        (
            _managed_command(kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2),
            "mallory",
            None,
            ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT,
        ),
    ),
)
def test_managed_authorization_failures_are_aggregate_noops(
    command: ManagedAssetLifecycleCommandV2,
    subject: str | None,
    grant: str | None,
    code: ManagedAssetLifecycleRejectCodeV2,
) -> None:
    state = _state()
    result = transition_asset_lane_v2(
        _context(command, subject=subject, grant_root=grant),
        state,
        command,
    )
    rejected = _assert_noop(result, state, code)
    assert rejected.route is AssetLaneRouteV2.MANAGED_LIFECYCLE


def test_registry_policy_drift_rejects_before_leaf_dispatch() -> None:
    state = _state(registry_drift=True)
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)

    rejected = _assert_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.REGISTRY_BINDING_MISMATCH,
    )
    assert rejected.route is AssetLaneRouteV2.COORDINATOR


def test_projection_mismatch_is_a_named_noop_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _state()
    command = _transfer_command()
    monkeypatch.setattr(
        coordinator_module,
        "_projection_holds_v2",
        lambda route, post_state, candidate: False,
    )

    result = transition_asset_lane_v2(_context(command), state, command)

    _assert_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    )


def test_input_graph_is_transitively_owned() -> None:
    transfer = _transfer_policy()
    managed = _managed_policy()
    balance = EconomicAmountV2("alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 1_000)
    registry = _registry((transfer,), (managed,))
    state = AssetLaneStateV2(
        _root("module-release"),
        registry,
        (transfer,),
        (managed,),
        (balance,),
        (AssetSupplyV2("USD", 1_000),),
    )
    state_root = state.state_root

    object.__setattr__(transfer, "transfer_fee_atoms", 99)
    object.__setattr__(managed, "enabled", False)
    object.__setattr__(balance, "amount_atoms", 1)
    object.__setattr__(registry, "module_release_id", _root("mutated-release"))

    assert state.state_root == state_root
    assert state.transfer_policies[0].transfer_fee_atoms == 2
    assert state.managed_policies[0].enabled is True
    assert state.balance_atoms("alice", "USD") == 1_000
    assert state.origin_registry.module_release_id == _root("module-release")


def test_result_getters_return_owned_snapshots() -> None:
    state = _state()
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)
    assert isinstance(result, AssetLaneAcceptedV2)
    post_root = result.post_state.state_root
    effect_root = result.effects.effect_plan_root
    journal_root = result.module_journal.journal_root

    exposed_state = result.post_state
    exposed_balance = exposed_state.balances[0]
    object.__setattr__(exposed_balance, "amount_atoms", 1)
    exposed_effect = result.effects.rows[0]
    object.__setattr__(exposed_effect, "delta_atoms", 1)
    exposed_journal = result.module_journal
    object.__setattr__(exposed_journal, "receipt_root", _root("mutated-receipt"))

    assert result.post_state.state_root == post_root
    assert result.effects.effect_plan_root == effect_root
    assert result.module_journal.journal_root == journal_root


def test_accepted_coordinator_receipt_cannot_be_caller_constructed() -> None:
    state = _state()
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)
    assert isinstance(result, AssetLaneAcceptedV2)

    with pytest.raises(TypeError, match="checker-constructed"):
        AssetLaneAcceptedV2(
            object(),
            result.route,
            result.source_leaf_journal_root,
            result.post_state,
            result.effects,
            result.module_journal,
        )


def test_supply_and_signed_effect_boundaries_reject_without_mutation() -> None:
    full = _state(supply_atoms=MAX_ATOMS_V2)
    issue = _managed_command(amount_atoms=1)
    _assert_noop(
        transition_asset_lane_v2(_context(issue), full, issue),
        full,
        ManagedAssetLifecycleRejectCodeV2.SUPPLY_OVERFLOW,
    )

    transfer = _transfer_command(amount_atoms=MAX_ATOMS_V2, max_fee_atoms=2)
    _assert_noop(
        transition_asset_lane_v2(_context(transfer), full, transfer),
        full,
        AssetTransferRejectCodeV2.EFFECT_DELTA_OVERFLOW,
    )


def test_state_rejects_unreconciled_owned_supply() -> None:
    with pytest.raises(ValueError, match="owned account total must equal supply"):
        _state(
            balances=(
                EconomicAmountV2(
                    "alice",
                    "USD",
                    ACCOUNT_CUSTODY_DOMAIN_V2,
                    999,
                ),
            ),
            supply_atoms=1_000,
        )


def test_closed_command_routing_rejects_subclasses() -> None:
    class EvilTransfer(AssetTransferCommandV2):
        pass

    command = _transfer_command()
    evil = object.__new__(EvilTransfer)
    for field in (
        "command_kind",
        "asset",
        "sender",
        "recipient",
        "amount_atoms",
        "max_fee_atoms",
        "asset_origin_root",
    ):
        object.__setattr__(evil, field, getattr(command, field))
    with pytest.raises(TypeError, match="exact closed V2 command"):
        transition_asset_lane_v2(_context(command), _state(), evil)


def test_profile_authentication_gap_is_explicit_on_state_and_result() -> None:
    state = _state()
    command = _transfer_command()
    result = transition_asset_lane_v2(_context(command), state, command)

    assert state.production_authority == "NONE"
    assert state.profile_authentication == "SHADOW"
    assert isinstance(result, AssetLaneAcceptedV2)
    assert result.production_authority == "NONE"
    assert result.profile_authentication == "SHADOW"
