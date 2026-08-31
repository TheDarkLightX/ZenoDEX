"""Regression obligations for the V2 managed asset lifecycle leaf."""

from dataclasses import replace

import pytest

from src.core.asset_transfer_types_v2 import AssetClassV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
)
from src.core.managed_asset_lifecycle_module_v2 import (
    transition_managed_asset_lifecycle_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
    MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleStateV2,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy(
    *,
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    origin: str | None = _root(40),
    issue_subject: str | None = "issuer",
    issue_root: str | None = _root(5),
    burn_root: str | None = _root(6),
    enabled: bool = True,
) -> ManagedAssetLifecyclePolicyV2:
    return ManagedAssetLifecyclePolicyV2(
        asset="USD",
        asset_class=asset_class,
        asset_origin_root=origin,
        atom_decimals=8,
        issue_authority_subject=issue_subject,
        issue_authorization_root=issue_root,
        burn_authorization_root=burn_root,
        enabled=enabled,
    )


def _state(
    *,
    policy: ManagedAssetLifecyclePolicyV2 | None = None,
    balances: tuple[EconomicAmountV2, ...] | None = None,
    supply_atoms: int = 10,
) -> ManagedAssetLifecycleStateV2:
    return ManagedAssetLifecycleStateV2(
        module_release_id=_root(3),
        policies=(_policy() if policy is None else policy,),
        balances=(EconomicAmountV2("alice", "USD", "accounts", 10),)
        if balances is None
        else balances,
        supplies=(AssetSupplyV2("USD", supply_atoms),),
    )


def _command(
    *,
    command_kind: str = MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    account_owner: str = "alice",
    amount_atoms: int = 7,
    asset: str = "USD",
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    origin: str | None = _root(40),
    atom_decimals: int = 8,
    authorization_root: str | None = _root(5),
) -> ManagedAssetLifecycleCommandV2:
    return ManagedAssetLifecycleCommandV2(
        command_kind=command_kind,
        asset=asset,
        asset_class=asset_class,
        asset_origin_root=origin,
        atom_decimals=atom_decimals,
        authorization_root=authorization_root,
        account_owner=account_owner,
        amount_atoms=amount_atoms,
    )


def _context(
    *,
    command: ManagedAssetLifecycleCommandV2 | None = None,
    subject: str = "issuer",
    grant: str = _root(5),
    global_pre_root: str = _root(90),
    occurrence: EconomicCommandOccurrenceV2 | None = None,
    module_release_id: str = _root(3),
    consumed_object_ids: tuple[str, ...] = (),
    nonce: int = 1,
) -> ManagedAssetLifecycleContextV2:
    selected = _command() if command is None else command
    selected_occurrence = occurrence or EconomicCommandOccurrenceV2(
        chain_id="zeno-v2-test",
        deployment_root=_root(1),
        height=8,
        tx_index=0,
        op_index=0,
        command_kind=selected.command_kind,
        command_body_hash=selected.command_body_hash,
        route_release_id=_root(70),
        subject_id=subject,
        grant_root=grant,
        nonce=nonce,
        profile_root=_root(2),
        pre_state_root=global_pre_root,
        consumed_object_ids=consumed_object_ids,
    )
    return ManagedAssetLifecycleContextV2(
        writer_epoch=7,
        module_release_id=module_release_id,
        global_pre_state_root=global_pre_root,
        occurrence=selected_occurrence,
    )


def _assert_noop(
    result: object,
    state: ManagedAssetLifecycleStateV2,
    code: ManagedAssetLifecycleRejectCodeV2,
) -> None:
    assert isinstance(result, ManagedAssetLifecycleRejectedV2)
    assert result.code is code
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.terminal_obligations_root == ZERO_ROOT_V2
    assert result.oracle_occurrence_plan_root == ZERO_ROOT_V2
    assert result.production_authority == MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2


def test_v2_managed_asset_lifecycle_leaf_is_available() -> None:
    assert callable(transition_managed_asset_lifecycle_v2)


def test_issue_binds_identity_authorization_effects_and_zero_external_roots() -> None:
    state = _state()
    command = _command()
    result = transition_managed_asset_lifecycle_v2(_context(command=command), state, command)

    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    assert result.post_state.balance_atoms("alice", "USD") == 17
    assert result.post_state.supply_atoms("USD") == 17
    assert result.production_authority == MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2
    assert result.module_journal.lane_id is LaneIdV2.ASSET_TRANSFER
    assert result.module_journal.private_port_root == ZERO_ROOT_V2
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V2
    assert result.module_journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
    assert result.effects.occurrence_consumptions == (result.module_journal.command_occurrence_id,)
    assert {(row.kind, row.delta_atoms) for row in result.effects.rows} == {
        (EconomicEffectKindV2.ACCOUNT_MOVEMENT, 7),
        (EconomicEffectKindV2.ISSUE, 7),
    }
    conservation = result.effects.asset_conservation[0]
    assert conservation.authorized_issue_atoms == 7
    assert conservation.authorized_burn_atoms == 0


def test_self_burn_decreases_account_supply_and_uses_burn_authorization() -> None:
    command = _command(
        command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        amount_atoms=4,
        authorization_root=_root(6),
    )
    result = transition_managed_asset_lifecycle_v2(
        _context(command=command, subject="alice", grant=_root(6)),
        _state(),
        command,
    )

    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    assert result.post_state.balance_atoms("alice", "USD") == 6
    assert result.post_state.supply_atoms("USD") == 6
    assert {(row.kind, row.delta_atoms) for row in result.effects.rows} == {
        (EconomicEffectKindV2.ACCOUNT_MOVEMENT, -4),
        (EconomicEffectKindV2.BURN, -4),
    }
    assert result.effects.asset_conservation[0].authorized_burn_atoms == 4


@pytest.mark.parametrize(
    ("context", "state", "command", "code"),
    (
        (
            replace(_context(), occurrence=None),  # type: ignore[call-arg]
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.MISSING_OCCURRENCE,
        ),
        (
            replace(_context(), global_pre_state_root=_root(91)),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            _context(module_release_id=_root(99)),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.RELEASE_MISMATCH,
        ),
        (
            _context(command=_command(command_kind="unknown")),
            _state(),
            _command(command_kind="unknown"),
            ManagedAssetLifecycleRejectCodeV2.UNKNOWN_COMMAND,
        ),
        (
            _context(command=_command(asset="EUR")),
            _state(),
            _command(asset="EUR"),
            ManagedAssetLifecycleRejectCodeV2.UNKNOWN_ASSET,
        ),
        (
            _context(),
            _state(policy=_policy(enabled=False)),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.DISABLED_ASSET,
        ),
        (
            _context(command=_command(asset_class=AssetClassV2.LP_SHARE)),
            _state(),
            _command(asset_class=AssetClassV2.LP_SHARE),
            ManagedAssetLifecycleRejectCodeV2.ASSET_CLASS_MISMATCH,
        ),
        (
            _context(command=_command(origin=None)),
            _state(policy=_policy(origin=None)),
            _command(origin=None),
            ManagedAssetLifecycleRejectCodeV2.UNREGISTERED_ASSET,
        ),
        (
            _context(command=_command(origin=_root(41))),
            _state(),
            _command(origin=_root(41)),
            ManagedAssetLifecycleRejectCodeV2.ASSET_ORIGIN_MISMATCH,
        ),
        (
            _context(),
            _state(policy=_policy(issue_subject=None, issue_root=None)),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.ISSUE_DISABLED,
        ),
        (
            _context(subject="mallory"),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT,
        ),
        (
            _context(grant=_root(99)),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV2.AUTHORIZATION_ROOT_MISMATCH,
        ),
        (
            _context(command=_command(amount_atoms=0)),
            _state(),
            _command(amount_atoms=0),
            ManagedAssetLifecycleRejectCodeV2.ZERO_AMOUNT,
        ),
    ),
)
def test_protocol_rejections_are_exact_noops(
    context: ManagedAssetLifecycleContextV2,
    state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
    code: ManagedAssetLifecycleRejectCodeV2,
) -> None:
    _assert_noop(transition_managed_asset_lifecycle_v2(context, state, command), state, code)


def test_occurrence_body_swap_and_consumed_input_reject_before_effects() -> None:
    command = _command()
    swapped = _context(command=_command(amount_atoms=8))
    consumed = _context(command=command, consumed_object_ids=("already-used",))

    _assert_noop(
        transition_managed_asset_lifecycle_v2(swapped, _state(), command),
        _state(),
        ManagedAssetLifecycleRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH,
    )
    _assert_noop(
        transition_managed_asset_lifecycle_v2(consumed, _state(), command),
        _state(),
        ManagedAssetLifecycleRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
    )


def test_protocol_managed_asset_cannot_use_generic_issue_authority() -> None:
    policy = ManagedAssetLifecyclePolicyV2(
        asset="TAU",
        asset_class=AssetClassV2.TAU_NATIVE_COIN,
        asset_origin_root=_root(40),
        atom_decimals=8,
        issue_authority_subject=None,
        issue_authorization_root=None,
        burn_authorization_root=None,
        enabled=True,
    )
    state = ManagedAssetLifecycleStateV2(
        module_release_id=_root(3),
        policies=(policy,),
        balances=(),
        supplies=(AssetSupplyV2("TAU", 0),),
    )
    command = _command(
        asset="TAU",
        asset_class=AssetClassV2.TAU_NATIVE_COIN,
        authorization_root=None,
    )
    _assert_noop(
        transition_managed_asset_lifecycle_v2(_context(command=command), state, command),
        state,
        ManagedAssetLifecycleRejectCodeV2.GENERIC_AUTHORITY_FORBIDDEN,
    )


def test_width_supply_and_balance_boundaries_reject_without_mutation() -> None:
    width_command = _command(amount_atoms=1 << 127)
    _assert_noop(
        transition_managed_asset_lifecycle_v2(
            _context(command=width_command),
            _state(balances=(), supply_atoms=0),
            width_command,
        ),
        _state(balances=(), supply_atoms=0),
        ManagedAssetLifecycleRejectCodeV2.EFFECT_DELTA_OVERFLOW,
    )
    overflow_command = _command(amount_atoms=1)
    full = _state(
        balances=(EconomicAmountV2("alice", "USD", "accounts", MAX_ATOMS_V2),),
        supply_atoms=MAX_ATOMS_V2,
    )
    _assert_noop(
        transition_managed_asset_lifecycle_v2(
            _context(command=overflow_command), full, overflow_command
        ),
        full,
        ManagedAssetLifecycleRejectCodeV2.SUPPLY_OVERFLOW,
    )


def test_snapshots_reject_subclasses_and_do_not_retain_policy_aliases() -> None:
    policy = _policy()
    state = _state(policy=policy)
    root = state.state_root
    object.__setattr__(policy, "enabled", False)
    object.__setattr__(policy, "asset_origin_root", _root(99))
    assert state.state_root == root
    assert state.policies[0].enabled is True
    assert state.policies[0].asset_origin_root == _root(40)

    class EvilCommand(ManagedAssetLifecycleCommandV2):
        pass

    evil = object.__new__(EvilCommand)
    for field, value in zip(
        (
            "command_kind",
            "asset",
            "asset_class",
            "asset_origin_root",
            "atom_decimals",
            "authorization_root",
            "account_owner",
            "amount_atoms",
        ),
        (
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
            "USD",
            AssetClassV2.REGISTERED_ORDINARY_TOKEN,
            _root(40),
            8,
            _root(5),
            "alice",
            1,
        ),
        strict=True,
    ):
        object.__setattr__(evil, field, value)
    with pytest.raises(TypeError, match="exact typed value"):
        transition_managed_asset_lifecycle_v2(_context(), state, evil)


def test_state_context_and_accepted_getters_return_owned_snapshots() -> None:
    state = _state()
    command = _command()
    context = _context(command=command)
    result = transition_managed_asset_lifecycle_v2(context, state, command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    occurrence = context.occurrence
    assert occurrence is not None

    state_root = state.state_root
    occurrence_id = occurrence.occurrence_id
    post_state_root = result.post_state.state_root
    effect_plan_root = result.effects.effect_plan_root
    journal_root = result.module_journal.journal_root
    receipt_root = result.receipt_root

    borrowed_policy = state.policies[0]
    borrowed_balance = state.balances[0]
    borrowed_supply = state.supplies[0]
    borrowed_occurrence = context.occurrence
    borrowed_post_state = result.post_state
    borrowed_effect = result.effects.rows[0]
    borrowed_journal = result.module_journal
    assert borrowed_occurrence is not None

    object.__setattr__(borrowed_policy, "enabled", False)
    object.__setattr__(borrowed_balance, "amount_atoms", 999)
    object.__setattr__(borrowed_supply, "amount_atoms", 999)
    object.__setattr__(borrowed_occurrence, "nonce", 999)
    object.__setattr__(borrowed_post_state, "module_release_id", _root(999))
    object.__setattr__(borrowed_effect, "delta_atoms", -999)
    object.__setattr__(borrowed_journal, "receipt_root", _root(999))

    assert state.state_root == state_root
    assert state.policies[0].enabled is True
    assert state.balances[0].amount_atoms == 10
    assert state.supplies[0].amount_atoms == 10
    retained_occurrence = context.occurrence
    assert retained_occurrence is not None
    assert retained_occurrence.occurrence_id == occurrence_id
    assert result.post_state.state_root == post_state_root
    assert result.effects.effect_plan_root == effect_plan_root
    assert result.module_journal.journal_root == journal_root
    assert result.receipt_root == receipt_root
    assert replace(state) == state
    assert replace(context) == context
    assert replace(result) == result


def test_rejected_result_owns_effect_plan_and_does_not_expose_it() -> None:
    state = _state()
    command = _command()
    accepted = transition_managed_asset_lifecycle_v2(
        _context(command=command),
        state,
        command,
    )
    assert isinstance(accepted, ManagedAssetLifecycleAcceptedV2)
    nonempty_effects = accepted.effects
    empty_effects = GlobalEconomicEffectPlanV2.empty()
    rejected = ManagedAssetLifecycleRejectedV2(
        ManagedAssetLifecycleRejectCodeV2.UNKNOWN_COMMAND,
        state.state_root,
        state.state_root,
        empty_effects,
    )

    object.__setattr__(empty_effects, "rows", nonempty_effects.rows)
    borrowed_effects = rejected.effects
    object.__setattr__(borrowed_effects, "rows", nonempty_effects.rows)

    assert rejected.effects.is_empty
    assert replace(rejected) == rejected


def test_unknown_constructor_field_is_rejected_and_v2_schema_is_distinct() -> None:
    with pytest.raises(TypeError, match="unexpected keyword"):
        ManagedAssetLifecycleCommandV2(  # type: ignore[call-arg]
            command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
            asset="USD",
            asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
            asset_origin_root=_root(40),
            atom_decimals=8,
            authorization_root=_root(5),
            account_owner="alice",
            amount_atoms=1,
            unknown_field="mallory",
        )
    assert _state().to_canonical()["schema"] == MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2


def test_stateful_issue_then_burn_restores_account_and_supply() -> None:
    initial = _state()
    issue = _command(amount_atoms=3)
    issued = transition_managed_asset_lifecycle_v2(_context(command=issue, nonce=1), initial, issue)
    assert isinstance(issued, ManagedAssetLifecycleAcceptedV2)
    burn = _command(
        command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        amount_atoms=3,
        authorization_root=_root(6),
    )
    burned = transition_managed_asset_lifecycle_v2(
        _context(command=burn, subject="alice", grant=_root(6), nonce=2),
        issued.post_state,
        burn,
    )
    assert isinstance(burned, ManagedAssetLifecycleAcceptedV2)
    assert burned.post_state.balance_atoms("alice", "USD") == initial.balance_atoms("alice", "USD")
    assert burned.post_state.supply_atoms("USD") == initial.supply_atoms("USD")
