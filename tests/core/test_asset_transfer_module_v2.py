from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace

import pytest

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2,
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_DELTA_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)


def _root(label: str) -> str:
    return hash_global_v2("test-root-v2", {"label": label})


def _policy(
    *,
    asset: str = "USD",
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    asset_origin_root: str | None = None,
    transfer_fee_atoms: int = 2,
    enabled: bool = True,
) -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset=asset,
        fee_owner="treasury",
        transfer_fee_atoms=transfer_fee_atoms,
        enabled=enabled,
        asset_class=asset_class,
        asset_origin_root=asset_origin_root or _root(f"origin:{asset}"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )


def _state(
    *,
    policy: AssetTransferPolicyV2 | None = None,
    alice_atoms: int = 1_000,
) -> AssetTransferStateV2:
    selected = policy or _policy()
    return AssetTransferStateV2(
        module_release_id=_root("asset-release"),
        policies=(selected,),
        balances=(
            EconomicAmountV2(
                owner="alice",
                asset=selected.asset,
                custody_domain=ACCOUNT_CUSTODY_DOMAIN_V2,
                amount_atoms=alice_atoms,
            ),
        ),
        supplies=(AssetSupplyV2(selected.asset, alice_atoms),),
    )


def _command(
    *,
    asset: str = "USD",
    sender: str = "alice",
    recipient: str = "bob",
    asset_origin_root: str | None = None,
    amount_atoms: int = 100,
    max_fee_atoms: int = 2,
) -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset=asset,
        sender=sender,
        recipient=recipient,
        amount_atoms=amount_atoms,
        max_fee_atoms=max_fee_atoms,
        asset_origin_root=asset_origin_root or _root(f"origin:{asset}"),
    )


def _context(
    state: AssetTransferStateV2,
    command: AssetTransferCommandV2,
) -> AssetTransferContextV2:
    global_pre_state_root = _root("global-pre-state")
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="zeno-test",
        deployment_root=_root("deployment"),
        height=7,
        tx_index=3,
        op_index=1,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root("route-release"),
        subject_id=command.sender,
        grant_root=_root("grant"),
        nonce=11,
        profile_root=_root("profile"),
        pre_state_root=global_pre_state_root,
        consumed_object_ids=(),
    )
    return AssetTransferContextV2(
        writer_epoch=5,
        module_release_id=state.module_release_id,
        global_pre_state_root=global_pre_state_root,
        occurrence=occurrence,
    )


def _assert_reject_noop(
    result: AssetTransferRejectedV2,
    expected: AssetTransferRejectCodeV2,
    state: AssetTransferStateV2,
) -> None:
    assert result.code is expected
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty


def test_transfer_accepts_one_origin_and_occurrence_bound_command() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)

    result = transition_asset_transfer_v2(context, state, command)

    assert isinstance(result, AssetTransferAcceptedV2)
    assert state.balance_atoms("alice", "USD") == 1_000
    assert result.post_state.balance_atoms("alice", "USD") == 898
    assert result.post_state.balance_atoms("bob", "USD") == 100
    assert result.post_state.balance_atoms("treasury", "USD") == 2
    assert result.effects.occurrence_consumptions == (context.occurrence.occurrence_id,)
    assert result.effects.lane_writes == (
        LaneWriteV2(
            LaneIdV2.ASSET_TRANSFER,
            state.state_root,
            result.post_state.state_root,
        ),
    )
    assert result.effects.asset_conservation[0].owned_and_custodied_pre_atoms == 1_000
    assert result.effects.asset_conservation[0].owned_and_custodied_post_atoms == 1_000
    assert result.effects.asset_conservation[0].supply_pre_atoms == 1_000
    assert result.effects.asset_conservation[0].supply_post_atoms == 1_000
    assert result.effects.fee_conservation[0].fee_charged_atoms == 2
    assert result.effects.fee_conservation[0].current_allocations_atoms == 2
    assert result.module_journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V2
    assert result.production_authority == "NONE"


@pytest.mark.parametrize(
    "journal_field",
    (
        "private_port_root",
        "terminal_obligations_root",
        "oracle_occurrence_plan_root",
    ),
)
def test_transfer_acceptance_rejects_nonzero_external_roots(
    journal_field: str,
) -> None:
    state = _state()
    command = _command()
    result = transition_asset_transfer_v2(_context(state, command), state, command)
    assert isinstance(result, AssetTransferAcceptedV2)

    with pytest.raises(ValueError, match="zero external roots"):
        AssetTransferAcceptedV2(
            result.post_state,
            result.effects,
            replace(result.module_journal, **{journal_field: _root(journal_field)}),
        )


def test_missing_occurrence_rejects_without_effects() -> None:
    state = _state()
    command = _command()
    context = replace(_context(state, command), occurrence=None)

    result = transition_asset_transfer_v2(context, state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, AssetTransferRejectCodeV2.MISSING_OCCURRENCE, state)


@pytest.mark.parametrize(
    ("mutate", "expected"),
    (
        (
            lambda context: replace(context, global_pre_state_root=_root("other-pre")),
            AssetTransferRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            lambda context: replace(
                context,
                occurrence=replace(
                    context.occurrence,
                    consumed_object_ids=("already-consumed",),
                ),
            ),
            AssetTransferRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            lambda context: replace(
                context,
                occurrence=replace(
                    context.occurrence,
                    command_body_hash=_root("wrong-command"),
                ),
            ),
            AssetTransferRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH,
        ),
    ),
)
def test_occurrence_relabeling_rejects_without_effects(
    mutate: Callable[[AssetTransferContextV2], AssetTransferContextV2],
    expected: AssetTransferRejectCodeV2,
) -> None:
    state = _state()
    command = _command()
    context = _context(state, command)

    result = transition_asset_transfer_v2(mutate(context), state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, expected, state)


@pytest.mark.parametrize(
    ("policy_origin", "command_origin", "expected"),
    (
        (None, _root("origin:USD"), AssetTransferRejectCodeV2.UNREGISTERED_ASSET),
        (_root("origin:USD"), None, AssetTransferRejectCodeV2.UNREGISTERED_ASSET),
        (
            _root("origin:USD"),
            _root("wrong-origin"),
            AssetTransferRejectCodeV2.ASSET_ORIGIN_MISMATCH,
        ),
    ),
)
def test_origin_absence_or_mismatch_rejects_without_effects(
    policy_origin: str | None,
    command_origin: str | None,
    expected: AssetTransferRejectCodeV2,
) -> None:
    policy = replace(_policy(), asset_origin_root=policy_origin)
    state = _state(policy=policy)
    command = replace(_command(), asset_origin_root=command_origin)
    context = _context(state, command)

    result = transition_asset_transfer_v2(context, state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, expected, state)


def test_protected_asset_identifier_cannot_be_relabelled() -> None:
    with pytest.raises(ValueError, match="wrong asset class"):
        _policy(asset="ZDEX")


def test_native_asset_accounting_remains_fail_closed() -> None:
    policy = _policy(asset="TAU", asset_class=AssetClassV2.TAU_NATIVE_COIN)
    state = _state(policy=policy)
    command = _command(asset="TAU")

    result = transition_asset_transfer_v2(_context(state, command), state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(
        result,
        AssetTransferRejectCodeV2.NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
        state,
    )


def test_unknown_disabled_and_subject_guards_preserve_rejection_precedence() -> None:
    state = _state()

    unknown_kind = replace(_command(), command_kind="unknown_transfer")
    unknown_result = transition_asset_transfer_v2(
        _context(state, unknown_kind),
        state,
        unknown_kind,
    )
    assert isinstance(unknown_result, AssetTransferRejectedV2)
    _assert_reject_noop(
        unknown_result,
        AssetTransferRejectCodeV2.UNKNOWN_COMMAND,
        state,
    )

    unknown_asset = _command(asset="OTHER")
    unknown_asset_result = transition_asset_transfer_v2(
        _context(state, unknown_asset),
        state,
        unknown_asset,
    )
    assert isinstance(unknown_asset_result, AssetTransferRejectedV2)
    _assert_reject_noop(
        unknown_asset_result,
        AssetTransferRejectCodeV2.UNKNOWN_ASSET,
        state,
    )

    disabled_state = _state(policy=replace(_policy(), enabled=False))
    disabled_command = _command()
    disabled_result = transition_asset_transfer_v2(
        _context(disabled_state, disabled_command),
        disabled_state,
        disabled_command,
    )
    assert isinstance(disabled_result, AssetTransferRejectedV2)
    _assert_reject_noop(
        disabled_result,
        AssetTransferRejectCodeV2.DISABLED_ASSET,
        disabled_state,
    )

    command = _command()
    context = _context(state, command)
    unauthorized_context = replace(
        context,
        occurrence=replace(context.occurrence, subject_id="mallory"),
    )
    unauthorized_result = transition_asset_transfer_v2(
        unauthorized_context,
        state,
        command,
    )
    assert isinstance(unauthorized_result, AssetTransferRejectedV2)
    _assert_reject_noop(
        unauthorized_result,
        AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT,
        state,
    )


@pytest.mark.parametrize(
    ("command", "expected"),
    (
        (_command(recipient="alice"), AssetTransferRejectCodeV2.SELF_TRANSFER),
        (_command(amount_atoms=0), AssetTransferRejectCodeV2.ZERO_AMOUNT),
        (_command(max_fee_atoms=1), AssetTransferRejectCodeV2.FEE_LIMIT_EXCEEDED),
    ),
)
def test_transfer_guards_reject_without_effects(
    command: AssetTransferCommandV2,
    expected: AssetTransferRejectCodeV2,
) -> None:
    state = _state()

    result = transition_asset_transfer_v2(_context(state, command), state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, expected, state)


def test_signed_effect_maximum_neighbor_is_accepted() -> None:
    state = _state(
        policy=_policy(transfer_fee_atoms=0),
        alice_atoms=MAX_DELTA_ATOMS_V2,
    )
    command = _command(amount_atoms=MAX_DELTA_ATOMS_V2, max_fee_atoms=0)

    result = transition_asset_transfer_v2(_context(state, command), state, command)

    assert isinstance(result, AssetTransferAcceptedV2)
    assert result.post_state.balance_atoms("alice", "USD") == 0
    assert result.post_state.balance_atoms("bob", "USD") == MAX_DELTA_ATOMS_V2


def test_signed_effect_bound_rejects_before_balance_application() -> None:
    amount_atoms = MAX_DELTA_ATOMS_V2 + 1
    state = _state(
        policy=_policy(transfer_fee_atoms=0),
        alice_atoms=amount_atoms,
    )
    command = _command(amount_atoms=amount_atoms, max_fee_atoms=0)

    result = transition_asset_transfer_v2(_context(state, command), state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, AssetTransferRejectCodeV2.EFFECT_DELTA_OVERFLOW, state)


def test_insufficient_balance_rejects_without_partial_application() -> None:
    state = _state()
    command = _command(amount_atoms=1_001)

    result = transition_asset_transfer_v2(_context(state, command), state, command)

    assert isinstance(result, AssetTransferRejectedV2)
    _assert_reject_noop(result, AssetTransferRejectCodeV2.INSUFFICIENT_BALANCE, state)


def test_boolean_amount_alias_and_unknown_field_are_rejected() -> None:
    with pytest.raises(ValueError, match="non-negative integer"):
        AssetTransferCommandV2(
            command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
            asset="USD",
            sender="alice",
            recipient="bob",
            amount_atoms=True,  # type: ignore[arg-type]
            max_fee_atoms=0,
            asset_origin_root=_root("origin:USD"),
        )
    with pytest.raises(TypeError):
        AssetTransferCommandV2(  # type: ignore[call-arg]
            command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
            asset="USD",
            sender="alice",
            recipient="bob",
            amount_atoms=1,
            max_fee_atoms=0,
            asset_origin_root=_root("origin:USD"),
            unknown=True,
        )


def test_transition_rejects_subclass_dispatch_before_behavior() -> None:
    class HostileCommand(AssetTransferCommandV2):
        pass

    state = _state()
    command = _command()
    hostile = HostileCommand(
        command.command_kind,
        command.asset,
        command.sender,
        command.recipient,
        command.amount_atoms,
        command.max_fee_atoms,
        command.asset_origin_root,
    )

    with pytest.raises(TypeError, match="exact typed value"):
        transition_asset_transfer_v2(_context(state, command), state, hostile)


def test_state_and_context_own_nested_snapshots() -> None:
    policy = _policy()
    state = _state(policy=policy)
    command = _command()
    occurrence = _context(state, command).occurrence
    assert occurrence is not None
    context = AssetTransferContextV2(
        writer_epoch=5,
        module_release_id=state.module_release_id,
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )
    state_root = state.state_root
    occurrence_id = context.occurrence.occurrence_id

    object.__setattr__(policy, "asset_origin_root", _root("mutated-origin"))
    object.__setattr__(occurrence, "command_body_hash", _root("mutated-command"))

    assert state.state_root == state_root
    assert state.policies[0].asset_origin_root == _root("origin:USD")
    assert context.occurrence.occurrence_id == occurrence_id
    assert context.occurrence.command_body_hash == command.command_body_hash


def test_state_context_and_result_getters_do_not_expose_nested_aliases() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)
    result = transition_asset_transfer_v2(context, state, command)
    assert isinstance(result, AssetTransferAcceptedV2)
    state_root = state.state_root
    occurrence_id = context.occurrence.occurrence_id
    result_bytes = canonical_global_bytes_v2(result)

    borrowed_policy = state.policies[0]
    borrowed_occurrence = context.occurrence
    borrowed_post_state = result.post_state
    borrowed_effect = result.effects.rows[0]
    object.__setattr__(borrowed_policy, "enabled", False)
    object.__setattr__(borrowed_occurrence, "nonce", 999)
    object.__setattr__(borrowed_post_state, "module_release_id", _root("mutated-release"))
    object.__setattr__(borrowed_effect, "delta_atoms", -999)

    assert state.state_root == state_root
    assert state.policies[0].enabled
    assert context.occurrence.occurrence_id == occurrence_id
    assert canonical_global_bytes_v2(result) == result_bytes


def test_rejected_result_owns_effect_plan_and_does_not_expose_it() -> None:
    effects = transition_asset_transfer_v2(
        _context(_state(), _command()),
        _state(),
        _command(),
    ).effects
    empty = type(effects).empty()
    state_root = _state().state_root
    rejected = AssetTransferRejectedV2(
        AssetTransferRejectCodeV2.UNKNOWN_COMMAND,
        state_root,
        state_root,
        empty,
    )
    rejected_bytes = canonical_global_bytes_v2(rejected)

    object.__setattr__(empty, "rows", effects.rows)
    borrowed = rejected.effects
    object.__setattr__(borrowed, "rows", effects.rows)

    assert rejected.effects.is_empty
    assert canonical_global_bytes_v2(rejected) == rejected_bytes


def test_same_inputs_produce_byte_identical_result() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)

    first = transition_asset_transfer_v2(context, state, command)
    second = transition_asset_transfer_v2(context, state, command)

    assert first == second
    assert canonical_global_bytes_v2(first) == canonical_global_bytes_v2(second)


def test_two_step_sequence_conserves_supply_and_consumes_distinct_occurrences() -> None:
    initial = _state()
    first_command = _command(amount_atoms=100)
    first_context = _context(initial, first_command)
    first = transition_asset_transfer_v2(first_context, initial, first_command)
    assert isinstance(first, AssetTransferAcceptedV2)

    second_command = _command(recipient="carol", amount_atoms=50)
    second_context = _context(first.post_state, second_command)
    second_context = replace(
        second_context,
        occurrence=replace(second_context.occurrence, nonce=12),
    )
    second = transition_asset_transfer_v2(
        second_context,
        first.post_state,
        second_command,
    )

    assert isinstance(second, AssetTransferAcceptedV2)
    assert second.post_state.balance_atoms("alice", "USD") == 846
    assert second.post_state.balance_atoms("bob", "USD") == 100
    assert second.post_state.balance_atoms("carol", "USD") == 50
    assert second.post_state.balance_atoms("treasury", "USD") == 4
    assert sum(row.amount_atoms for row in second.post_state.balances) == 1_000
    assert first.effects.occurrence_consumptions != second.effects.occurrence_consumptions


def test_v2_values_use_distinct_schemas_and_hash_domains() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)
    result = transition_asset_transfer_v2(context, state, command)

    assert isinstance(result, AssetTransferAcceptedV2)
    assert state.to_canonical()["schema"] == ASSET_TRANSFER_MODULE_SCHEMA_V2
    assert result.module_journal.to_canonical()["schema"] == GLOBAL_SETTLEMENT_ABI_V2
    assert b"zenodex/global-settlement-abi/v1" not in canonical_global_bytes_v2(result)
