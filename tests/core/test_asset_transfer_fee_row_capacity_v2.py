"""Distinct-fee transfer row-capacity boundary obligations for V2.

A funded sender that remains funded, an absent recipient, and an absent,
distinct positive-fee collector materialize two new physical balance rows.  The
leaf must evaluate that final table rather than an intermediate update or a
one-credit row estimate.
"""

from __future__ import annotations

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    MAX_ASSET_TRANSFER_BALANCE_ROWS_V2,
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from tests.core import test_asset_transfer_module_v2 as _fixture

_ASSET = "EUR"
_SENDER = "sender"
_RECIPIENT = "recipient"
_FEE_COLLECTOR = "collector"
_AMOUNT_ATOMS = 3
_FEE_ATOMS = 2
_SENDER_PRE_ATOMS = 9
_ROW_CAPACITY = MAX_ASSET_TRANSFER_BALANCE_ROWS_V2


def _filler_owner(index: int) -> str:
    return f"holder{index:04d}"


def _policy() -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset=_ASSET,
        fee_owner=_FEE_COLLECTOR,
        transfer_fee_atoms=_FEE_ATOMS,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_fixture._root("origin:EUR"),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )


def _state_with_row_count(row_count: int) -> AssetTransferStateV2:
    if row_count < 1:
        raise ValueError("the funded sender must occupy one physical row")
    balances = (
        EconomicAmountV2(
            _SENDER,
            _ASSET,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            _SENDER_PRE_ATOMS,
        ),
        *(
            EconomicAmountV2(
                _filler_owner(index),
                _ASSET,
                ACCOUNT_CUSTODY_DOMAIN_V2,
                1,
            )
            for index in range(row_count - 1)
        ),
    )
    canonical_balances = tuple(sorted(balances, key=lambda row: row.key))
    supply_atoms = _SENDER_PRE_ATOMS + row_count - 1
    return AssetTransferStateV2(
        module_release_id=_fixture._root("asset-release"),
        policies=(_policy(),),
        balances=canonical_balances,
        supplies=(AssetSupplyV2(_ASSET, supply_atoms),),
    )


def _command() -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset=_ASSET,
        sender=_SENDER,
        recipient=_RECIPIENT,
        amount_atoms=_AMOUNT_ATOMS,
        max_fee_atoms=_FEE_ATOMS,
        asset_origin_root=_fixture._root("origin:EUR"),
    )


def _expected_post_rows(state: AssetTransferStateV2) -> tuple[EconomicAmountV2, ...]:
    """Build this three-role outcome without calling the transition helpers."""

    sender_post_atoms = _SENDER_PRE_ATOMS - _AMOUNT_ATOMS - _FEE_ATOMS
    assert sender_post_atoms > 0
    unchanged_rows = tuple(row for row in state.balances if row.owner != _SENDER)
    rows = (
        *unchanged_rows,
        EconomicAmountV2(
            _SENDER,
            _ASSET,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            sender_post_atoms,
        ),
        EconomicAmountV2(
            _RECIPIENT,
            _ASSET,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            _AMOUNT_ATOMS,
        ),
        EconomicAmountV2(
            _FEE_COLLECTOR,
            _ASSET,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            _FEE_ATOMS,
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.key))


def _assert_typed_resource_noop(
    result: object,
    state: AssetTransferStateV2,
) -> None:
    assert isinstance(result, AssetTransferRejectedV2)
    assert result.code is AssetTransferRejectCodeV2.STATE_RESOURCE_LIMIT
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert result.effects.lane_writes == ()
    assert result.effects.occurrence_consumptions == ()
    assert result.effects.external_outbox_enqueue == ()


def test_distinct_positive_fee_adds_two_physical_rows_from_4094_to_4096() -> None:
    """A final 4096-row three-role result is admitted with canonical contents."""

    state = _state_with_row_count(_ROW_CAPACITY - 2)
    command = _command()
    context = _fixture._context(state, command)
    expected_rows = _expected_post_rows(state)

    assert len(state.balances) == _ROW_CAPACITY - 2
    assert len({_SENDER, _RECIPIENT, _FEE_COLLECTOR}) == 3
    assert state.policies[0].fee_owner == _FEE_COLLECTOR
    assert state.policies[0].transfer_fee_atoms == _FEE_ATOMS
    assert _FEE_ATOMS > 0
    assert state.balance_atoms(_SENDER, _ASSET) == _SENDER_PRE_ATOMS
    assert state.balance_atoms(_RECIPIENT, _ASSET) == 0
    assert state.balance_atoms(_FEE_COLLECTOR, _ASSET) == 0
    assert len(expected_rows) == _ROW_CAPACITY
    assert sum(row.amount_atoms for row in expected_rows) == state.supply_atoms(_ASSET)

    result = transition_asset_transfer_v2(context, state, command)

    assert isinstance(result, AssetTransferAcceptedV2)
    assert result.post_state.policies == state.policies
    assert result.post_state.balances == expected_rows
    assert result.post_state.supplies == state.supplies
    assert result.post_state.balance_atoms(_SENDER, _ASSET) == 4
    assert result.post_state.balance_atoms(_RECIPIENT, _ASSET) == _AMOUNT_ATOMS
    assert result.post_state.balance_atoms(_FEE_COLLECTOR, _ASSET) == _FEE_ATOMS
    assert context.occurrence is not None
    assert result.effects.occurrence_consumptions == (context.occurrence.occurrence_id,)


def test_distinct_positive_fee_4095_to_candidate_4097_is_typed_noop() -> None:
    """The second absent credit defeats a one-credit row-capacity counter."""

    state = _state_with_row_count(_ROW_CAPACITY - 1)
    command = _command()
    context = _fixture._context(state, command)
    pre_rows = state.balances
    pre_supplies = state.supplies
    pre_bytes = canonical_global_bytes_v2(state)

    assert len(pre_rows) == _ROW_CAPACITY - 1
    assert len(_expected_post_rows(state)) == _ROW_CAPACITY + 1

    result = transition_asset_transfer_v2(context, state, command)

    _assert_typed_resource_noop(result, state)
    assert state.balances == pre_rows
    assert state.supplies == pre_supplies
    assert canonical_global_bytes_v2(state) == pre_bytes
