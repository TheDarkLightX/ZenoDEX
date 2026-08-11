from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

import pytest

from src.core.asset_transfer_module_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
    transition_asset_transfer_v1,
)
from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)

CANONICAL_VECTOR_SHA256_V1 = {
    "context": "4629858b2b5d24a68a564c2f413fbe9dd1b0499b50cf7c5e71a871ebb7f6786a",
    "command": "1404382098da29fbcf5facf9fe4ecf5d0cd67a04eaec0c0cb89f6d78f17d1bc6",
    "pre_state": "ffd49e8969de8b04cd1059ecd22ff422f4c1442c41ddf673342811ef32dbb274",
    "post_state": "8620254b8374262d59dfb7b24cdfdecb385e0409f65343990951bed2cdc25a63",
    "effects": "34243fd329cf76b63cbaa433505f4cb5ed11c40ba80146426041b21e20bd0db5",
    "module_journal": "4cec50ca78d33c8e3d4c09359523ffcd6c2eb700c2dd0c441d8a31e609139c78",
}
CANONICAL_VECTOR_ROOTS_V1 = {
    "pre_state": "0x2e153465fca81b1035f8823db8368022c5ee4393b8bcdff136a2e4ec5de74ca8",
    "post_state": "0xbdb2605d119cc52da0f883c15e5979a9c8be98d728fc2f53e1c2af44d25de758",
    "effects": "0xb1b9e0b5c0078d0f90dbacce439026ac062c8d393f80533a1f9c1215c1f9e9fc",
    "receipt": "0x80ed14647f235e94982788fd932e7b63a933b9cb2f41505dbed0815c8c6a7cfb",
    "module_journal": "0x9c1fdc428aa5b38e698620f4bf93306fef83e3b469acaff9046ad7d8976977f3",
}


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _context(
    *,
    module_release_id: str | None = None,
    subject_id: str = "alice",
    command_occurrence_id: str | None = None,
) -> AssetTransferContextV1:
    return AssetTransferContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=module_release_id or _root(3),
        command_occurrence_id=command_occurrence_id or _root(4),
        subject_id=subject_id,
        grant_root=_root(5),
    )


def _state(
    *,
    enabled: bool = True,
    fee_atoms: int = 2,
    fee_owner: str = "treasury",
    balances: tuple[EconomicAmountV1, ...] | None = None,
    supply_atoms: int = 115,
) -> AssetTransferStateV1:
    rows = balances or (
        EconomicAmountV1("alice", "USD", "accounts", 100),
        EconomicAmountV1("bob", "USD", "accounts", 10),
        EconomicAmountV1("treasury", "USD", "accounts", 5),
    )
    return AssetTransferStateV1(
        module_release_id=_root(3),
        policies=(AssetTransferPolicyV1("USD", fee_owner, fee_atoms, enabled),),
        balances=rows,
        supplies=(AssetSupplyV1("USD", supply_atoms),),
    )


def _command(
    *,
    command_kind: str = ASSET_TRANSFER_COMMAND_KIND_V1,
    asset: str = "USD",
    sender: str = "alice",
    recipient: str = "bob",
    amount_atoms: int = 30,
    max_fee_atoms: int = 2,
) -> AssetTransferCommandV1:
    return AssetTransferCommandV1(
        command_kind=command_kind,
        asset=asset,
        sender=sender,
        recipient=recipient,
        amount_atoms=amount_atoms,
        max_fee_atoms=max_fee_atoms,
    )


def test_transfer_accepts_with_canonical_fee_and_conservation_effects() -> None:
    pre_state = _state()
    context = _context()
    command = _command()
    result = transition_asset_transfer_v1(context, pre_state, command)

    assert isinstance(result, AssetTransferAcceptedV1)
    assert result.post_state.balance_atoms("alice", "USD") == 68
    assert result.post_state.balance_atoms("bob", "USD") == 40
    assert result.post_state.balance_atoms("treasury", "USD") == 7
    assert result.post_state.supply_atoms("USD") == 115
    assert result.effects.occurrence_consumptions == (_root(4),)
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.asset_conservation[0].owned_and_custodied_pre_atoms == 115
    assert result.effects.asset_conservation[0].owned_and_custodied_post_atoms == 115
    assert result.effects.fee_conservation[0].fee_charged_atoms == 2
    assert result.effects.fee_conservation[0].current_allocations_atoms == 2
    assert result.effects.fee_conservation[0].carried_residue_atoms == 0
    assert [(row.kind, row.principal, row.delta_atoms) for row in result.effects.rows] == [
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", -32),
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "bob", 30),
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "treasury", 2),
        (EconomicEffectKindV1.FEE_ALLOCATION, "treasury", 2),
    ]
    assert result.effects.lane_writes[0].pre_root == pre_state.state_root
    assert result.effects.lane_writes[0].post_root == result.post_state.state_root
    assert result.module_journal.lane_id is LaneIdV1.ASSET_TRANSFER
    assert result.module_journal.private_port_root == ZERO_ROOT_V1
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V1
    vector_values = {
        "context": context,
        "command": command,
        "pre_state": pre_state,
        "post_state": result.post_state,
        "effects": result.effects,
        "module_journal": result.module_journal,
    }
    assert {
        name: sha256(canonical_global_bytes_v1(value)).hexdigest()
        for name, value in vector_values.items()
    } == CANONICAL_VECTOR_SHA256_V1
    assert {
        "pre_state": pre_state.state_root,
        "post_state": result.post_state.state_root,
        "effects": result.effects.effect_plan_root,
        "receipt": result.receipt_root,
        "module_journal": result.module_journal.journal_root,
    } == CANONICAL_VECTOR_ROOTS_V1


@pytest.mark.parametrize(
    ("context", "state", "command", "code"),
    (
        (_context(module_release_id=_root(99)), _state(), _command(), AssetTransferRejectCodeV1.RELEASE_MISMATCH),
        (_context(), _state(), _command(command_kind="unknown"), AssetTransferRejectCodeV1.UNKNOWN_COMMAND),
        (_context(), _state(), _command(asset="EUR"), AssetTransferRejectCodeV1.UNKNOWN_ASSET),
        (_context(), _state(enabled=False), _command(), AssetTransferRejectCodeV1.DISABLED_ASSET),
        (_context(subject_id="mallory"), _state(), _command(), AssetTransferRejectCodeV1.UNAUTHORIZED_SUBJECT),
        (_context(), _state(), _command(recipient="alice"), AssetTransferRejectCodeV1.SELF_TRANSFER),
        (_context(), _state(), _command(amount_atoms=0), AssetTransferRejectCodeV1.ZERO_AMOUNT),
        (_context(), _state(), _command(max_fee_atoms=1), AssetTransferRejectCodeV1.FEE_LIMIT_EXCEEDED),
        (_context(), _state(), _command(amount_atoms=99), AssetTransferRejectCodeV1.INSUFFICIENT_BALANCE),
    ),
)
def test_every_transfer_rejection_is_an_exact_no_op(
    context: AssetTransferContextV1,
    state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
    code: AssetTransferRejectCodeV1,
) -> None:
    result = transition_asset_transfer_v1(context, state, command)

    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is code
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty


def test_transfer_rejects_effect_width_before_balance_mutation() -> None:
    amount_atoms = 1 << 127
    pre_state = _state(
        fee_atoms=0,
        balances=(EconomicAmountV1("alice", "USD", "accounts", amount_atoms),),
        supply_atoms=amount_atoms,
    )

    result = transition_asset_transfer_v1(
        _context(),
        pre_state,
        _command(amount_atoms=amount_atoms, max_fee_atoms=0),
    )

    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.EFFECT_DELTA_OVERFLOW
    assert result.effects.is_empty


def test_zero_fee_split_and_merged_transfers_reach_the_same_state_root() -> None:
    pre_state = _state(fee_atoms=0)
    merged = transition_asset_transfer_v1(
        _context(),
        pre_state,
        _command(amount_atoms=30, max_fee_atoms=0),
    )
    first = transition_asset_transfer_v1(
        _context(),
        pre_state,
        _command(amount_atoms=10, max_fee_atoms=0),
    )
    assert isinstance(merged, AssetTransferAcceptedV1)
    assert isinstance(first, AssetTransferAcceptedV1)
    second = transition_asset_transfer_v1(
        _context(command_occurrence_id=_root(6)),
        first.post_state,
        _command(amount_atoms=20, max_fee_atoms=0),
    )

    assert isinstance(second, AssetTransferAcceptedV1)
    assert merged.post_state.state_root == second.post_state.state_root
    assert merged.effects.fee_conservation == ()
    assert second.effects.fee_conservation == ()


@pytest.mark.parametrize(
    ("fee_owner", "alice_atoms", "bob_atoms", "owner_delta"),
    (("alice", 70, 40, -30), ("bob", 68, 42, 32)),
)
def test_fee_owner_alias_is_aggregated_before_effect_projection(
    fee_owner: str,
    alice_atoms: int,
    bob_atoms: int,
    owner_delta: int,
) -> None:
    result = transition_asset_transfer_v1(
        _context(),
        _state(fee_owner=fee_owner),
        _command(),
    )

    assert isinstance(result, AssetTransferAcceptedV1)
    assert result.post_state.balance_atoms("alice", "USD") == alice_atoms
    assert result.post_state.balance_atoms("bob", "USD") == bob_atoms
    owner_row = next(
        row
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT and row.principal == fee_owner
    )
    assert owner_row.delta_atoms == owner_delta
    assert result.effects.asset_conservation[0].owned_and_custodied_post_atoms == 115


def test_accepted_result_rejects_a_parallel_journal_binding_mutation() -> None:
    result = transition_asset_transfer_v1(_context(), _state(), _command())
    assert isinstance(result, AssetTransferAcceptedV1)
    wrong_journal = replace(result.module_journal, effect_plan_root=_root(99))

    with pytest.raises(ValueError, match="wrong effect-plan root"):
        AssetTransferAcceptedV1(result.post_state, result.effects, wrong_journal)


def test_state_rejects_account_total_above_supply_and_u128_overflow() -> None:
    with pytest.raises(ValueError, match="account balances exceed supply"):
        _state(supply_atoms=114)
    with pytest.raises(ValueError, match="unsigned 128-bit"):
        AssetTransferPolicyV1("USD", "treasury", MAX_ATOMS_V1 + 1, True)
