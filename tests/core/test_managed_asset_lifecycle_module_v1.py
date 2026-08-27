from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)
from src.core.managed_asset_lifecycle_module_v1 import (
    transition_managed_asset_lifecycle_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy(
    *,
    asset_class: ManagedAssetClassV1 = ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
    issue_subject: str | None = "issuer",
    issue_root: str | None = _root(5),
    burn_root: str | None = _root(6),
    enabled: bool = True,
) -> ManagedAssetLifecyclePolicyV1:
    return ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=asset_class,
        issue_authority_subject=issue_subject,
        issue_policy_root=issue_root,
        burn_policy_root=burn_root,
        enabled=enabled,
    )


def _state(
    *,
    policy: ManagedAssetLifecyclePolicyV1 | None = None,
    balances: tuple[EconomicAmountV1, ...] | None = None,
    supply_atoms: int = 10,
) -> ManagedAssetLifecycleStateV1:
    return ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=(_policy() if policy is None else policy,),
        balances=(
            (EconomicAmountV1("alice", "USD", "accounts", 10),)
            if balances is None
            else balances
        ),
        supplies=(AssetSupplyV1("USD", supply_atoms),),
    )


def _context(
    *,
    subject_id: str = "issuer",
    grant_root: str | None = None,
    module_release_id: str | None = None,
) -> ManagedAssetLifecycleContextV1:
    return ManagedAssetLifecycleContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3) if module_release_id is None else module_release_id,
        command_occurrence_id=_root(4),
        subject_id=subject_id,
        grant_root=_root(5) if grant_root is None else grant_root,
    )


def _command(
    *,
    command_kind: str = MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    account_owner: str = "alice",
    amount_atoms: int = 7,
) -> ManagedAssetLifecycleCommandV1:
    return ManagedAssetLifecycleCommandV1(
        command_kind=command_kind,
        asset="USD",
        account_owner=account_owner,
        amount_atoms=amount_atoms,
    )


def _assert_noop(
    result: object,
    state: ManagedAssetLifecycleStateV1,
    code: ManagedAssetLifecycleRejectCodeV1,
) -> None:
    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert result.code is code
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty


def test_named_issue_profile_increases_account_and_supply_exactly() -> None:
    pre_state = _state()
    result = transition_managed_asset_lifecycle_v1(_context(), pre_state, _command())

    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert result.post_state.balance_atoms("alice", "USD") == 17
    assert result.post_state.supply_atoms("USD") == 17
    conservation = result.effects.asset_conservation[0]
    assert conservation.owned_and_custodied_pre_atoms == 10
    assert conservation.owned_and_custodied_post_atoms == 17
    assert conservation.supply_pre_atoms == 10
    assert conservation.supply_post_atoms == 17
    assert conservation.authorized_issue_atoms == 7
    assert conservation.authorized_burn_atoms == 0
    assert {(row.kind, row.principal, row.delta_atoms) for row in result.effects.rows} == {
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", 7),
        (EconomicEffectKindV1.ISSUE, "alice", 7),
    }
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.occurrence_consumptions == (_root(4),)
    assert result.module_journal.lane_id is LaneIdV1.ASSET_TRANSFER
    assert result.module_journal.private_port_root == ZERO_ROOT_V1
    assert result.module_journal.terminal_obligations_root == ZERO_ROOT_V1


def test_profile_bound_self_burn_decreases_account_and_supply_exactly() -> None:
    context = _context(subject_id="alice", grant_root=_root(6))
    command = _command(
        command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1,
        amount_atoms=4,
    )
    result = transition_managed_asset_lifecycle_v1(context, _state(), command)

    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert result.post_state.balance_atoms("alice", "USD") == 6
    assert result.post_state.supply_atoms("USD") == 6
    conservation = result.effects.asset_conservation[0]
    assert conservation.authorized_issue_atoms == 0
    assert conservation.authorized_burn_atoms == 4
    assert {(row.kind, row.principal, row.delta_atoms) for row in result.effects.rows} == {
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", -4),
        (EconomicEffectKindV1.BURN, "alice", -4),
    }


@pytest.mark.parametrize(
    ("name", "context", "command", "byte_hashes", "roots"),
    (
        (
            "issue",
            _context(),
            _command(),
            {
                "context": "3d38eaec45656db314443ff15bad0bae45f6211558055eff91f949143b3f09d6",
                "command": "533e6782f4d1151184bf2454c1bd831cbce2faf15b659085e185c34880437afa",
                "pre_state": "96cb14644957c04ecfc3b26cb54bcb4273bf7b6a46d2d0160db2bade4ef45855",
                "post_state": "0a15c9a3e825509148bbccf33ad798babc1e2adceed9f0dab24721e381b22e7c",
                "effects": "53c3029c697e5f6568e974b1a7dbcf38d5a1a4c184affd496ea33217473d97b6",
                "module_journal": "2ee98dc3179f173e7e398f9b6c7dee68fd8e43a55c7c6b27bb45a5090f01a71b",
            },
            {
                "pre_state": "0x3c026d5b4b479df83144ff80809160e085a53d83ef66ecf448262d75ad9a7781",
                "post_state": "0x5d4e148902614b6ed22fbe8d64885aa0f8237fde1da1f12843f28466640e8dee",
                "effects": "0x41af9589b39f6d7219aadfa5089718ca0f2787caa406a68b9e2706cfc3efd80e",
                "receipt": "0xdfd3e45ee519617a1c62c21181c64e8cc4d8180cbffd7c4330cdd13c8963e627",
                "module_journal": "0x5f3bd854e4fce48fe9a9b1c9eca948186fd488b86addaf4dcf2c2bfa91025d77",
            },
        ),
        (
            "burn",
            _context(subject_id="alice", grant_root=_root(6)),
            _command(command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1, amount_atoms=4),
            {
                "context": "6d3753828ecb423b1ca432de1dc5883a01381dfd2b906d10613d3c696afa1108",
                "command": "12f79d91a9f827df793cbaa85265483f26067777fdec27ce56e8e7db03bf735f",
                "pre_state": "96cb14644957c04ecfc3b26cb54bcb4273bf7b6a46d2d0160db2bade4ef45855",
                "post_state": "04932c1497458a8135e758abf37404756ed8cea48e6243637028ca94a3aec7b5",
                "effects": "22ef496d1bbf7763a4f1c80b15bab5ad4f78dd7fd1c6a64402712959dc27833e",
                "module_journal": "04a20ecc71d22da70a66d17a6dde6fb7f3ac8784135fcacdec3e9f118897ab6c",
            },
            {
                "pre_state": "0x3c026d5b4b479df83144ff80809160e085a53d83ef66ecf448262d75ad9a7781",
                "post_state": "0xba9ac989411ad9af4653b3b1bfd7b0fd0b41f0c752747a56c0d629b240a49b1b",
                "effects": "0x8f2e19f92b2ce7c1117b8656bdaedbad779ffb3100f90e226a5fb1aad8deed24",
                "receipt": "0xd24649608ef33d62efd81bf6740beb5aeba4015e9a8f1daf7b443821eed4581e",
                "module_journal": "0xa0f0f5709d2e3a205ea09737bfce98b96baef5bfa0ad9f9755c27c77cbff4191",
            },
        ),
    ),
)
def test_python_rust_issue_and_burn_canonical_vectors_are_pinned(
    name: str,
    context: ManagedAssetLifecycleContextV1,
    command: ManagedAssetLifecycleCommandV1,
    byte_hashes: dict[str, str],
    roots: dict[str, str],
) -> None:
    pre_state = _state()
    result = transition_managed_asset_lifecycle_v1(context, pre_state, command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1), name
    values = {
        "context": context,
        "command": command,
        "pre_state": pre_state,
        "post_state": result.post_state,
        "effects": result.effects,
        "module_journal": result.module_journal,
    }
    assert {
        key: sha256(canonical_global_bytes_v1(value)).hexdigest()
        for key, value in values.items()
    } == byte_hashes
    assert {
        "pre_state": pre_state.state_root,
        "post_state": result.post_state.state_root,
        "effects": result.effects.effect_plan_root,
        "receipt": result.receipt_root,
        "module_journal": result.module_journal.journal_root,
    } == roots


@pytest.mark.parametrize(
    "asset_class",
    tuple(
        asset_class
        for asset_class in ManagedAssetClassV1
        if asset_class is not ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN
    ),
)
@pytest.mark.parametrize(
    "command_kind",
    (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1),
)
def test_every_protocol_managed_asset_rejects_generic_issue_and_burn(
    asset_class: ManagedAssetClassV1,
    command_kind: str,
) -> None:
    policy = _policy(
        asset_class=asset_class,
        issue_subject=None,
        issue_root=None,
        burn_root=None,
    )
    state = _state(policy=policy)
    context = _context(
        subject_id="alice" if command_kind == MANAGED_ASSET_BURN_COMMAND_KIND_V1 else "issuer",
        grant_root=_root(6) if command_kind == MANAGED_ASSET_BURN_COMMAND_KIND_V1 else _root(5),
    )

    _assert_noop(
        transition_managed_asset_lifecycle_v1(
            context,
            state,
            _command(command_kind=command_kind),
        ),
        state,
        ManagedAssetLifecycleRejectCodeV1.GENERIC_AUTHORITY_FORBIDDEN,
    )


@pytest.mark.parametrize(
    ("context", "state", "command", "code"),
    (
        (
            _context(module_release_id=_root(99)),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV1.RELEASE_MISMATCH,
        ),
        (
            _context(),
            _state(),
            _command(command_kind="unknown"),
            ManagedAssetLifecycleRejectCodeV1.UNKNOWN_COMMAND,
        ),
        (
            _context(),
            _state(),
            replace(_command(), asset="EUR"),
            ManagedAssetLifecycleRejectCodeV1.UNKNOWN_ASSET,
        ),
        (
            _context(),
            _state(policy=_policy(enabled=False)),
            _command(),
            ManagedAssetLifecycleRejectCodeV1.DISABLED_ASSET,
        ),
        (
            _context(),
            _state(policy=_policy(issue_subject=None, issue_root=None)),
            _command(),
            ManagedAssetLifecycleRejectCodeV1.ISSUE_DISABLED,
        ),
        (
            _context(subject_id="mallory"),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV1.UNAUTHORIZED_SUBJECT,
        ),
        (
            _context(subject_id="alice", grant_root=_root(6)),
            _state(policy=_policy(burn_root=None)),
            _command(command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1),
            ManagedAssetLifecycleRejectCodeV1.BURN_DISABLED,
        ),
        (
            _context(grant_root=_root(99)),
            _state(),
            _command(),
            ManagedAssetLifecycleRejectCodeV1.AUTHORITY_PROFILE_MISMATCH,
        ),
        (
            _context(subject_id="mallory", grant_root=_root(6)),
            _state(),
            _command(command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1),
            ManagedAssetLifecycleRejectCodeV1.UNAUTHORIZED_SUBJECT,
        ),
        (
            _context(subject_id="alice", grant_root=_root(99)),
            _state(),
            _command(command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1),
            ManagedAssetLifecycleRejectCodeV1.AUTHORITY_PROFILE_MISMATCH,
        ),
        (
            _context(),
            _state(),
            _command(amount_atoms=0),
            ManagedAssetLifecycleRejectCodeV1.ZERO_AMOUNT,
        ),
        (
            _context(subject_id="alice", grant_root=_root(6)),
            _state(),
            _command(command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V1, amount_atoms=11),
            ManagedAssetLifecycleRejectCodeV1.INSUFFICIENT_BALANCE,
        ),
    ),
)
def test_every_lifecycle_rejection_is_an_exact_noop(
    context: ManagedAssetLifecycleContextV1,
    state: ManagedAssetLifecycleStateV1,
    command: ManagedAssetLifecycleCommandV1,
    code: ManagedAssetLifecycleRejectCodeV1,
) -> None:
    _assert_noop(
        transition_managed_asset_lifecycle_v1(context, state, command),
        state,
        code,
    )


def test_effect_width_and_supply_overflow_reject_before_mutation() -> None:
    amount_atoms = 1 << 127
    state = _state(balances=(), supply_atoms=0)
    _assert_noop(
        transition_managed_asset_lifecycle_v1(
            _context(),
            state,
            _command(amount_atoms=amount_atoms),
        ),
        state,
        ManagedAssetLifecycleRejectCodeV1.EFFECT_DELTA_OVERFLOW,
    )

    full_supply = _state(
        balances=(EconomicAmountV1("bob", "USD", "accounts", MAX_ATOMS_V1),),
        supply_atoms=MAX_ATOMS_V1,
    )
    _assert_noop(
        transition_managed_asset_lifecycle_v1(
            _context(),
            full_supply,
            _command(amount_atoms=1),
        ),
        full_supply,
        ManagedAssetLifecycleRejectCodeV1.SUPPLY_OVERFLOW,
    )


def test_state_forbids_generic_authority_on_protocol_managed_assets() -> None:
    with pytest.raises(ValueError, match="protocol-managed asset"):
        _policy(asset_class=ManagedAssetClassV1.CANONICAL_ZUSD)


def test_accepted_result_rejects_parallel_journal_mutation() -> None:
    result = transition_managed_asset_lifecycle_v1(_context(), _state(), _command())
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)

    with pytest.raises(ValueError, match="wrong effect-plan root"):
        ManagedAssetLifecycleAcceptedV1(
            result.post_state,
            result.effects,
            replace(result.module_journal, effect_plan_root=_root(99)),
        )
