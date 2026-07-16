"""BDD and invariant evidence for the unmounted Liquity V1 owner-close core."""

from __future__ import annotations

from dataclasses import fields, replace
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.zusd_owner_close as owner_close_module
from src.core.zusd_owner_close import (
    LIQUITY_V1_CCR_E18,
    LIQUITY_V1_GAS_RESERVE_ATOMS,
    LIQUITY_V1_MIN_NET_DEBT_ATOMS,
    PRICE_SCALE_E18,
    U256_MAX,
    U256_MODULUS,
    ZUSD_SCALE,
    AccountIdentity,
    ActiveVaultCount,
    ActiveWithCompositeDebt,
    AuthenticatedOwnerCapability,
    CandidateTCRAtOrAboveCCR,
    CandidateTCRBelowCCR,
    ClosedByOwner,
    CloseVaultRequest,
    CollateralAtoms,
    CommitmentDigest,
    GasReserveProjection,
    GuardBlocked,
    GuardFailed,
    GuardOutcome,
    GuardPassed,
    NormalModeDecision,
    OwnerCloseAccepted,
    OwnerCloseContext,
    OwnerCloseEffects,
    OwnerCloseReject,
    OwnerCloseRejected,
    OwnerCloseState,
    OwnerWalletProjection,
    PriceE18,
    RecoveryModeDecision,
    SequenceNumber,
    StakeAtoms,
    SupplyProjection,
    SystemAggregateProjection,
    VaultIdentity,
    ZUSDAtoms,
    committed_state,
    derive_risk_mode_decision,
    run_owner_close,
)

Q = ZUSD_SCALE


def _digest(fill: int) -> CommitmentDigest:
    return CommitmentDigest(bytes([fill]) * 32)


def _context(sequence: int = 0, *, fill: int = 1) -> OwnerCloseContext:
    digest = _digest(fill)
    return OwnerCloseContext(
        vault_state_root=digest,
        asset_ledger_root=digest,
        gas_reserve_root=digest,
        risk_decision_root=digest,
        owner_close_sequence=SequenceNumber(sequence),
    )


def _active(
    *,
    owner: int = 11,
    collateral_atoms: int = 10 * Q,
    net_debt_atoms: int = 1_800 * Q,
    stake_atoms: int = 10 * Q,
) -> ActiveWithCompositeDebt:
    return ActiveWithCompositeDebt(
        vault_identity=VaultIdentity(101),
        owner_identity=AccountIdentity(owner),
        collateral_atoms=CollateralAtoms(collateral_atoms),
        net_debt_atoms=ZUSDAtoms(net_debt_atoms),
        reserve_debt_atoms=ZUSDAtoms(LIQUITY_V1_GAS_RESERVE_ATOMS),
        stake_atoms=StakeAtoms(stake_atoms),
    )


def _state(
    *,
    active: ActiveWithCompositeDebt | None = None,
    system_collateral_atoms: int = 30 * Q,
    system_debt_atoms: int = 4_000 * Q,
    total_stake_atoms: int = 30 * Q,
    active_count: int = 2,
    owner_zusd_atoms: int = 1_800 * Q,
    owner_collateral_atoms: int = 5 * Q,
    target_reserve_atoms: int = LIQUITY_V1_GAS_RESERVE_ATOMS,
    gas_pool_atoms: int = 2 * LIQUITY_V1_GAS_RESERVE_ATOMS,
    total_supply_atoms: int = 4_000 * Q,
    sequence: int = 0,
) -> OwnerCloseState:
    vault = active or _active()
    return OwnerCloseState(
        lifecycle=vault,
        system=SystemAggregateProjection(
            collateral_atoms=CollateralAtoms(system_collateral_atoms),
            composite_debt_atoms=ZUSDAtoms(system_debt_atoms),
            total_active_stake_atoms=StakeAtoms(total_stake_atoms),
            active_vault_and_index_count=ActiveVaultCount(active_count),
        ),
        owner_wallet=OwnerWalletProjection(
            owner_identity=vault.owner_identity,
            zusd_balance_atoms=ZUSDAtoms(owner_zusd_atoms),
            collateral_balance_atoms=CollateralAtoms(owner_collateral_atoms),
        ),
        gas_reserve=GasReserveProjection(
            target_vault_identity=vault.vault_identity,
            target_reserve_atoms=ZUSDAtoms(target_reserve_atoms),
            gas_pool_custody_atoms=ZUSDAtoms(gas_pool_atoms),
        ),
        supply=SupplyProjection(
            total_zusd_supply_atoms=ZUSDAtoms(total_supply_atoms),
        ),
        transition_sequence=SequenceNumber(sequence),
    )


def _request(
    state: OwnerCloseState,
    *,
    price_e18: int = 200 * PRICE_SCALE_E18,
    context: OwnerCloseContext | None = None,
    candidate_at_or_above: bool = True,
) -> CloseVaultRequest:
    active = state.lifecycle
    if type(active) is not ActiveWithCompositeDebt:
        raise TypeError("test request helper requires an active lifecycle")
    bound_context = context or _context(state.transition_sequence.value)
    candidate_collateral = (
        state.system.collateral_atoms.value - active.collateral_atoms.value
    )
    candidate_debt = (
        state.system.composite_debt_atoms.value - active.composite_debt_atoms.value
    )
    candidate_type = (
        CandidateTCRAtOrAboveCCR if candidate_at_or_above else CandidateTCRBelowCCR
    )
    return CloseVaultRequest(
        target_vault_identity=active.vault_identity,
        authority=AuthenticatedOwnerCapability(
            actor_identity=active.owner_identity,
            target_vault_identity=active.vault_identity,
            authenticated_command_occurrence=SequenceNumber(7),
            expected_context=bound_context,
            expected_owner_close_sequence=state.transition_sequence,
        ),
        risk_mode=derive_risk_mode_decision(
            source_context=bound_context,
            system_collateral_atoms=state.system.collateral_atoms,
            system_composite_debt_atoms=state.system.composite_debt_atoms,
            price_e18=PriceE18(price_e18),
        ),
        candidate_tcr=candidate_type(
            source_context=bound_context,
            candidate_system_collateral_atoms=CollateralAtoms(candidate_collateral),
            candidate_system_composite_debt_atoms=ZUSDAtoms(candidate_debt),
            price_e18=PriceE18(price_e18),
        ),
        route_context=bound_context,
        actual_context=bound_context,
    )


def _assert_reject(
    result: object,
    pre_state: OwnerCloseState,
    reason: OwnerCloseReject,
) -> OwnerCloseRejected:
    assert type(result) is OwnerCloseRejected
    assert result.primary_reason is reason
    assert committed_state(result) == pre_state
    return result


def _reconstruct_accepted(
    source: OwnerCloseAccepted,
    *,
    pre_state: OwnerCloseState | None = None,
    request: CloseVaultRequest | None = None,
    post_state: OwnerCloseState | None = None,
    effects: OwnerCloseEffects | None = None,
    guard_outcomes: tuple[GuardOutcome, ...] | None = None,
    construction_token: object = owner_close_module._RESULT_CONSTRUCTION_TOKEN,
) -> OwnerCloseAccepted:
    return OwnerCloseAccepted(
        pre_state=source.pre_state if pre_state is None else pre_state,
        request=source.request if request is None else request,
        post_state=source.post_state if post_state is None else post_state,
        effects=source.effects if effects is None else effects,
        guard_outcomes=(
            source.guard_outcomes if guard_outcomes is None else guard_outcomes
        ),
        _construction_token=construction_token,
    )


def test_given_source_valid_close_when_evaluated_then_every_leg_commits_atomically() -> None:
    """Given/When/Then: the pinned V1 acceptance vector closes exactly once."""

    pre = _state()
    result = run_owner_close(pre, _request(pre))

    assert type(result) is OwnerCloseAccepted
    post = committed_state(result)
    assert type(post.lifecycle) is ClosedByOwner
    assert post.system.composite_debt_atoms.value == 2_000 * Q
    assert post.supply.total_zusd_supply_atoms.value == 2_000 * Q
    assert post.owner_wallet.zusd_balance_atoms.value == 0
    assert post.gas_reserve.gas_pool_custody_atoms.value == 200 * Q
    assert post.owner_wallet.collateral_balance_atoms.value == 15 * Q
    assert result.effects.total_zusd_burn_atoms.value == 2_000 * Q
    assert result.effects.owner_net_debt_burn_atoms.value == 1_800 * Q
    assert result.effects.gas_reserve_burn_atoms.value == 200 * Q


def test_active_lifecycle_makes_subfloor_debt_and_wrong_reserve_unrepresentable() -> None:
    with pytest.raises(ValueError, match="at least 1800e18"):
        _active(net_debt_atoms=LIQUITY_V1_MIN_NET_DEBT_ATOMS - 1)
    with pytest.raises(ValueError, match="200e18"):
        ActiveWithCompositeDebt(
            vault_identity=VaultIdentity(101),
            owner_identity=AccountIdentity(11),
            collateral_atoms=CollateralAtoms(Q),
            net_debt_atoms=ZUSDAtoms(LIQUITY_V1_MIN_NET_DEBT_ATOMS),
            reserve_debt_atoms=ZUSDAtoms(LIQUITY_V1_GAS_RESERVE_ATOMS - 1),
            stake_atoms=StakeAtoms(Q),
        )
    with pytest.raises(TypeError, match="must be an int"):
        ZUSDAtoms(True)


def test_closed_lifecycle_structurally_has_no_active_value_or_index_fields() -> None:
    closed = ClosedByOwner(
        VaultIdentity(101),
        AccountIdentity(11),
        SequenceNumber(1),
    )
    for active_field in (
        "collateral_atoms",
        "net_debt_atoms",
        "reserve_debt_atoms",
        "stake_atoms",
    ):
        assert not hasattr(closed, active_field)


def test_authenticated_owner_capability_requires_a_positive_occurrence() -> None:
    context = _context()
    with pytest.raises(ValueError, match="occurrence must be positive"):
        AuthenticatedOwnerCapability(
            actor_identity=AccountIdentity(11),
            target_vault_identity=VaultIdentity(101),
            authenticated_command_occurrence=SequenceNumber(0),
            expected_context=context,
            expected_owner_close_sequence=SequenceNumber(0),
        )


def test_primitive_and_lifecycle_boundaries_fail_closed() -> None:
    with pytest.raises(ValueError, match="unsigned 256-bit"):
        ZUSDAtoms(-1)
    with pytest.raises(ValueError, match="unsigned 256-bit"):
        ZUSDAtoms(U256_MODULUS)
    with pytest.raises(ValueError, match="must be positive"):
        AccountIdentity(0)
    with pytest.raises(TypeError, match="must be bytes"):
        CommitmentDigest(cast(bytes, "not-bytes"))
    with pytest.raises(ValueError, match="exactly 32 bytes"):
        CommitmentDigest(b"short")
    with pytest.raises(ValueError, match="positive collateral"):
        _active(collateral_atoms=0)
    with pytest.raises(ValueError, match="composite debt"):
        _active(net_debt_atoms=U256_MAX)
    with pytest.raises(ValueError, match="occurrence must be positive"):
        ClosedByOwner(VaultIdentity(101), AccountIdentity(11), SequenceNumber(0))
    valid = _state()
    with pytest.raises(TypeError, match="lifecycle"):
        replace(valid, lifecycle=cast(ActiveWithCompositeDebt, object()))
    with pytest.raises(TypeError, match="system must be"):
        replace(valid, system=cast(SystemAggregateProjection, object()))


def test_zero_candidate_debt_has_the_source_infinite_tcr_classification() -> None:
    decision = CandidateTCRAtOrAboveCCR(
        _context(),
        CollateralAtoms(0),
        ZUSDAtoms(0),
        PriceE18(1),
    )
    assert decision.candidate_system_composite_debt_atoms.value == 0


def test_close_request_rejects_open_ended_decision_types() -> None:
    pre = _state()
    request = _request(pre)
    with pytest.raises(TypeError, match="Normal or Recovery"):
        replace(request, risk_mode=cast(NormalModeDecision, object()))
    with pytest.raises(TypeError, match="candidate TCR decision"):
        replace(
            request,
            candidate_tcr=cast(CandidateTCRAtOrAboveCCR, object()),
        )
    with pytest.raises(ValueError, match="lower ordinal"):
        GuardBlocked(1, 1)


def test_guard_table_rejects_reject_code_order_drift() -> None:
    with pytest.raises(RuntimeError, match="guard order diverged"):
        owner_close_module._append_guard(
            [],
            lambda: True,
            OwnerCloseReject.WRONG_VAULT_OWNER,
        )


def test_exact_ccr_boundary_is_accepted_and_one_atom_below_is_typed_below() -> None:
    context = _context()
    exact = CandidateTCRAtOrAboveCCR(
        context,
        CollateralAtoms(12 * Q),
        ZUSDAtoms(2_000 * Q),
        PriceE18(250 * PRICE_SCALE_E18),
    )
    below = CandidateTCRBelowCCR(
        context,
        CollateralAtoms(12 * Q - 1),
        ZUSDAtoms(2_000 * Q),
        PriceE18(250 * PRICE_SCALE_E18),
    )
    assert LIQUITY_V1_CCR_E18 == 1_500_000_000_000_000_000
    assert exact.candidate_system_collateral_atoms.value == 12 * Q
    assert below.candidate_system_collateral_atoms.value == 12 * Q - 1
    with pytest.raises(ValueError, match="at or above"):
        CandidateTCRAtOrAboveCCR(
            context,
            CollateralAtoms(12 * Q - 1),
            ZUSDAtoms(2_000 * Q),
            PriceE18(250 * PRICE_SCALE_E18),
        )
    with pytest.raises(ValueError, match="below"):
        CandidateTCRBelowCCR(
            context,
            CollateralAtoms(12 * Q),
            ZUSDAtoms(2_000 * Q),
            PriceE18(250 * PRICE_SCALE_E18),
        )


def test_risk_mode_is_a_disjoint_exhaustive_partition_of_the_system_tcr() -> None:
    context = _context()
    debt = ZUSDAtoms(4_000 * Q)
    price = PriceE18(200 * PRICE_SCALE_E18)
    exact_collateral = CollateralAtoms(30 * Q)
    below_collateral = CollateralAtoms(30 * Q - 1)

    exact = derive_risk_mode_decision(context, exact_collateral, debt, price)
    below = derive_risk_mode_decision(context, below_collateral, debt, price)

    assert type(exact) is NormalModeDecision
    assert type(below) is RecoveryModeDecision
    with pytest.raises(ValueError, match="at or above"):
        NormalModeDecision(context, below_collateral, debt, price)
    with pytest.raises(ValueError, match="below"):
        RecoveryModeDecision(context, exact_collateral, debt, price)
    assert type(
        derive_risk_mode_decision(
            context,
            CollateralAtoms(U256_MAX),
            ZUSDAtoms(0),
            PriceE18(U256_MAX),
        )
    ) is NormalModeDecision
    CandidateTCRAtOrAboveCCR(
        context,
        CollateralAtoms(U256_MAX),
        ZUSDAtoms(0),
        PriceE18(U256_MAX),
    )


def test_inactive_target_blocks_dependent_guards_without_dereference() -> None:
    active_pre = _state()
    request = _request(active_pre)
    active = active_pre.lifecycle
    assert type(active) is ActiveWithCompositeDebt
    closed_pre = replace(
        active_pre,
        lifecycle=ClosedByOwner(
            active.vault_identity,
            active.owner_identity,
            SequenceNumber(1),
        ),
    )
    result = _assert_reject(
        run_owner_close(closed_pre, request),
        closed_pre,
        OwnerCloseReject.TARGET_VAULT_INACTIVE,
    )
    for ordinal in (1, 2, 4, 5, 6, 7, 8, 9, 10, 11):
        blocked = result.guard_outcomes[ordinal]
        assert type(blocked) is GuardBlocked
        assert blocked.prerequisite_ordinal == 0


def test_wrong_authenticated_actor_rejects_before_any_value_plan() -> None:
    pre = _state()
    request = _request(pre)
    request = replace(
        request,
        authority=replace(request.authority, actor_identity=AccountIdentity(99)),
    )
    _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.WRONG_VAULT_OWNER,
    )


def test_wrong_wallet_projection_cannot_burn_or_credit_another_owner() -> None:
    pre = _state()
    pre = replace(
        pre,
        owner_wallet=replace(pre.owner_wallet, owner_identity=AccountIdentity(99)),
    )
    result = _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.OWNER_WALLET_BINDING_MISMATCH,
    )
    blocked = result.guard_outcomes[4]
    assert type(blocked) is GuardBlocked
    assert blocked.prerequisite_ordinal == 2


def test_recovery_mode_close_is_a_noop() -> None:
    pre = _state(system_collateral_atoms=30 * Q - 1)
    request = _request(pre)
    assert type(request.risk_mode) is RecoveryModeDecision
    _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.RECOVERY_MODE,
    )


def test_short_owner_balance_rejects_the_exact_net_debt_burn() -> None:
    pre = _state(owner_zusd_atoms=1_800 * Q - 1)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.INSUFFICIENT_OWNER_NET_DEBT_BALANCE,
    )


def test_final_active_vault_cannot_close() -> None:
    pre = _state(
        active_count=1,
        gas_pool_atoms=LIQUITY_V1_GAS_RESERVE_ATOMS,
    )
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.FINAL_ACTIVE_VAULT,
    )


def test_zero_active_count_is_also_an_inconsistent_candidate_aggregate() -> None:
    pre = _state(active_count=0, gas_pool_atoms=0)
    result = _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.FINAL_ACTIVE_VAULT,
    )
    assert OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT in result.violations


@pytest.mark.parametrize(
    "underflow_case",
    ("collateral", "debt", "stake", "supply"),
)
def test_candidate_aggregate_underflow_rejects_before_candidate_dereference(
    underflow_case: str,
) -> None:
    valid_pre = _state()
    request = _request(valid_pre)
    if underflow_case == "collateral":
        underflow_pre = _state(system_collateral_atoms=10 * Q - 1)
    elif underflow_case == "debt":
        underflow_pre = _state(
            system_debt_atoms=2_000 * Q - 1,
            total_supply_atoms=2_000 * Q - 1,
        )
    elif underflow_case == "stake":
        underflow_pre = _state(total_stake_atoms=10 * Q - 1)
    else:
        underflow_pre = _state(total_supply_atoms=2_000 * Q - 1)
    result = _assert_reject(
        run_owner_close(underflow_pre, request),
        underflow_pre,
        OwnerCloseReject.CANDIDATE_AGGREGATE_UNDERFLOW,
    )
    blocked = result.guard_outcomes[8]
    assert type(blocked) is GuardBlocked
    assert blocked.prerequisite_ordinal == 6


def test_candidate_supply_debt_mismatch_is_a_typed_noop() -> None:
    pre = _state(total_supply_atoms=4_000 * Q - 1)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT,
    )


def test_remaining_active_vault_cannot_be_backed_by_reserve_only_debt() -> None:
    pre = _state(
        system_collateral_atoms=17 * Q,
        system_debt_atoms=2_200 * Q,
        total_stake_atoms=11 * Q,
        total_supply_atoms=2_200 * Q,
    )
    request = _request(pre)
    assert type(request.risk_mode) is NormalModeDecision
    assert type(request.candidate_tcr) is CandidateTCRAtOrAboveCCR

    _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT,
    )


def test_substituted_candidate_aggregate_cannot_authorize_a_different_close() -> None:
    pre = _state()
    request = _request(pre)
    candidate = request.candidate_tcr
    request = replace(
        request,
        candidate_tcr=CandidateTCRAtOrAboveCCR(
            candidate.source_context,
            CollateralAtoms(candidate.candidate_system_collateral_atoms.value + 1),
            candidate.candidate_system_composite_debt_atoms,
            candidate.price_e18,
        ),
    )
    _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT,
    )


def test_historical_burn_is_not_acceptance_critical_state() -> None:
    assert tuple(field.name for field in fields(SupplyProjection)) == (
        "total_zusd_supply_atoms",
    )
    pre = _state()
    result = run_owner_close(pre, _request(pre))
    assert type(result) is OwnerCloseAccepted
    assert result.effects.total_zusd_burn_atoms.value == 2_000 * Q


def test_candidate_aggregate_requires_positive_collateral_for_every_remaining_vault() -> None:
    active = _active(collateral_atoms=1, stake_atoms=0)
    pre = _state(
        active=active,
        system_collateral_atoms=2,
        system_debt_atoms=6_000 * Q,
        total_stake_atoms=0,
        active_count=3,
        gas_pool_atoms=3 * LIQUITY_V1_GAS_RESERVE_ATOMS,
        total_supply_atoms=6_000 * Q,
    )
    _assert_reject(
        run_owner_close(pre, _request(pre, price_e18=6 * 10**39)),
        pre,
        OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT,
    )


def test_candidate_aggregate_accepts_exact_positive_collateral_floor() -> None:
    active = _active(collateral_atoms=1, stake_atoms=0)
    pre = _state(
        active=active,
        system_collateral_atoms=3,
        system_debt_atoms=6_000 * Q,
        total_stake_atoms=0,
        active_count=3,
        gas_pool_atoms=3 * LIQUITY_V1_GAS_RESERVE_ATOMS,
        total_supply_atoms=6_000 * Q,
    )
    result = run_owner_close(pre, _request(pre, price_e18=3 * 10**39))
    assert type(result) is OwnerCloseAccepted
    assert committed_state(result).system.collateral_atoms.value == 2


def test_candidate_collateral_credit_and_reserve_count_overflows_are_noops() -> None:
    collateral_overflow = _state(owner_collateral_atoms=U256_MAX - 10 * Q + 1)
    _assert_reject(
        run_owner_close(collateral_overflow, _request(collateral_overflow)),
        collateral_overflow,
        OwnerCloseReject.CANDIDATE_ACCOUNTING_OVERFLOW,
    )
    overflowing_count = U256_MAX // LIQUITY_V1_GAS_RESERVE_ATOMS + 1
    count_overflow = _state(active_count=overflowing_count)
    _assert_reject(
        run_owner_close(count_overflow, _request(count_overflow)),
        count_overflow,
        OwnerCloseReject.CANDIDATE_ACCOUNTING_OVERFLOW,
    )


def test_post_close_tcr_below_ccr_is_a_noop() -> None:
    high_collateral_target = _active(collateral_atoms=20 * Q, stake_atoms=20 * Q)
    pre = _state(active=high_collateral_target, total_stake_atoms=40 * Q)
    request = _request(
        pre,
        price_e18=250 * PRICE_SCALE_E18,
        candidate_at_or_above=False,
    )
    _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.POST_CLOSE_TCR_BELOW_CCR,
    )


def test_exact_post_close_tcr_at_ccr_accepts() -> None:
    active = _active(collateral_atoms=12 * Q, stake_atoms=12 * Q)
    pre = _state(
        active=active,
        system_collateral_atoms=24 * Q,
        total_stake_atoms=32 * Q,
    )
    result = run_owner_close(
        pre,
        _request(pre, price_e18=250 * PRICE_SCALE_E18),
    )
    assert type(result) is OwnerCloseAccepted
    assert committed_state(result).system.collateral_atoms.value == 12 * Q


def test_reserve_mismatch_is_a_noop() -> None:
    pre = _state(target_reserve_atoms=LIQUITY_V1_GAS_RESERVE_ATOMS - 1)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.RESERVE_CUSTODY_MISMATCH,
    )


def test_reserve_insufficiency_is_a_noop() -> None:
    pre = _state(gas_pool_atoms=LIQUITY_V1_GAS_RESERVE_ATOMS - 1)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.RESERVE_CUSTODY_INSUFFICIENT,
    )


def test_gas_pool_cardinality_shortfall_is_a_noop() -> None:
    pre = _state(gas_pool_atoms=LIQUITY_V1_GAS_RESERVE_ATOMS + 1)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.RESERVE_CUSTODY_MISMATCH,
    )


def test_gas_pool_donation_cannot_grief_owner_close() -> None:
    donated_atoms = 1
    pre = _state(
        gas_pool_atoms=2 * LIQUITY_V1_GAS_RESERVE_ATOMS + donated_atoms
    )

    result = run_owner_close(pre, _request(pre))

    assert type(result) is OwnerCloseAccepted
    post = committed_state(result)
    assert post.gas_reserve.gas_pool_custody_atoms.value == (
        LIQUITY_V1_GAS_RESERVE_ATOMS + donated_atoms
    )
    assert result.effects.gas_reserve_burn_atoms.value == (
        LIQUITY_V1_GAS_RESERVE_ATOMS
    )


def test_sequence_exhaustion_is_a_noop() -> None:
    pre = _state(sequence=U256_MAX)
    _assert_reject(
        run_owner_close(pre, _request(pre)),
        pre,
        OwnerCloseReject.OWNER_CLOSE_SEQUENCE_EXHAUSTED,
    )


def test_any_context_or_decision_binding_substitution_rejects_as_stale() -> None:
    pre = _state()
    request = _request(pre)
    stale_context = _context(fill=2)
    variants = (
        replace(request, route_context=stale_context),
        replace(
            request,
            authority=replace(request.authority, expected_context=stale_context),
        ),
        replace(
            request,
            risk_mode=replace(request.risk_mode, source_context=stale_context),
        ),
        replace(
            request,
            candidate_tcr=replace(request.candidate_tcr, source_context=stale_context),
        ),
        replace(
            request,
            authority=replace(
                request.authority,
                expected_owner_close_sequence=SequenceNumber(1),
            ),
        ),
        replace(
            request,
            risk_mode=replace(
                request.risk_mode,
                system_collateral_atoms=CollateralAtoms(
                    request.risk_mode.system_collateral_atoms.value + 1
                ),
            ),
        ),
    )
    for variant in variants:
        _assert_reject(
            run_owner_close(pre, variant),
            pre,
            OwnerCloseReject.STALE_OWNER_CLOSE_CONTEXT,
        )


def test_tcr_numerator_overflow_is_rejected_at_typed_decision_construction() -> None:
    with pytest.raises(ValueError, match="numerator exceeds u256"):
        CandidateTCRAtOrAboveCCR(
            _context(),
            CollateralAtoms(U256_MAX),
            ZUSDAtoms(Q),
            PriceE18(2),
        )


def test_multiple_failures_retain_stable_primary_and_complete_projection() -> None:
    pre = _state(
        active_count=1,
        owner_zusd_atoms=1,
        gas_pool_atoms=LIQUITY_V1_GAS_RESERVE_ATOMS,
        system_collateral_atoms=30 * Q - 1,
    )
    request = _request(pre)
    assert type(request.risk_mode) is RecoveryModeDecision
    request = replace(
        request,
        authority=replace(request.authority, actor_identity=AccountIdentity(99)),
    )
    result = _assert_reject(
        run_owner_close(pre, request),
        pre,
        OwnerCloseReject.WRONG_VAULT_OWNER,
    )
    assert result.violations[:4] == (
        OwnerCloseReject.WRONG_VAULT_OWNER,
        OwnerCloseReject.RECOVERY_MODE,
        OwnerCloseReject.INSUFFICIENT_OWNER_NET_DEBT_BALANCE,
        OwnerCloseReject.FINAL_ACTIVE_VAULT,
    )


@pytest.mark.parametrize(
    ("net_debt", "target_collateral", "other_debt", "other_collateral", "price"),
    (
        (1_800, 10, 2_000, 20, 200),
        (2_400, 12, 3_000, 30, 200),
        (5_000, 40, 4_000, 40, 200),
        (9_000, 80, 2_000, 20, 200),
    ),
)
def test_bounded_acceptance_preserves_supply_debt_custody_and_stake(
    net_debt: int,
    target_collateral: int,
    other_debt: int,
    other_collateral: int,
    price: int,
) -> None:
    active = _active(
        collateral_atoms=target_collateral * Q,
        net_debt_atoms=net_debt * Q,
        stake_atoms=target_collateral * Q,
    )
    composite = active.composite_debt_atoms.value
    pre = _state(
        active=active,
        system_collateral_atoms=(target_collateral + other_collateral) * Q,
        system_debt_atoms=composite + other_debt * Q,
        total_stake_atoms=(target_collateral + other_collateral) * Q,
        owner_zusd_atoms=net_debt * Q,
        total_supply_atoms=composite + other_debt * Q,
    )
    result = run_owner_close(
        pre,
        _request(pre, price_e18=price * PRICE_SCALE_E18),
    )
    assert type(result) is OwnerCloseAccepted
    post = committed_state(result)
    assert (
        pre.supply.total_zusd_supply_atoms.value
        - post.supply.total_zusd_supply_atoms.value
        == composite
    )
    assert (
        pre.system.composite_debt_atoms.value
        - post.system.composite_debt_atoms.value
        == composite
    )
    assert post.supply.total_zusd_supply_atoms == post.system.composite_debt_atoms
    assert (
        pre.owner_wallet.zusd_balance_atoms.value
        - post.owner_wallet.zusd_balance_atoms.value
        == net_debt * Q
    )
    assert (
        pre.gas_reserve.gas_pool_custody_atoms.value
        - post.gas_reserve.gas_pool_custody_atoms.value
        == LIQUITY_V1_GAS_RESERVE_ATOMS
    )
    assert post.gas_reserve.gas_pool_custody_atoms.value == 200 * Q
    assert post.gas_reserve.target_reserve_atoms.value == 0
    assert (
        pre.system.collateral_atoms.value - post.system.collateral_atoms.value
        == target_collateral * Q
    )
    assert (
        post.owner_wallet.collateral_balance_atoms.value
        - pre.owner_wallet.collateral_balance_atoms.value
        == target_collateral * Q
    )
    assert (
        pre.system.total_active_stake_atoms.value
        - post.system.total_active_stake_atoms.value
        == target_collateral * Q
    )
    assert post.system.active_vault_and_index_count.value == 1


def test_extra_owner_balance_is_metamorphic_and_does_not_change_effects() -> None:
    exact_pre = _state(owner_zusd_atoms=1_800 * Q)
    rich_pre = _state(owner_zusd_atoms=2_300 * Q)
    exact = run_owner_close(exact_pre, _request(exact_pre))
    rich = run_owner_close(rich_pre, _request(rich_pre))
    assert type(exact) is OwnerCloseAccepted
    assert type(rich) is OwnerCloseAccepted
    assert exact.effects == rich.effects
    assert committed_state(rich).owner_wallet.zusd_balance_atoms.value == 500 * Q


def test_importable_result_token_cannot_construct_a_forged_supply_poststate() -> None:
    pre = _state()
    result = run_owner_close(pre, _request(pre))
    assert type(result) is OwnerCloseAccepted
    forged_post = replace(
        result.post_state,
        supply=replace(
            result.post_state.supply,
            total_zusd_supply_atoms=ZUSDAtoms(
                result.post_state.supply.total_zusd_supply_atoms.value + 1
            ),
        ),
    )
    with pytest.raises(ValueError, match="deterministic transition construction"):
        OwnerCloseAccepted(
            pre_state=result.pre_state,
            request=result.request,
            post_state=forged_post,
            effects=result.effects,
            guard_outcomes=result.guard_outcomes,
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )


def test_committed_state_rejects_low_level_post_construction_mutation() -> None:
    pre = _state()
    result = run_owner_close(pre, _request(pre))
    assert type(result) is OwnerCloseAccepted
    forged_post = replace(
        result.post_state,
        supply=replace(
            result.post_state.supply,
            total_zusd_supply_atoms=ZUSDAtoms(
                result.post_state.supply.total_zusd_supply_atoms.value + 1
            ),
        ),
    )
    object.__setattr__(result, "post_state", forged_post)

    with pytest.raises(ValueError, match="deterministic transition replay"):
        committed_state(result)


def test_importable_result_token_cannot_construct_forged_effects_or_rejection() -> None:
    pre = _state()
    accepted = run_owner_close(pre, _request(pre))
    assert type(accepted) is OwnerCloseAccepted
    forged_effects = replace(
        accepted.effects,
        stake_removal_atoms=StakeAtoms(
            accepted.effects.stake_removal_atoms.value + 1
        ),
    )
    with pytest.raises(ValueError, match="deterministic transition construction"):
        OwnerCloseAccepted(
            pre_state=accepted.pre_state,
            request=accepted.request,
            post_state=accepted.post_state,
            effects=forged_effects,
            guard_outcomes=accepted.guard_outcomes,
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )

    recovery_pre = _state(system_collateral_atoms=30 * Q - 1)
    recovery_request = _request(recovery_pre)
    assert type(recovery_request.risk_mode) is RecoveryModeDecision
    rejected = run_owner_close(recovery_pre, recovery_request)
    assert type(rejected) is OwnerCloseRejected
    with pytest.raises(ValueError, match="deterministic guard evaluation"):
        OwnerCloseRejected(
            pre_state=recovery_pre,
            request=accepted.request,
            guard_outcomes=rejected.guard_outcomes,
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )


def test_effect_constructor_kills_every_conservation_mutation() -> None:
    pre = _state()
    result = run_owner_close(pre, _request(pre))
    assert type(result) is OwnerCloseAccepted
    effects = result.effects
    with pytest.raises(ValueError, match="total zUSD burn"):
        replace(
            effects,
            total_zusd_burn_atoms=ZUSDAtoms(effects.total_zusd_burn_atoms.value + 1),
        )
    with pytest.raises(ValueError, match="system debt decrease"):
        replace(
            effects,
            system_composite_debt_decrease_atoms=ZUSDAtoms(
                effects.system_composite_debt_decrease_atoms.value + 1
            ),
        )
    wrong_reserve = ZUSDAtoms(LIQUITY_V1_GAS_RESERVE_ATOMS - 1)
    wrong_total = ZUSDAtoms(
        effects.owner_net_debt_burn_atoms.value + wrong_reserve.value
    )
    with pytest.raises(ValueError, match="exactly the Liquity V1 reserve"):
        replace(
            effects,
            gas_reserve_burn_atoms=wrong_reserve,
            total_zusd_burn_atoms=wrong_total,
            system_composite_debt_decrease_atoms=wrong_total,
        )
    with pytest.raises(ValueError, match="collateral return"):
        replace(
            effects,
            system_collateral_decrease_atoms=CollateralAtoms(
                effects.system_collateral_decrease_atoms.value + 1
            ),
        )
    with pytest.raises(ValueError, match="sorted-index removal"):
        replace(
            effects,
            sorted_index_removal_vault_identity=VaultIdentity(102),
        )
    with pytest.raises(ValueError, match="exactly one"):
        replace(
            effects,
            active_vault_and_index_count_decrease=ActiveVaultCount(2),
        )
    with pytest.raises(ValueError, match="total zUSD burn"):
        replace(
            effects,
            owner_net_debt_burn_atoms=ZUSDAtoms(U256_MAX),
        )


def test_result_constructors_kill_guard_and_lifecycle_shape_mutations() -> None:
    pre = _state()
    accepted = run_owner_close(pre, _request(pre))
    assert type(accepted) is OwnerCloseAccepted
    with pytest.raises(TypeError, match="only be constructed"):
        _reconstruct_accepted(accepted, construction_token=object())
    with pytest.raises(ValueError, match="totalize"):
        _reconstruct_accepted(
            accepted,
            guard_outcomes=accepted.guard_outcomes[:-1],
        )
    malformed_outcomes = cast(
        tuple[GuardOutcome, ...],
        (object(), *accepted.guard_outcomes[1:]),
    )
    with pytest.raises(TypeError, match="Passed, Failed, or Blocked"):
        _reconstruct_accepted(accepted, guard_outcomes=malformed_outcomes)
    wrong_ordinal = cast(
        tuple[GuardOutcome, ...],
        (GuardPassed(1), *accepted.guard_outcomes[1:]),
    )
    with pytest.raises(ValueError, match="ordinal"):
        _reconstruct_accepted(accepted, guard_outcomes=wrong_ordinal)

    recovery_pre = _state(system_collateral_atoms=30 * Q - 1)
    recovery_request = _request(recovery_pre)
    assert type(recovery_request.risk_mode) is RecoveryModeDecision
    with pytest.raises(ValueError, match="deterministic guard evaluation"):
        OwnerCloseAccepted(
            pre_state=recovery_pre,
            request=recovery_request,
            post_state=accepted.post_state,
            effects=accepted.effects,
            guard_outcomes=accepted.guard_outcomes,
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )
    rejected = run_owner_close(recovery_pre, recovery_request)
    assert type(rejected) is OwnerCloseRejected
    wrong_code = list(rejected.guard_outcomes)
    wrong_code[3] = GuardFailed(3, OwnerCloseReject.WRONG_VAULT_OWNER)
    with pytest.raises(ValueError, match="declared ordinal"):
        OwnerCloseRejected(
            pre_state=recovery_pre,
            request=recovery_request,
            guard_outcomes=tuple(wrong_code),
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )
    with pytest.raises(ValueError, match="requires every guard"):
        _reconstruct_accepted(accepted, guard_outcomes=rejected.guard_outcomes)
    with pytest.raises(ValueError, match="requires at least one"):
        OwnerCloseRejected(
            pre_state=pre,
            request=accepted.request,
            guard_outcomes=accepted.guard_outcomes,
            _construction_token=owner_close_module._RESULT_CONSTRUCTION_TOKEN,
        )
    with pytest.raises(TypeError, match="only be constructed"):
        OwnerCloseRejected(
            pre_state=recovery_pre,
            request=recovery_request,
            guard_outcomes=rejected.guard_outcomes,
            _construction_token=object(),
        )

    exhausted_pre = replace(pre, transition_sequence=SequenceNumber(U256_MAX))
    with pytest.raises(ValueError, match="sequence exhaustion"):
        _reconstruct_accepted(accepted, pre_state=exhausted_pre)
    wrong_sequence_post = replace(
        accepted.post_state,
        transition_sequence=SequenceNumber(2),
    )
    with pytest.raises(ValueError, match="advance its sequence once"):
        _reconstruct_accepted(accepted, post_state=wrong_sequence_post)
    active_post = replace(accepted.post_state, lifecycle=pre.lifecycle)
    with pytest.raises(TypeError, match="construct ClosedByOwner"):
        _reconstruct_accepted(accepted, post_state=active_post)
    closed = accepted.post_state.lifecycle
    assert type(closed) is ClosedByOwner
    wrong_close_post = replace(
        accepted.post_state,
        lifecycle=replace(closed, close_occurrence=SequenceNumber(2)),
    )
    with pytest.raises(ValueError, match="closed lifecycle"):
        _reconstruct_accepted(accepted, post_state=wrong_close_post)
    wrong_effect_occurrence = replace(
        accepted.effects,
        close_occurrence=SequenceNumber(2),
    )
    with pytest.raises(ValueError, match="effects must bind"):
        _reconstruct_accepted(accepted, effects=wrong_effect_occurrence)


def test_wrong_target_reserve_identity_and_result_type_fail_closed() -> None:
    pre = _state()
    request = _request(pre)
    wrong_target = replace(request, target_vault_identity=VaultIdentity(102))
    _assert_reject(
        run_owner_close(pre, wrong_target),
        pre,
        OwnerCloseReject.TARGET_VAULT_INACTIVE,
    )
    wrong_reserve_identity = replace(
        pre,
        gas_reserve=replace(
            pre.gas_reserve,
            target_vault_identity=VaultIdentity(102),
        ),
    )
    _assert_reject(
        run_owner_close(wrong_reserve_identity, _request(wrong_reserve_identity)),
        wrong_reserve_identity,
        OwnerCloseReject.RESERVE_CUSTODY_MISMATCH,
    )
    with pytest.raises(TypeError, match="result must be"):
        committed_state(cast(OwnerCloseAccepted, object()))
    with pytest.raises(TypeError, match="pre_state must be"):
        run_owner_close(cast(OwnerCloseState, object()), request)


def test_every_accepted_guard_is_total_and_passed() -> None:
    pre = _state()
    result = run_owner_close(pre, _request(pre))
    assert type(result) is OwnerCloseAccepted
    assert len(result.guard_outcomes) == len(OwnerCloseReject)
    assert all(type(outcome) is GuardPassed for outcome in result.guard_outcomes)


@settings(max_examples=100, derandomize=True, deadline=None)
@given(
    net_debt=st.integers(min_value=1_800, max_value=10_000),
    target_collateral=st.integers(min_value=1, max_value=100),
    other_debt=st.integers(min_value=2_000, max_value=10_000),
    tcr_cushion_collateral=st.integers(min_value=0, max_value=20),
    extra_owner_zusd=st.integers(min_value=0, max_value=1_000),
    owner_collateral=st.integers(min_value=0, max_value=100),
)
def test_generated_acceptance_conserves_every_owned_quantity(
    net_debt: int,
    target_collateral: int,
    other_debt: int,
    tcr_cushion_collateral: int,
    extra_owner_zusd: int,
    owner_collateral: int,
) -> None:
    price = 200
    composite_debt = net_debt + 200
    minimum_candidate_collateral = (3 * other_debt + 399) // 400
    minimum_total_collateral = (
        3 * (composite_debt + other_debt) + 399
    ) // 400
    minimum_other_collateral = max(
        minimum_candidate_collateral,
        minimum_total_collateral - target_collateral,
    )
    other_collateral = minimum_other_collateral + tcr_cushion_collateral
    active = _active(
        collateral_atoms=target_collateral * Q,
        net_debt_atoms=net_debt * Q,
        stake_atoms=target_collateral * Q,
    )
    composite = active.composite_debt_atoms.value
    pre = _state(
        active=active,
        system_collateral_atoms=(target_collateral + other_collateral) * Q,
        system_debt_atoms=composite + other_debt * Q,
        total_stake_atoms=(target_collateral + other_collateral) * Q,
        owner_zusd_atoms=(net_debt + extra_owner_zusd) * Q,
        owner_collateral_atoms=owner_collateral * Q,
        total_supply_atoms=composite + other_debt * Q,
    )
    result = run_owner_close(
        pre,
        _request(pre, price_e18=price * PRICE_SCALE_E18),
    )
    assert type(result) is OwnerCloseAccepted
    post = committed_state(result)
    assert result.effects.total_zusd_burn_atoms.value == composite
    assert post.supply.total_zusd_supply_atoms == post.system.composite_debt_atoms
    assert (
        pre.supply.total_zusd_supply_atoms.value
        - post.supply.total_zusd_supply_atoms.value
        == composite
    )
    assert (
        post.owner_wallet.collateral_balance_atoms.value
        - pre.owner_wallet.collateral_balance_atoms.value
        == target_collateral * Q
    )
    assert (
        pre.system.total_active_stake_atoms.value
        - post.system.total_active_stake_atoms.value
        == target_collateral * Q
    )
    assert post.gas_reserve.gas_pool_custody_atoms.value == 200 * Q
