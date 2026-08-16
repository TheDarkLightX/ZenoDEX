from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_clbf_model_v1 as checker
from tools import production_readiness_g1_clbf_contract_v1 as contract


def _root(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _lot(
    label: str,
    lot_type: contract.LotTypeV1,
    amount_atoms: int,
    *,
    asset_id: str = "USDC",
    parent_lot_id: str | None = None,
) -> contract.SourceLotV1:
    return contract.SourceLotV1(
        lot_id=_root(f"lot:{label}"),
        asset_id=asset_id,
        lot_type=lot_type,
        amount_atoms=amount_atoms,
        parent_lot_id=parent_lot_id,
        source_root=_root(f"source:{label}"),
    )


def _allocation(
    destination: contract.LotDestinationV1,
    amount_atoms: int,
    *,
    successor: contract.SourceLotV1 | None = None,
) -> contract.LotAllocationV1:
    return contract.LotAllocationV1(
        destination=destination,
        amount_atoms=amount_atoms,
        successor_lot_id=successor.lot_id if successor is not None else None,
    )


def _valid_revenue_transition() -> contract.LotTransitionV1:
    revenue = _lot(
        "revenue",
        contract.LotTypeV1.UNRESTRICTED_PROTOCOL_REVENUE,
        100,
    )
    credit = _lot(
        "credit",
        contract.LotTypeV1.CREDIT_RESERVE,
        10,
        parent_lot_id=revenue.lot_id,
    )
    buyback = _lot(
        "buyback",
        contract.LotTypeV1.BUYBACK_CARRY,
        40,
        parent_lot_id=revenue.lot_id,
    )
    spend = contract.LotSpendV1(
        source_lot=revenue,
        allocations=(
            _allocation(contract.LotDestinationV1.P1_SAFETY_RESERVE, 20),
            _allocation(contract.LotDestinationV1.P2_SERVICE_PAYMENT, 20),
            _allocation(contract.LotDestinationV1.P3_OPERATIONS_PAYMENT, 10),
            _allocation(
                contract.LotDestinationV1.G_CREDIT_RESERVE_CREATE,
                10,
                successor=credit,
            ),
            _allocation(
                contract.LotDestinationV1.C_BUYBACK_CARRY,
                40,
                successor=buyback,
            ),
        ),
    )
    return contract.LotTransitionV1(
        transition_id=_root("transition:revenue"),
        spends=(spend,),
        successor_lots=tuple(sorted((credit, buyback), key=lambda lot: lot.lot_id)),
        authorization_root=_root("authorization:revenue"),
    )


def _earn_command() -> contract.EarnCreditV1:
    return contract.EarnCreditV1(
        cash_fee_atoms=100,
        requested_credit_atoms=10,
        earn_bps=1_000,
        available_growth_reserve_atoms=10,
        earned_epoch=1,
        maturity_epoch=31,
        expiry_epoch=181,
        continuous_lock_witness_root=_root("lock:earn"),
    )


def test_artifact_is_exact_and_keeps_clbf_activation_blocked() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["activation_allowed"] is False
    assert report["production_ready"] is False
    assert report["selected_parameter_count"] == 0
    assert document["status"] == "RESEARCH_ONLY_UNSELECTED"
    assert document["production_promotion"] is False


def test_closed_lot_registry_preserves_restricted_funds() -> None:
    registry = contract.allowed_destinations_v1()
    discretionary = {
        contract.LotDestinationV1.P1_SAFETY_RESERVE,
        contract.LotDestinationV1.P2_SERVICE_PAYMENT,
        contract.LotDestinationV1.P3_OPERATIONS_PAYMENT,
        contract.LotDestinationV1.G_CREDIT_RESERVE_CREATE,
        contract.LotDestinationV1.X_BUYBACK_EXECUTION,
    }
    protected = {
        contract.LotTypeV1.THIRD_PARTY_PROPERTY,
        contract.LotTypeV1.REFUNDABLE_SERVICE_BOND,
        contract.LotTypeV1.BACKSTOP_RISK_PRINCIPAL,
        contract.LotTypeV1.MARKET_MAKER_LIQUIDITY,
    }

    assert set(registry) == set(contract.LotTypeV1)
    for lot_type in protected:
        assert registry[lot_type].isdisjoint(discretionary)


def test_valid_revenue_transition_conserves_and_binds_successors() -> None:
    transition = _valid_revenue_transition()

    outcome = contract.validate_lot_transition_v1(transition, frozenset())

    assert isinstance(outcome, contract.LotAcceptV1)
    assert outcome.consumed_lot_ids_after == frozenset(
        {transition.spends[0].source_lot.lot_id}
    )
    assert sum(
        allocation.amount_atoms
        for allocation in transition.spends[0].allocations
    ) == transition.spends[0].source_lot.amount_atoms


@pytest.mark.parametrize(
    ("lot_type", "forbidden_destination"),
    (
        (
            contract.LotTypeV1.SERVICE_PREFUND,
            contract.LotDestinationV1.X_BUYBACK_EXECUTION,
        ),
        (
            contract.LotTypeV1.REFUNDABLE_SERVICE_BOND,
            contract.LotDestinationV1.X_BUYBACK_EXECUTION,
        ),
        (
            contract.LotTypeV1.CREDIT_RESERVE,
            contract.LotDestinationV1.G_CREDIT_RESERVE_CREATE,
        ),
        (
            contract.LotTypeV1.GENESIS_LOT,
            contract.LotDestinationV1.P3_OPERATIONS_PAYMENT,
        ),
    ),
)
def test_restricted_lot_cannot_be_swept_to_forbidden_destination(
    lot_type: contract.LotTypeV1,
    forbidden_destination: contract.LotDestinationV1,
) -> None:
    source = _lot("restricted", lot_type, 10)
    transition = contract.LotTransitionV1(
        transition_id=_root("transition:restricted"),
        spends=(
            contract.LotSpendV1(
                source_lot=source,
                allocations=(_allocation(forbidden_destination, 10),),
            ),
        ),
        successor_lots=(),
        authorization_root=_root("authorization:restricted"),
    )

    outcome = contract.validate_lot_transition_v1(transition, frozenset())

    assert isinstance(outcome, contract.LotRejectV1)
    assert outcome.code is contract.LotRejectCodeV1.DESTINATION_NOT_ALLOWED


def test_overallocated_lot_rejects_without_consuming_input() -> None:
    transition = _valid_revenue_transition()
    spend = transition.spends[0]
    malformed = contract.LotTransitionV1(
        transition_id=transition.transition_id,
        spends=(
            contract.LotSpendV1(
                source_lot=spend.source_lot,
                allocations=spend.allocations
                + (_allocation(contract.LotDestinationV1.X_BUYBACK_EXECUTION, 1),),
            ),
        ),
        successor_lots=transition.successor_lots,
        authorization_root=transition.authorization_root,
    )

    outcome = contract.validate_lot_transition_v1(malformed, frozenset())

    assert isinstance(outcome, contract.LotRejectV1)
    assert outcome.code is contract.LotRejectCodeV1.ALLOCATION_SUM_MISMATCH
    assert outcome.consumed_lot_ids_after == frozenset()


def test_wrong_successor_type_rejects() -> None:
    transition = _valid_revenue_transition()
    original = transition.successor_lots[0]
    malformed_successor = contract.SourceLotV1(
        lot_id=original.lot_id,
        asset_id=original.asset_id,
        lot_type=contract.LotTypeV1.GENESIS_LOT,
        amount_atoms=original.amount_atoms,
        parent_lot_id=original.parent_lot_id,
        source_root=original.source_root,
    )
    malformed = contract.LotTransitionV1(
        transition_id=transition.transition_id,
        spends=transition.spends,
        successor_lots=tuple(
            malformed_successor if lot.lot_id == original.lot_id else lot
            for lot in transition.successor_lots
        ),
        authorization_root=transition.authorization_root,
    )

    outcome = contract.validate_lot_transition_v1(malformed, frozenset())

    assert isinstance(outcome, contract.LotRejectV1)
    assert outcome.code is contract.LotRejectCodeV1.SUCCESSOR_TYPE_MISMATCH


def test_orphan_successor_rejects() -> None:
    transition = _valid_revenue_transition()
    orphan = _lot("orphan", contract.LotTypeV1.BUYBACK_CARRY, 1)
    malformed = contract.LotTransitionV1(
        transition_id=transition.transition_id,
        spends=transition.spends,
        successor_lots=tuple(
            sorted(transition.successor_lots + (orphan,), key=lambda lot: lot.lot_id)
        ),
        authorization_root=transition.authorization_root,
    )

    outcome = contract.validate_lot_transition_v1(malformed, frozenset())

    assert isinstance(outcome, contract.LotRejectV1)
    assert outcome.code is contract.LotRejectCodeV1.ORPHAN_SUCCESSOR


def test_replay_of_consumed_lot_rejects_no_op() -> None:
    transition = _valid_revenue_transition()
    first = contract.validate_lot_transition_v1(transition, frozenset())
    assert isinstance(first, contract.LotAcceptV1)

    replay = contract.validate_lot_transition_v1(
        transition,
        first.consumed_lot_ids_after,
    )

    assert isinstance(replay, contract.LotRejectV1)
    assert replay.code is contract.LotRejectCodeV1.LOT_ALREADY_CONSUMED
    assert replay.consumed_lot_ids_after == first.consumed_lot_ids_after


def test_noncanonical_allocation_order_rejects() -> None:
    transition = _valid_revenue_transition()
    spend = transition.spends[0]
    malformed = contract.LotTransitionV1(
        transition_id=transition.transition_id,
        spends=(
            contract.LotSpendV1(
                source_lot=spend.source_lot,
                allocations=tuple(reversed(spend.allocations)),
            ),
        ),
        successor_lots=transition.successor_lots,
        authorization_root=transition.authorization_root,
    )

    outcome = contract.validate_lot_transition_v1(malformed, frozenset())

    assert isinstance(outcome, contract.LotRejectV1)
    assert outcome.code is contract.LotRejectCodeV1.NONCANONICAL_ALLOCATION_ORDER


def test_waterfall_funds_services_before_growth_and_buyback() -> None:
    candidate = contract.RevenueWaterfallV1(
        asset_id="USDC",
        finalized_unrestricted_revenue_atoms=100,
        p1_safety_shortfall_atoms=20,
        p2_service_shortfall_atoms=20,
        p3_operations_shortfall_atoms=10,
        requested_growth_reserve_atoms=10,
        selected_growth_reserve_bps=2_000,
        requested_buyback_atoms=40,
        requested_buyback_carry_atoms=0,
        obligation_snapshot_root=_root("obligations:funded"),
        revenue_source_root=_root("revenue:funded"),
    )

    outcome = contract.validate_revenue_waterfall_v1(candidate)

    assert isinstance(outcome, contract.RevenueWaterfallAcceptV1)
    assert outcome.allocation.p2_service_atoms == 20
    assert outcome.allocation.pre_growth_surplus_atoms == 50
    assert outcome.allocation.eligible_surplus_atoms == 40
    assert outcome.allocation.buyback_atoms == 40


def test_underfunded_required_services_cannot_create_surplus() -> None:
    candidate = contract.RevenueWaterfallV1(
        asset_id="USDC",
        finalized_unrestricted_revenue_atoms=100,
        p1_safety_shortfall_atoms=30,
        p2_service_shortfall_atoms=80,
        p3_operations_shortfall_atoms=0,
        requested_growth_reserve_atoms=0,
        selected_growth_reserve_bps=0,
        requested_buyback_atoms=0,
        requested_buyback_carry_atoms=0,
        obligation_snapshot_root=_root("obligations:underfunded"),
        revenue_source_root=_root("revenue:underfunded"),
    )

    outcome = contract.validate_revenue_waterfall_v1(candidate)

    assert isinstance(outcome, contract.RevenueWaterfallRejectV1)
    assert (
        outcome.code
        is contract.RevenueWaterfallRejectCodeV1.REQUIRED_FUNDING_EXCEEDS_REVENUE
    )


def test_waterfall_cannot_hide_unallocated_surplus() -> None:
    candidate = contract.RevenueWaterfallV1(
        asset_id="USDC",
        finalized_unrestricted_revenue_atoms=100,
        p1_safety_shortfall_atoms=20,
        p2_service_shortfall_atoms=20,
        p3_operations_shortfall_atoms=10,
        requested_growth_reserve_atoms=10,
        selected_growth_reserve_bps=2_000,
        requested_buyback_atoms=39,
        requested_buyback_carry_atoms=0,
        obligation_snapshot_root=_root("obligations:remainder"),
        revenue_source_root=_root("revenue:remainder"),
    )

    outcome = contract.validate_revenue_waterfall_v1(candidate)

    assert isinstance(outcome, contract.RevenueWaterfallRejectV1)
    assert (
        outcome.code
        is contract.RevenueWaterfallRejectCodeV1.SURPLUS_ALLOCATION_MISMATCH
    )


def test_credit_lifecycle_preserves_reserve_and_external_revenue_tags() -> None:
    state = contract.empty_credit_state_v1("USDC")
    earned = contract.run_credit_transition_v1(state, _earn_command())
    assert isinstance(earned, contract.CreditAcceptV1)
    assert earned.state.reserve_atoms == 10
    assert earned.state.pending_credit_atoms == 10
    assert earned.effect.external_cash_fee_atoms == 100

    matured = contract.run_credit_transition_v1(
        earned.state,
        contract.MatureCreditV1(
            current_epoch=31,
            continuous_lock_witness_root=_root("lock:mature"),
        ),
    )
    assert isinstance(matured, contract.CreditAcceptV1)
    assert matured.state.matured_credit_atoms == 10

    redeemed = contract.run_credit_transition_v1(
        matured.state,
        contract.RedeemCreditV1(
            gross_fee_atoms=40,
            requested_credit_atoms=5,
            redemption_bps=2_500,
            current_epoch=32,
        ),
    )
    assert isinstance(redeemed, contract.CreditAcceptV1)
    assert redeemed.state.reserve_atoms == 5
    assert redeemed.state.matured_credit_atoms == 5
    assert redeemed.effect.external_cash_fee_atoms == 35
    assert redeemed.effect.reserve_release_atoms == 5
    assert redeemed.effect.fee_settlement_atoms == 40
    assert redeemed.effect.new_credit_atoms == 0

    expired = contract.run_credit_transition_v1(
        redeemed.state,
        contract.ExpireCreditV1(current_epoch=181),
    )
    assert isinstance(expired, contract.CreditAcceptV1)
    assert expired.state.reserve_atoms == 0
    assert expired.state.buyback_carry_atoms == 5
    assert expired.state.status is contract.CreditStatusV1.EXPIRED


def test_early_unlock_cancels_pending_credit_into_buyback_carry() -> None:
    state = contract.empty_credit_state_v1("USDC")
    earned = contract.run_credit_transition_v1(state, _earn_command())
    assert isinstance(earned, contract.CreditAcceptV1)

    canceled = contract.run_credit_transition_v1(
        earned.state,
        contract.EarlyUnlockCreditV1(current_epoch=10),
    )

    assert isinstance(canceled, contract.CreditAcceptV1)
    assert canceled.state.pending_credit_atoms == 0
    assert canceled.state.reserve_atoms == 0
    assert canceled.state.buyback_carry_atoms == 10
    assert canceled.state.status is contract.CreditStatusV1.CANCELED


def test_credit_rate_at_or_above_full_fee_rejects_no_op() -> None:
    state = contract.empty_credit_state_v1("USDC")
    command = contract.EarnCreditV1(
        cash_fee_atoms=100,
        requested_credit_atoms=100,
        earn_bps=10_000,
        available_growth_reserve_atoms=100,
        earned_epoch=1,
        maturity_epoch=31,
        expiry_epoch=181,
        continuous_lock_witness_root=_root("lock:unsafe"),
    )

    outcome = contract.run_credit_transition_v1(state, command)

    assert isinstance(outcome, contract.CreditRejectV1)
    assert outcome.code is contract.CreditRejectCodeV1.EARN_BPS_OUT_OF_RANGE
    assert outcome.state == state


def test_credit_amount_above_consensus_bound_rejects_no_op() -> None:
    state = contract.empty_credit_state_v1("USDC")
    command = contract.EarnCreditV1(
        cash_fee_atoms=contract.MAX_ATOMS + 1,
        requested_credit_atoms=1,
        earn_bps=1,
        available_growth_reserve_atoms=1,
        earned_epoch=1,
        maturity_epoch=31,
        expiry_epoch=181,
        continuous_lock_witness_root=_root("lock:overflow"),
    )

    outcome = contract.run_credit_transition_v1(state, command)

    assert isinstance(outcome, contract.CreditRejectV1)
    assert outcome.code is contract.CreditRejectCodeV1.INVALID_AMOUNT
    assert outcome.state == state


def test_redemption_above_fee_cap_rejects_no_op() -> None:
    state = contract.empty_credit_state_v1("USDC")
    earned = contract.run_credit_transition_v1(state, _earn_command())
    assert isinstance(earned, contract.CreditAcceptV1)
    matured = contract.run_credit_transition_v1(
        earned.state,
        contract.MatureCreditV1(
            current_epoch=31,
            continuous_lock_witness_root=_root("lock:mature"),
        ),
    )
    assert isinstance(matured, contract.CreditAcceptV1)

    outcome = contract.run_credit_transition_v1(
        matured.state,
        contract.RedeemCreditV1(
            gross_fee_atoms=4,
            requested_credit_atoms=2,
            redemption_bps=2_500,
            current_epoch=32,
        ),
    )

    assert isinstance(outcome, contract.CreditRejectV1)
    assert outcome.code is contract.CreditRejectCodeV1.REDEMPTION_CAP_EXCEEDED
    assert outcome.state == matured.state


def test_bounded_oracle_finds_no_direct_incentive_counterexample() -> None:
    evidence = checker.bounded_attack_evidence()

    assert evidence["credit_direct_profit_search"]["counterexample"] is None
    assert evidence["event_cap_profit_search"]["counterexample"] is None
    assert evidence["sybil_split_search"]["counterexample"] is None
    assert all(
        witness["profit_atoms"] > 0
        for witness in evidence["named_mutant_witnesses"]
    )


def test_independent_integer_oracle_confirms_credit_and_event_bounds() -> None:
    for fee_atoms in range(33):
        for bps in range(10_000):
            credit_atoms = fee_atoms * bps // 10_000
            event_benefit_atoms = fee_atoms * bps // 10_000
            assert credit_atoms - fee_atoms <= 0
            assert event_benefit_atoms - fee_atoms <= 0


def test_independent_sybil_oracle_confirms_floor_subadditivity() -> None:
    for first_fee_atoms in range(17):
        for second_fee_atoms in range(17):
            for bps in (0, 1, 500, 1_500, 9_999):
                split = (
                    first_fee_atoms * bps // 10_000
                    + second_fee_atoms * bps // 10_000
                )
                combined = (first_fee_atoms + second_fee_atoms) * bps // 10_000
                assert split <= combined


def test_artifact_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["activation_gate"]["activation_allowed"] = True
    candidate = tmp_path / "activated.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["activation_allowed"] is False


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text(
        '{"schema":"first","schema":"second"}\n',
        encoding="utf-8",
    )

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_selected_parameter_mutation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        contract,
        "SELECTED_CLBF_PARAMETERS",
        {**contract.SELECTED_CLBF_PARAMETERS, "earn_bps": 500},
    )

    with pytest.raises(ValueError, match="parameters must remain unselected"):
        checker.build_document()


def test_frozen_research_source_byte_drift_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real_git_bytes = checker._git_bytes

    def altered_git_bytes(repo_root: Path, *args: str) -> bytes:
        observed = real_git_bytes(repo_root, *args)
        if args and args[0] == "show":
            return observed + b"tampered"
        return observed

    monkeypatch.setattr(checker, "_git_bytes", altered_git_bytes)

    with pytest.raises(ValueError, match="research source drift"):
        checker.build_document()
