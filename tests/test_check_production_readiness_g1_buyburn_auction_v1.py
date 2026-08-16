from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_buyburn_auction_v1 as checker
from tools import production_readiness_g1_buyburn_auction_contract_v1 as contract


def _root(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _policy() -> contract.BurnAuctionPolicyV1:
    return contract.BurnAuctionPolicyV1(
        protocol_asset_id="ZDEX",
        quote_asset_id="USDC",
        supply_ceiling_atoms=1_000,
        active_floor_atoms=200,
        absolute_floor_atoms=1,
        reserve_value_bps=9_000,
        maximum_epoch_burn_bps=5_000,
        maximum_epoch_burn_atoms=100,
        minimum_source_lag_epochs=2,
        minimum_reference_lag_epochs=2,
        maximum_reference_age_epochs=10,
        minimum_independent_reference_sources=2,
        maximum_revealed_bids=16,
        minimum_burn_interval_epochs=1,
        profile_root=_root("profile"),
        valuation_profile_root=_root("valuation-profile"),
        admission_profile_root=_root("admission-profile"),
        burn_authority_id="zenodex-genesis-burn-kernel-v2",
    )


def _state() -> contract.BurnAuctionStateV1:
    return contract.BurnAuctionStateV1(
        supply_atoms=1_000,
        cumulative_burn_atoms=0,
        active_floor_atoms=200,
        absolute_floor_atoms=1,
        last_burn_epoch=10,
        writer_epoch=3,
        active_profile_root=_root("profile"),
        consumed_lot_ids=frozenset(),
        settled_auction_ids=frozenset(),
    )


def _lot() -> contract.BurnAuctionLotV1:
    return contract.BurnAuctionLotV1(
        lot_id=_root("lot"),
        lot_type=contract.BurnAuctionLotTypeV1.UNRESTRICTED_PROTOCOL_REVENUE,
        asset_id="USDC",
        amount_atoms=1_000,
        source_epoch=10,
        source_root=_root("lot-source"),
    )


def _auction() -> contract.BurnAuctionV1:
    return contract.BurnAuctionV1(
        auction_id=_root("auction"),
        lot=_lot(),
        current_epoch=20,
        commit_close_epoch=16,
        reveal_close_epoch=18,
        settlement_deadline_epoch=22,
        expected_writer_epoch=3,
        profile_root=_root("profile"),
        admission_profile_root=_root("admission-profile"),
        complete_reveal_set_root=_root("placeholder-reveal-set"),
        admitted_reveal_count=2,
    )


def _valuation() -> contract.BurnAuctionValuationV1:
    return contract.BurnAuctionValuationV1(
        lot_id=_root("lot"),
        quote_asset_id="USDC",
        certified_lot_value_quote_atoms=1_000,
        reference_quote_atoms=10,
        reference_zdex_atoms=1,
        occurrence_epoch=15,
        independent_reference_source_count=3,
        occurrence_root=_root("valuation-occurrence"),
        valuation_profile_root=_root("valuation-profile"),
    )


def _bid(
    label: str,
    burn_atoms: int,
    *,
    bidder_id: str | None = None,
    auction: contract.BurnAuctionV1 | None = None,
) -> contract.RevealedBurnBidV1:
    selected_auction = auction or _auction()
    bidder = bidder_id or f"bidder-{label}"
    recipient = f"recipient-{label}"
    salt_root = _root(f"salt:{label}")
    commitment_id = contract.burn_bid_commitment_v1(
        auction_id=selected_auction.auction_id,
        lot_id=selected_auction.lot.lot_id,
        profile_root=selected_auction.profile_root,
        bidder_capability_id=bidder,
        recipient_id=recipient,
        burn_bid_atoms=burn_atoms,
        salt_root=salt_root,
    )
    return contract.RevealedBurnBidV1(
        commitment_id=commitment_id,
        auction_id=selected_auction.auction_id,
        lot_id=selected_auction.lot.lot_id,
        profile_root=selected_auction.profile_root,
        bidder_capability_id=bidder,
        recipient_id=recipient,
        burn_bid_atoms=burn_atoms,
        escrowed_zdex_atoms=burn_atoms,
        reveal_epoch=17,
        salt_root=salt_root,
        admission_witness_root=_root(f"admission:{label}"),
    )


def _bids(*items: contract.RevealedBurnBidV1) -> tuple[contract.RevealedBurnBidV1, ...]:
    return tuple(sorted(items, key=lambda bid: bid.commitment_id))


def _replace_burn_bid(
    bid: contract.RevealedBurnBidV1,
    burn_atoms: int,
) -> contract.RevealedBurnBidV1:
    commitment_id = contract.burn_bid_commitment_v1(
        auction_id=bid.auction_id,
        lot_id=bid.lot_id,
        profile_root=bid.profile_root,
        bidder_capability_id=bid.bidder_capability_id,
        recipient_id=bid.recipient_id,
        burn_bid_atoms=burn_atoms,
        salt_root=bid.salt_root,
    )
    return replace(
        bid,
        commitment_id=commitment_id,
        burn_bid_atoms=burn_atoms,
        escrowed_zdex_atoms=burn_atoms,
    )


def _settle(
    *,
    policy: contract.BurnAuctionPolicyV1 | None = None,
    state: contract.BurnAuctionStateV1 | None = None,
    auction: contract.BurnAuctionV1 | None = None,
    valuation: contract.BurnAuctionValuationV1 | None = None,
    bids: tuple[contract.RevealedBurnBidV1, ...] | None = None,
) -> contract.BurnAuctionOutcomeV1:
    selected_auction = auction or _auction()
    selected_bids = bids if bids is not None else _bids(_bid("low", 95), _bid("high", 100))
    if selected_auction.complete_reveal_set_root == _root("placeholder-reveal-set"):
        selected_auction = replace(
            selected_auction,
            complete_reveal_set_root=contract.complete_reveal_set_root_v1(
                auction_id=selected_auction.auction_id,
                admission_profile_root=selected_auction.admission_profile_root,
                bids=selected_bids,
            ),
        )
    return contract.assess_burn_auction_settlement_v1(
        policy or _policy(),
        state or _state(),
        selected_auction,
        valuation or _valuation(),
        selected_bids,
    )


def test_selected_2b_e18_supply_constants_are_exact_atoms() -> None:
    assert contract.ZDEX_WHOLE_TOKEN_SUPPLY == 2_000_000_000
    assert contract.ZDEX_UNIT_SCALE == 10**18
    assert contract.ZDEX_GENESIS_SUPPLY_ATOMS == 2_000_000_000 * 10**18
    assert contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS == 200_000_000 * 10**18
    assert contract.ZDEX_ABSOLUTE_FLOOR_ATOMS == 1


@pytest.mark.parametrize(
    ("supply_atoms", "floor_atoms", "expected_cap"),
    ((200, 200, 0), (201, 200, 0), (202, 200, 1), (203, 200, 1), (204, 200, 2)),
)
def test_zeno_cap_never_reaches_the_active_floor(
    supply_atoms: int,
    floor_atoms: int,
    expected_cap: int,
) -> None:
    cap = contract.zeno_burn_cap_v1(supply_atoms, floor_atoms)

    assert cap == expected_cap
    if cap > 0:
        assert supply_atoms - cap > floor_atoms


def test_highest_fully_escrowed_bid_burns_and_receives_exact_lot() -> None:
    outcome = _settle()

    assert isinstance(outcome, contract.BurnAuctionSettlementCandidateV1)
    assert outcome.winner.burn_bid_atoms == 100
    assert outcome.candidate_state_after.supply_atoms == 900
    assert outcome.effect_plan.burned_zdex_atoms == 100
    assert outcome.effect_plan.transferred_lot_atoms == 1_000
    assert outcome.effect_plan.protocol_acquired_zdex_atoms == 0
    assert tuple(disposition.kind for disposition in outcome.effect_plan.escrow_dispositions) == (
        contract.BurnEscrowDispositionKindV1.RETURN,
        contract.BurnEscrowDispositionKindV1.BURN,
    )
    assert (
        sum(
            disposition.amount_atoms
            for disposition in outcome.effect_plan.escrow_dispositions
            if disposition.kind is contract.BurnEscrowDispositionKindV1.RETURN
        )
        == 95
    )
    assert outcome.settlement_authorized is False


def test_tied_burn_bid_uses_canonical_commitment_id() -> None:
    left = _bid("left", 100)
    right = _bid("right", 100)
    outcome = _settle(bids=_bids(left, right))

    assert isinstance(outcome, contract.BurnAuctionSettlementCandidateV1)
    assert outcome.winner.commitment_id == min(
        left.commitment_id,
        right.commitment_id,
    )


def test_below_reserve_bid_preserves_lot_as_carry_without_effect() -> None:
    auction = replace(_auction(), admitted_reveal_count=1)
    outcome = _settle(auction=auction, bids=_bids(_bid("low", 89, auction=auction)))

    assert isinstance(outcome, contract.BurnAuctionCarryCandidateV1)
    assert outcome.reason is contract.BurnAuctionCarryReasonV1.RESERVE_NOT_MET
    assert outcome.candidate_state_after == replace(
        _state(),
        settled_auction_ids=frozenset({auction.auction_id}),
    )
    assert outcome.effect_plan.carried_lot_id == auction.lot.lot_id
    assert outcome.effect_plan.escrow_returns == (
        contract.BurnEscrowDispositionV1(
            commitment_id=_bid("low", 89, auction=auction).commitment_id,
            bidder_capability_id="bidder-low",
            amount_atoms=89,
            kind=contract.BurnEscrowDispositionKindV1.RETURN,
        ),
    )
    assert outcome.effect_plan.external_outbox_effect_count == 0


def test_no_reveals_finalize_only_the_auction_and_carry_the_lot() -> None:
    auction = replace(_auction(), admitted_reveal_count=0)

    outcome = _settle(auction=auction, bids=())

    assert isinstance(outcome, contract.BurnAuctionCarryCandidateV1)
    assert outcome.reason is contract.BurnAuctionCarryReasonV1.NO_REVEALED_BIDS
    assert outcome.candidate_state_after.settled_auction_ids == frozenset({auction.auction_id})
    assert outcome.candidate_state_after.consumed_lot_ids == frozenset()
    assert outcome.effect_plan.escrow_returns == ()


@pytest.mark.parametrize(
    ("mutate_bid", "expected_code"),
    (
        (
            lambda bid: replace(bid, escrowed_zdex_atoms=bid.burn_bid_atoms - 1),
            contract.BurnAuctionRejectCodeV1.BID_NOT_FULLY_ESCROWED,
        ),
        (
            lambda bid: replace(bid, commitment_id=_root("forged")),
            contract.BurnAuctionRejectCodeV1.COMMITMENT_MISMATCH,
        ),
        (
            lambda bid: _replace_burn_bid(bid, 101),
            contract.BurnAuctionRejectCodeV1.BURN_CAP_EXCEEDED,
        ),
    ),
)
def test_invalid_bid_rejects_exact_no_op(
    mutate_bid: object,
    expected_code: contract.BurnAuctionRejectCodeV1,
) -> None:
    auction = replace(_auction(), admitted_reveal_count=1)
    original = _bid("one", 100, auction=auction)
    mutated = mutate_bid(original)  # type: ignore[operator]

    outcome = _settle(auction=auction, bids=_bids(mutated))

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is expected_code
    assert outcome.state_after == _state()
    assert outcome.effect_plan == ()


def test_duplicate_bidder_capability_rejects_duplicate_reveal() -> None:
    left = _bid("left", 95, bidder_id="same-bidder")
    right = _bid("right", 100, bidder_id="same-bidder")

    outcome = _settle(bids=_bids(left, right))

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.DUPLICATE_BIDDER


def test_reveal_set_root_and_admission_profile_are_exactly_bound() -> None:
    root_mismatch = _settle(
        auction=replace(
            _auction(),
            complete_reveal_set_root=_root("forged-reveal-set"),
        )
    )
    profile_mismatch = _settle(
        auction=replace(
            _auction(),
            admission_profile_root=_root("wrong-admission-profile"),
        )
    )

    assert isinstance(root_mismatch, contract.BurnAuctionRejectV1)
    assert root_mismatch.code is contract.BurnAuctionRejectCodeV1.REVEAL_SET_ROOT_MISMATCH
    assert isinstance(profile_mismatch, contract.BurnAuctionRejectV1)
    assert profile_mismatch.code is contract.BurnAuctionRejectCodeV1.POLICY_BINDING_MISMATCH


def test_supply_and_cumulative_burn_must_reconcile_to_ceiling() -> None:
    outcome = _settle(state=replace(_state(), cumulative_burn_atoms=1))

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.STATE_INVALID
    assert outcome.state_after == replace(_state(), cumulative_burn_atoms=1)
    assert outcome.effect_plan == ()


def test_protocol_asset_cannot_be_auction_quote_asset() -> None:
    policy = replace(_policy(), quote_asset_id="ZDEX")
    lot = replace(_lot(), asset_id="ZDEX")
    auction = replace(_auction(), lot=lot)
    valuation = replace(_valuation(), quote_asset_id="ZDEX")

    outcome = _settle(policy=policy, auction=auction, valuation=valuation)

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.POLICY_INVALID


def test_noncanonical_reveal_order_rejects() -> None:
    ordered = _bids(_bid("left", 95), _bid("right", 100))

    outcome = _settle(bids=tuple(reversed(ordered)))

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.NONCANONICAL_BID_ORDER


@pytest.mark.parametrize(
    ("auction", "valuation", "expected_code"),
    (
        (
            replace(_auction(), lot=replace(_lot(), source_epoch=19)),
            _valuation(),
            contract.BurnAuctionRejectCodeV1.SOURCE_LOT_TOO_RECENT,
        ),
        (
            _auction(),
            replace(_valuation(), occurrence_epoch=19),
            contract.BurnAuctionRejectCodeV1.REFERENCE_TOO_RECENT,
        ),
        (
            _auction(),
            replace(_valuation(), occurrence_epoch=17),
            contract.BurnAuctionRejectCodeV1.REFERENCE_TOO_RECENT,
        ),
        (
            _auction(),
            replace(_valuation(), occurrence_epoch=9),
            contract.BurnAuctionRejectCodeV1.REFERENCE_STALE,
        ),
        (
            replace(_auction(), lot=replace(_lot(), source_epoch=17)),
            _valuation(),
            contract.BurnAuctionRejectCodeV1.SOURCE_LOT_TOO_RECENT,
        ),
        (
            _auction(),
            replace(_valuation(), independent_reference_source_count=1),
            contract.BurnAuctionRejectCodeV1.REFERENCE_DIVERSITY_INSUFFICIENT,
        ),
    ),
)
def test_source_and_reference_timing_fail_closed(
    auction: contract.BurnAuctionV1,
    valuation: contract.BurnAuctionValuationV1,
    expected_code: contract.BurnAuctionRejectCodeV1,
) -> None:
    auction = replace(auction, admitted_reveal_count=0)
    outcome = _settle(auction=auction, valuation=valuation, bids=())

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is expected_code
    assert outcome.state_after == _state()


def test_replay_of_lot_or_auction_rejects() -> None:
    state = replace(
        _state(),
        consumed_lot_ids=frozenset({_lot().lot_id}),
        settled_auction_ids=frozenset({_auction().auction_id}),
    )

    outcome = _settle(state=state)

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.AUCTION_ALREADY_SETTLED


def test_restricted_service_prefund_cannot_be_auctioned() -> None:
    malformed_lot = replace(
        _lot(),
        lot_type="SERVICE_PREFUND",  # type: ignore[arg-type]
    )
    auction = replace(_auction(), lot=malformed_lot, admitted_reveal_count=0)

    outcome = _settle(auction=auction, bids=())

    assert isinstance(outcome, contract.BurnAuctionRejectV1)
    assert outcome.code is contract.BurnAuctionRejectCodeV1.LOT_TYPE_NOT_ALLOWED


def test_floor_descent_requires_new_release_and_limits_each_step() -> None:
    current = contract.FloorProfileV1(
        profile_root=_root("floor-current"),
        predecessor_profile_root=None,
        activation_epoch=10,
        active_floor_atoms=200,
        absolute_floor_atoms=1,
        unit_scale=10**18,
    )
    next_profile = contract.FloorProfileV1(
        profile_root=_root("floor-next"),
        predecessor_profile_root=current.profile_root,
        activation_epoch=30,
        active_floor_atoms=100,
        absolute_floor_atoms=1,
        unit_scale=10**18,
    )
    policy = contract.FloorDescentPolicyV1(
        minimum_activation_delay_epochs=10,
        maximum_reduction_bps=5_000,
    )

    accepted = contract.assess_floor_descent_v1(
        current,
        next_profile,
        policy,
        current_epoch=20,
        release_root=_root("floor-release"),
    )
    too_deep = contract.assess_floor_descent_v1(
        current,
        replace(next_profile, active_floor_atoms=99),
        policy,
        current_epoch=20,
        release_root=_root("floor-release"),
    )

    assert isinstance(accepted, contract.FloorDescentCandidateV1)
    assert accepted.activation_authorized is False
    assert isinstance(too_deep, contract.FloorDescentRejectV1)
    assert too_deep.code is contract.FloorDescentRejectCodeV1.REDUCTION_TOO_DEEP


@pytest.mark.parametrize(
    ("current", "policy", "current_epoch", "expected_code"),
    (
        (
            contract.FloorProfileV1(
                profile_root=_root("floor-current"),
                predecessor_profile_root=None,
                activation_epoch=10,
                active_floor_atoms=200,
                absolute_floor_atoms=1,
                unit_scale=10**8,
            ),
            contract.FloorDescentPolicyV1(10, 5_000),
            20,
            contract.FloorDescentRejectCodeV1.UNIT_SCALE_CHANGED,
        ),
        (
            contract.FloorProfileV1(
                profile_root=_root("floor-current"),
                predecessor_profile_root=None,
                activation_epoch=10,
                active_floor_atoms=200,
                absolute_floor_atoms=1,
                unit_scale=10**18,
            ),
            contract.FloorDescentPolicyV1(0, 5_000),
            20,
            contract.FloorDescentRejectCodeV1.POLICY_INVALID,
        ),
        (
            contract.FloorProfileV1(
                profile_root=_root("floor-current"),
                predecessor_profile_root=None,
                activation_epoch=30,
                active_floor_atoms=200,
                absolute_floor_atoms=1,
                unit_scale=10**18,
            ),
            contract.FloorDescentPolicyV1(10, 5_000),
            20,
            contract.FloorDescentRejectCodeV1.PROFILE_BINDING_MISMATCH,
        ),
    ),
)
def test_floor_descent_requires_selected_scale_delay_and_active_predecessor(
    current: contract.FloorProfileV1,
    policy: contract.FloorDescentPolicyV1,
    current_epoch: int,
    expected_code: contract.FloorDescentRejectCodeV1,
) -> None:
    successor = contract.FloorProfileV1(
        profile_root=_root("floor-next"),
        predecessor_profile_root=current.profile_root,
        activation_epoch=40,
        active_floor_atoms=100,
        absolute_floor_atoms=current.absolute_floor_atoms,
        unit_scale=current.unit_scale,
    )

    outcome = contract.assess_floor_descent_v1(
        current,
        successor,
        policy,
        current_epoch=current_epoch,
        release_root=_root("floor-release"),
    )

    assert isinstance(outcome, contract.FloorDescentRejectV1)
    assert outcome.code is expected_code


def test_bounded_evidence_closes_only_declared_integer_domains() -> None:
    evidence = checker.bounded_buyburn_evidence()

    assert evidence["zeno_nonarrival_search"]["counterexample"] is None
    assert evidence["maximal_recurrence_search"]["counterexample"] is None
    assert evidence["reserve_cross_product_search"]["counterexample"] is None
    assert {row["id"] for row in evidence["named_mutant_witnesses"]} == {
        "CEIL_HALF_REACHES_ACTIVE_FLOOR",
        "NO_ZENO_CAP_CROSSES_FLOOR",
        "PARTIAL_ESCROW_WINNER_DEFAULT",
        "MISSING_LOSER_ESCROW_RETURN",
        "OMITTED_REVEAL_BEATS_CANONICAL_WINNER",
        "STALE_OR_SELF_REFERENTIAL_PRICE",
        "POST_COMMIT_LOT_OR_VALUATION",
        "UNRECONCILED_SUPPLY_STATE",
        "SERVICE_PREFUND_SWEPT_TO_AUCTION",
        "ZDEX_AS_ITS_OWN_SURPLUS_LOT",
        "TREASURY_MARKET_ORDER_FRONT_RUN",
        "DECIMALS_CREATE_MORE_ATOMS",
    }
    assert evidence["supply_reconciliation_search"]["counterexample"] is None


def test_artifact_is_exact_and_keeps_route_unselected() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["selected_route_count"] == 0
    assert report["activation_allowed"] is False
    assert report["settlement_allowed"] is False
    assert report["production_ready"] is False
    assert document["status"] == "RESEARCH_ONLY_UNSELECTED"


def test_artifact_tampering_and_duplicate_json_fail_closed(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["activation_gate"]["settlement_allowed"] = True
    tampered = tmp_path / "tampered.json"
    tampered.write_bytes(checker._encoded(artifact))
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    assert checker.check_artifact(tampered)["ok"] is False
    duplicate_report = checker.check_artifact(duplicate)
    assert duplicate_report["ok"] is False
    assert any("duplicate JSON keys" in error for error in duplicate_report["errors"])


def test_selected_route_mutation_fails_generation(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        contract,
        "SELECTED_BUYBURN_ROUTE_V1",
        {"route": "COMPETITIVE_BURN_TO_CLAIM_AUCTION"},
    )

    with pytest.raises(ValueError, match="buyburn route must remain unselected"):
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

    with pytest.raises(ValueError, match="buyburn-auction research source drift"):
        checker.build_document()
