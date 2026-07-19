# [TESTER] v1

from __future__ import annotations

from dataclasses import replace

from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig, DexState, step, step_with_candidate_settlement
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.core.liquidity import create_pool
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.core.settlement import FillAction, Settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _make_single_swap_setup() -> tuple[DexState, list[Intent], str, str, str, str]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 0)
    lp = LPTable()

    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=lp)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        )
    ]
    return state, intents, pool_id, pk, asset0, asset1


def _make_two_create_pool_setup(
    *,
    nonce_a: int | None,
    nonce_b: int | None,
) -> tuple[DexState, list[Intent], str]:
    pk = "0x" + "77" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    asset2 = "0x" + "33" * 32
    asset3 = "0x" + "44" * 32

    balances = BalanceTable()
    for asset in (asset0, asset1, asset2, asset3):
        balances.set(pk, asset, 10_000_000)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(11),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "amount0": 1000,
                "amount1": 1000,
                **({"nonce": int(nonce_a)} if nonce_a is not None else {}),
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(12),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset2,
                "asset1": asset3,
                "fee_bps": 30,
                "amount0": 1000,
                "amount1": 1000,
                **({"nonce": int(nonce_b)} if nonce_b is not None else {}),
            },
        ),
    ]
    return DexState(balances=balances, pools={}, lp_balances=LPTable()), intents, pk


def _make_snapshot_bound_quote_setup() -> tuple[DexState, list[Intent]]:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            curve_tag="CPMM",
            curve_params="",
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }

    quote = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=123,
    )
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    fields = dict(intent.fields or {})
    fields.pop("quote_receipt_hash", None)
    fields.pop("quote_receipt_leg_index", None)
    intent = replace(intent, fields=fields)

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())
    return state, [intent]


def test_dex_config_default_swap_ordering_is_explicitly_greedy_ab_refined() -> None:
    cfg = DexConfig()
    assert cfg.swap_ordering == "greedy_ab_refined"


def test_step_with_candidate_settlement_accepts_valid_candidate() -> None:
    state, intents, pool_id, pk, asset0, asset1 = _make_single_swap_setup()
    intents[0] = intents[0].with_field("nonce", 1)
    cfg = DexConfig(settlement_validation="strong_replay")

    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )

    r_candidate = step_with_candidate_settlement(
        cfg, state, intents, candidate_settlement=candidate
    )
    assert r_candidate.ok, r_candidate.error
    assert r_candidate.state is not None

    # Sanity: internal "propose then verify" path should also succeed.
    r_internal = step(cfg, state, intents)
    assert r_internal.ok, r_internal.error
    assert r_internal.state is not None

    # Post-states must match for the same single-intent batch.
    assert (
        r_candidate.state.balances.get(pk, asset0)
        == r_internal.state.balances.get(pk, asset0)
    )
    assert (
        r_candidate.state.balances.get(pk, asset1)
        == r_internal.state.balances.get(pk, asset1)
    )
    assert r_candidate.state.pools[pool_id].reserve0 == r_internal.state.pools[pool_id].reserve0
    assert r_candidate.state.pools[pool_id].reserve1 == r_internal.state.pools[pool_id].reserve1
    assert r_candidate.state.nonces.get_last(pk) == 1
    assert r_internal.state.nonces.get_last(pk) == 1


def test_intent_auth_shape_covers_material_swap_fields_before_candidate_settlement() -> None:
    state, intents, _pool_id, _pk, _asset0, _asset1 = _make_single_swap_setup()
    intent = intents[0]
    intent = intent.with_field("nonce", 1)
    intents[0] = intent
    material_fields = {
        "pool_id": intent.fields["pool_id"],
        "asset_in": intent.fields["asset_in"],
        "asset_out": intent.fields["asset_out"],
        "amount_in": intent.fields["amount_in"],
        "min_amount_out": intent.fields["min_amount_out"],
        "nonce": 1,
    }

    signing_dict = build_dex_intent_signing_dict_v1(intent)
    assert signing_dict["fields"] == material_fields

    cfg = DexConfig(settlement_validation="strong_replay")
    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )
    assert candidate.fills
    assert candidate.fills[0].amount_in_filled == material_fields["amount_in"]
    assert candidate.fills[0].intent_id == intent.intent_id

    result = step_with_candidate_settlement(cfg, state, intents, candidate_settlement=candidate)
    assert result.ok, result.error
    assert result.state is not None


def test_step_advances_nonce_state_for_valid_out_of_order_batch() -> None:
    state, intents, pk = _make_two_create_pool_setup(nonce_a=2, nonce_b=1)

    result = step(
        DexConfig(
            settlement_validation="strong_replay",
            reject_settlements_with_rejected_intents=False,
        ),
        state,
        intents,
    )

    assert result.ok, result.error
    assert result.state is not None
    assert state.nonces.get_last(pk) == 0
    assert result.state.nonces.get_last(pk) == 2


def test_step_with_candidate_settlement_rejects_mixed_nonce_presence() -> None:
    state, intents, _pk = _make_two_create_pool_setup(nonce_a=1, nonce_b=None)
    cfg = DexConfig(settlement_validation="strong_replay")

    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )

    result = step_with_candidate_settlement(cfg, state, intents, candidate_settlement=candidate)

    assert not result.ok
    assert result.error is not None
    assert "nonce" in result.error


def test_step_with_candidate_settlement_rejects_rejected_intent_by_default() -> None:
    state, intents, _pool_id, _pk, _asset0, _asset1 = _make_single_swap_setup()
    cfg = DexConfig(settlement_validation="strong_replay")
    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )
    rejected = replace(
        candidate,
        included_intents=[(intents[0].intent_id, FillAction.REJECT)],
        fills=[
            replace(
                candidate.fills[0],
                action=FillAction.REJECT,
                reason="bdd_invalid_state",
                amount_in_filled=None,
                amount_out_filled=None,
                fee_paid=None,
                protocol_fee_paid=None,
                reserve_in_before=None,
                reserve_out_before=None,
            )
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    result = step_with_candidate_settlement(cfg, state, intents, candidate_settlement=rejected)

    assert result.ok is False
    assert result.error == (
        "settlement contains rejected intent at public DEX boundary: "
        f"{intents[0].intent_id}"
    )
    assert result.state is None


def test_step_with_candidate_settlement_allows_rejected_intent_when_boundary_opted_out() -> None:
    state, intents, _pool_id, _pk, _asset0, _asset1 = _make_single_swap_setup()
    cfg = DexConfig(
        settlement_validation="strong_replay",
        reject_settlements_with_rejected_intents=False,
    )
    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )
    rejected = replace(
        candidate,
        included_intents=[(intents[0].intent_id, FillAction.REJECT)],
        fills=[
            replace(
                candidate.fills[0],
                action=FillAction.REJECT,
                reason="internal_noop",
                amount_in_filled=None,
                amount_out_filled=None,
                fee_paid=None,
                protocol_fee_paid=None,
                reserve_in_before=None,
                reserve_out_before=None,
            )
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    result = step_with_candidate_settlement(cfg, state, intents, candidate_settlement=rejected)

    assert result.ok, result.error
    assert result.state is not None
    assert result.state.balances.get(intents[0].sender_pubkey, intents[0].fields["asset_in"]) == (
        state.balances.get(intents[0].sender_pubkey, intents[0].fields["asset_in"])
    )


def test_step_rejects_snapshot_bound_quote_binding_without_explicit_opt_in() -> None:
    state, intents = _make_snapshot_bound_quote_setup()

    result = step(DexConfig(settlement_validation="strong_replay"), state, intents)

    assert not result.ok
    assert result.error is not None
    assert "quote receipt snapshot binding requires validated engine witness" in result.error
    assert f"intent_id='{intents[0].intent_id}'" in result.error


def test_step_accepts_snapshot_bound_quote_binding_with_explicit_opt_in() -> None:
    state, intents = _make_snapshot_bound_quote_setup()

    result = step(
        DexConfig(
            settlement_validation="strong_replay",
            allow_snapshot_bound_quote_bindings=True,
        ),
        state,
        intents,
    )

    assert result.ok, result.error
    assert result.state is not None


def test_step_with_candidate_settlement_accepts_snapshot_bound_quote_binding_with_opt_in() -> None:
    state, intents = _make_snapshot_bound_quote_setup()
    cfg = DexConfig(
        settlement_validation="strong_replay",
        allow_snapshot_bound_quote_bindings=True,
    )
    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(cfg.swap_ordering),
    )

    result = step_with_candidate_settlement(
        cfg,
        state,
        intents,
        candidate_settlement=candidate,
    )

    assert result.ok, result.error
    assert result.state is not None


class TestStepWithCandidateSettlementBVA:
    """Boundary Value Analysis (BVA) for candidate-settlement verification."""

    def test_rejects_off_by_one_amount_out(self) -> None:
        # Boundary: valid -> invalid by a minimal unit change (amount_out - 1).
        state, intents, _pool_id, _pk, _asset0, _asset1 = _make_single_swap_setup()
        cfg = DexConfig(settlement_validation="strong_replay")

        candidate: Settlement = compute_settlement(
            intents=intents,
            pools=state.pools,
            balances=state.balances,
            lp_balances=state.lp_balances,
            swap_ordering=str(cfg.swap_ordering),
        )
        assert candidate.fills and candidate.fills[0].amount_out_filled is not None
        assert int(candidate.fills[0].amount_out_filled) >= 2

        bad_fills = [
            replace(f, amount_out_filled=int(f.amount_out_filled) - 1)
            if f.action.value == "FILL"
            else f
            for f in candidate.fills
        ]
        bad = replace(candidate, fills=bad_fills)

        r = step_with_candidate_settlement(cfg, state, intents, candidate_settlement=bad)
        assert not r.ok
        assert r.error is not None
