from __future__ import annotations

import copy
from typing import Any, Callable

import pytest

import src.core.quote_receipts as quote_receipts_module
from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.frontier_signature_root import (
    FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
    FrontierSignatureCertificatesRootBinding,
)
from src.core.quote_receipt_limits import (
    ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG,
    ROUTE_QUOTE_RECEIPT_MAX_LEGS,
    ROUTE_QUOTE_RECEIPT_MAX_POOLS,
)
from src.core.quote_receipts import (
    QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE,
    QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_OK,
    RouteQuoteReceiptCertificateOutcome,
    _pool_reserves_for_hop,
    _ReceiptHopData,
    _replay_and_apply_hop,
    _require_receipt_gate_flag,
    attach_frontier_signature_binding_to_route_quote_receipt,
    evaluate_route_quote_receipt_certificate_gate,
    evaluate_route_quote_receipt_hop_replay_gate,
    make_route_quote_receipt,
    pool_state_fingerprint,
    receipt_hash,
    verify_route_quote_receipt,
)
from src.core.routing import (
    RouteHop,
    RouteLeg,
    RouteQuote,
    best_route_exact_in_2hop,
    best_route_exact_out_2hop,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _hop_data(
    pool: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    amount_out: int,
) -> _ReceiptHopData:
    return _ReceiptHopData(
        pool_id=pool.pool_id,
        pool=pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in),
        amount_out=int(amount_out),
    )


def _single_hop_exact_in_receipt() -> tuple[dict[str, Any], dict[str, PoolState]]:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
    }
    pool = pools["p_ab"]
    amount_in = 100
    amount_out, _ = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in,
    )
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": amount_in,
        "amount_out": int(amount_out),
        "legs": [
            {
                "amount_in": amount_in,
                "amount_out": int(amount_out),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in,
                        "amount_out": int(amount_out),
                    }
                ],
            }
        ],
        "pools": {
            "p_ab": pool_state_fingerprint(pool),
        },
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _single_hop_exact_out_receipt() -> tuple[dict[str, Any], dict[str, PoolState]]:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
    }
    pool = pools["p_ab"]
    amount_out = 50
    amount_in, _ = swap_exact_out_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_out=amount_out,
    )
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_out",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": int(amount_in),
        "amount_out": amount_out,
        "legs": [
            {
                "amount_in": int(amount_in),
                "amount_out": amount_out,
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": int(amount_in),
                        "amount_out": amount_out,
                    }
                ],
            }
        ],
        "pools": {
            "p_ab": pool_state_fingerprint(pool),
        },
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def test_quote_receipt_exact_in_roundtrip() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    assert "canonical_route_certificate" in receipt["body"]
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err

    # Receipt hash should be deterministic across dict ordering.
    pools_flipped = dict(reversed(list(pools.items())))
    receipt2 = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools_flipped)
    assert receipt2["receipt_hash"] == receipt["receipt_hash"]

    # Mutate a pool snapshot: verification should fail-closed.
    pools_mut = dict(pools)
    p_ab = pools_mut["p_ab"]
    pools_mut["p_ab"] = PoolState(
        pool_id=p_ab.pool_id,
        asset0=p_ab.asset0,
        asset1=p_ab.asset1,
        reserve0=int(p_ab.reserve0) + 1,
        reserve1=int(p_ab.reserve1),
        fee_bps=int(p_ab.fee_bps),
        lp_supply=int(p_ab.lp_supply),
        status=p_ab.status,
        created_at=int(p_ab.created_at),
        curve_tag=p_ab.curve_tag,
        curve_params=p_ab.curve_params,
    )
    ok2, err2 = verify_route_quote_receipt(receipt, pools_by_id=pools_mut)
    assert not ok2
    assert err2 in {"pool_snapshot_mismatch", "hop_quote_mismatch", "hop_quote_error"}


def test_quote_receipt_roundtrip_with_quote_epoch() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools, quote_epoch=7)
    assert receipt["body"]["quote_epoch"] == 7
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_quote_receipt_accepts_expected_quote_epoch() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools, quote_epoch=7)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools, expected_quote_epoch=7)
    assert ok, err


def test_quote_receipt_binds_expected_frontier_signature_root() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=120,
    )
    assert q is not None
    frontier_root = "0x" + "aa" * 32

    receipt = attach_frontier_signature_binding_to_route_quote_receipt(
        make_route_quote_receipt(
            kind="exact_in",
            quote=q,
            pools_by_id=pools,
        ),
        frontier_signature_binding=FrontierSignatureCertificatesRootBinding(
            certificate_count=1,
            certificates_root=frontier_root,
        ),
    )

    assert receipt["body"]["shared_pool_frontier_signature_certificate_count"] == 1
    assert (
        receipt["body"]["shared_pool_frontier_signature_certificates_root"]
        == frontier_root
    )
    ok, err = verify_route_quote_receipt(
        receipt,
        pools_by_id=pools,
        expected_frontier_signature_binding=FrontierSignatureCertificatesRootBinding(
            certificate_count=1,
            certificates_root=frontier_root,
        ),
    )
    assert ok, err

    forged = copy.deepcopy(receipt)
    forged["body"]["shared_pool_frontier_signature_certificates_root"] = "0x" + "bb" * 32
    forged["receipt_hash"] = receipt_hash(forged["body"])
    ok, err = verify_route_quote_receipt(
        forged,
        pools_by_id=pools,
        expected_frontier_signature_binding=FrontierSignatureCertificatesRootBinding(
            certificate_count=1,
            certificates_root=frontier_root,
        ),
    )
    assert not ok
    assert err == "frontier_signature_root_mismatch"


def test_quote_receipt_rejects_missing_expected_frontier_signature_root() -> None:
    receipt, pools = _single_hop_exact_in_receipt()

    ok, err = verify_route_quote_receipt(
        receipt,
        pools_by_id=pools,
        expected_frontier_signature_binding=(
            FrontierSignatureCertificatesRootBinding(
                certificate_count=0,
                certificates_root=FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
            )
        ),
    )

    assert not ok
    assert err == "missing_frontier_signature_binding"


def test_quote_receipt_rejects_partial_frontier_signature_binding() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    mutated["body"]["shared_pool_frontier_signature_certificate_count"] = 1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])

    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)

    assert not ok
    assert err == "frontier_signature_binding_partial"


def test_make_route_quote_receipt_rejects_malformed_frontier_signature_binding() -> None:
    with pytest.raises(ValueError, match="must be empty root when count is zero"):
        FrontierSignatureCertificatesRootBinding(
            certificate_count=0,
            certificates_root="0x" + "aa" * 32,
        )


def test_quote_receipt_rejects_quote_epoch_session_mismatch() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools, quote_epoch=7)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools, expected_quote_epoch=8)
    assert not ok
    assert err == "quote_epoch_mismatch"


def test_quote_receipt_rejects_missing_quote_epoch_when_expected() -> None:
    receipt, pools = _single_hop_exact_in_receipt()

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools, expected_quote_epoch=7)
    assert not ok
    assert err == "missing_quote_epoch"


def test_quote_receipt_rejects_bad_expected_quote_epoch() -> None:
    receipt, pools = _single_hop_exact_in_receipt()

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools, expected_quote_epoch=-1)
    assert not ok
    assert err == "bad_expected_quote_epoch"


def test_quote_receipt_hop_replay_maps_expected_quote_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    pool = _pool("p_ab", "A", "B", 1_000, 1_000, 0)

    def rejecting_swap(*args: object, **kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("bad quote input")

    monkeypatch.setattr(quote_receipts_module, "swap_exact_in_for_pool", rejecting_swap)
    ok, err, next_pool = _replay_and_apply_hop(
        kind="exact_in",
        hop_data=_hop_data(pool, asset_in="A", asset_out="B", amount_in=100, amount_out=90),
    )

    assert not ok
    assert err == "hop_quote_error"
    assert next_pool is None


def test_quote_receipt_hop_replay_propagates_unexpected_quote_engine_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pool = _pool("p_ab", "A", "B", 1_000, 1_000, 0)

    def broken_swap(*args: object, **kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("quote engine bug")

    monkeypatch.setattr(quote_receipts_module, "swap_exact_in_for_pool", broken_swap)
    with pytest.raises(RuntimeError, match="quote engine bug"):
        _replay_and_apply_hop(
            kind="exact_in",
            hop_data=_hop_data(pool, asset_in="A", asset_out="B", amount_in=100, amount_out=90),
        )


def test_quote_receipt_exact_out_split_roundtrip() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    assert "canonical_route_certificate" not in receipt["body"]
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_quote_receipt_rejects_tampered_exact_in_canonical_certificate() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    body = copy.deepcopy(receipt["body"])
    cert = dict(body["canonical_route_certificate"])
    cert["winner_index"] = int(cert["winner_index"]) + 1
    body["canonical_route_certificate"] = cert
    bad = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(bad, pools_by_id=pools)
    assert not ok
    assert err == "bad_canonical_route_certificate:certificate payload mismatch"


def test_quote_receipt_rejects_unexpected_canonical_certificate_on_exact_out() -> None:
    receipt, pools = _single_hop_exact_out_receipt()
    receipt["body"]["canonical_route_certificate"] = {"winner_quote": {}}
    receipt["receipt_hash"] = receipt_hash(receipt["body"])

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert not ok
    assert err == "unexpected_canonical_route_certificate"


def test_quote_receipt_rejects_bad_canonical_certificate_winner_shape(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.integration import exact_in_route_certificate as cert_module

    monkeypatch.setattr(
        cert_module,
        "verify_exact_in_route_canonical_certificate_payload",
        lambda _payload: (True, "ok"),
    )
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    body = copy.deepcopy(receipt["body"])
    cert = dict(body["canonical_route_certificate"])
    cert["winner_quote"] = 7
    body["canonical_route_certificate"] = cert
    bad = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(bad, pools_by_id=pools)
    assert not ok
    assert err == "bad_canonical_route_certificate_winner"


def test_quote_receipt_rejects_canonical_certificate_amount_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.integration import exact_in_route_certificate as cert_module

    monkeypatch.setattr(
        cert_module,
        "verify_exact_in_route_canonical_certificate_payload",
        lambda _payload: (True, "ok"),
    )
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    body = copy.deepcopy(receipt["body"])
    cert = dict(body["canonical_route_certificate"])
    winner = dict(cert["winner_quote"])
    winner["amount_in"] = int(winner["amount_in"]) + 1
    cert["winner_quote"] = winner
    body["canonical_route_certificate"] = cert
    bad = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(bad, pools_by_id=pools)
    assert not ok
    assert err == "canonical_route_certificate_amount_in_mismatch"


def test_quote_receipt_omits_exact_in_canonical_certificate_for_noncanonical_quote() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.legs[0].hops) == 2

    noncanonical = RouteQuote(
        asset_in=q.asset_in,
        asset_out=q.asset_out,
        amount_in=q.amount_in,
        amount_out=max(1, int(q.amount_out) - 1),
        legs=q.legs,
    )
    receipt = make_route_quote_receipt(kind="exact_in", quote=noncanonical, pools_by_id=pools)
    assert "canonical_route_certificate" not in receipt["body"]
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert not ok
    assert err in {"hop_quote_mismatch", "totals_mismatch"}


def test_quote_receipt_rejects_bad_quote_epoch() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    body = copy.deepcopy(receipt["body"])
    body["quote_epoch"] = -1
    bad = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(bad, pools_by_id=pools)
    assert not ok
    assert err == "bad_quote_epoch"


def test_quote_receipt_verifier_rejects_repeated_pool_split_with_stale_second_leg() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }
    pool = pools["p_ab"]
    amount_in_leg = 100
    out1, _next1 = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in_leg,
    )

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 2 * amount_in_leg,
        "amount_out": 2 * int(out1),
        "legs": [
            {
                "amount_in": amount_in_leg,
                "amount_out": int(out1),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in_leg,
                        "amount_out": int(out1),
                    }
                ],
            },
            {
                "amount_in": amount_in_leg,
                "amount_out": int(out1),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in_leg,
                        "amount_out": int(out1),
                    }
                ],
            },
        ],
        "pools": {
            "p_ab": pool_state_fingerprint(pool),
        },
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert not ok
    assert err == "hop_quote_mismatch"


def test_quote_receipt_verifier_accepts_repeated_pool_split_with_stateful_legs() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }
    pool = pools["p_ab"]
    amount_in_leg = 100
    out1, (r0_after_1, r1_after_1) = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in_leg,
    )
    pool_after_1 = PoolState(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=int(r0_after_1),
        reserve1=int(r1_after_1),
        fee_bps=int(pool.fee_bps),
        lp_supply=int(pool.lp_supply),
        status=pool.status,
        created_at=int(pool.created_at),
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )
    out2, _next2 = swap_exact_in_for_pool(
        pool_after_1,
        reserve_in=int(pool_after_1.reserve0),
        reserve_out=int(pool_after_1.reserve1),
        amount_in=amount_in_leg,
    )

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 2 * amount_in_leg,
        "amount_out": int(out1) + int(out2),
        "legs": [
            {
                "amount_in": amount_in_leg,
                "amount_out": int(out1),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in_leg,
                        "amount_out": int(out1),
                    }
                ],
            },
            {
                "amount_in": amount_in_leg,
                "amount_out": int(out2),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in_leg,
                        "amount_out": int(out2),
                    }
                ],
            },
        ],
        "pools": {
            "p_ab": pool_state_fingerprint(pool),
        },
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_make_route_quote_receipt_reuses_pool_fingerprint_for_repeated_pool() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }
    pool = pools["p_ab"]
    amount_in_leg = 100
    out1, (r0_after_1, r1_after_1) = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in_leg,
    )
    pool_after_1 = PoolState(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=int(r0_after_1),
        reserve1=int(r1_after_1),
        fee_bps=int(pool.fee_bps),
        lp_supply=int(pool.lp_supply),
        status=pool.status,
        created_at=int(pool.created_at),
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )
    out2, _ = swap_exact_in_for_pool(
        pool_after_1,
        reserve_in=int(pool_after_1.reserve0),
        reserve_out=int(pool_after_1.reserve1),
        amount_in=amount_in_leg,
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=2 * amount_in_leg,
        amount_out=int(out1) + int(out2),
        legs=(
            RouteLeg(
                hops=(RouteHop(pool_id="p_ab", asset_in="A", asset_out="B", amount_in=amount_in_leg, amount_out=int(out1)),),
                amount_in=amount_in_leg,
                amount_out=int(out1),
            ),
            RouteLeg(
                hops=(RouteHop(pool_id="p_ab", asset_in="A", asset_out="B", amount_in=amount_in_leg, amount_out=int(out2)),),
                amount_in=amount_in_leg,
                amount_out=int(out2),
            ),
        ),
    )
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    assert list(receipt["body"]["pools"].keys()) == ["p_ab"]
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_quote_receipt_verifier_rejects_missing_pool_fingerprint_for_hop() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    # Attacker-style mutation: remove a hop's pool fingerprint but keep hash consistent.
    body = dict(receipt["body"])
    pools_map = dict(body["pools"])
    pools_map.pop("p2")
    body["pools"] = pools_map
    receipt2 = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(receipt2, pools_by_id=pools)
    assert not ok
    assert err == "missing_pool_fingerprint"


def test_quote_receipt_verifier_rejects_asset_chain_mismatch() -> None:
    # Build a receipt that is numerically consistent hop-by-hop but semantically invalid
    # because the asset chain is broken between hops.
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_db": _pool("p_db", "D", "B", 1000, 1000, 0),
    }
    p_ac = pools["p_ac"]
    p_db = pools["p_db"]

    amt_in = 100
    out_ac, _ = swap_exact_in_for_pool(p_ac, reserve_in=int(p_ac.reserve0), reserve_out=int(p_ac.reserve1), amount_in=amt_in)
    # p_db has canonical ordering (B < D), but the hop we want is D -> B.
    out_db, _ = swap_exact_in_for_pool(p_db, reserve_in=int(p_db.reserve1), reserve_out=int(p_db.reserve0), amount_in=int(out_ac))

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": int(amt_in),
        "amount_out": int(out_db),
        "legs": [
            {
                "amount_in": int(amt_in),
                "amount_out": int(out_db),
                "hops": [
                    {
                        "pool_id": "p_ac",
                        "asset_in": "A",
                        "asset_out": "C",
                        "amount_in": int(amt_in),
                        "amount_out": int(out_ac),
                    },
                    {
                        "pool_id": "p_db",
                        "asset_in": "D",  # breaks the A->C->B chain (should be C)
                        "asset_out": "B",
                        "amount_in": int(out_ac),
                        "amount_out": int(out_db),
                    },
                ],
            }
        ],
        "pools": {
            "p_ac": pool_state_fingerprint(p_ac),
            "p_db": pool_state_fingerprint(p_db),
        },
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert not ok
    assert err == "hop_asset_chain_mismatch"


def test_quote_receipt_verifier_accepts_explicit_two_hop_route() -> None:
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 1000, 1500, 0),
        "p_cb": _pool("p_cb", "C", "B", 1500, 1200, 0),
    }
    p_ac = pools["p_ac"]
    p_cb = pools["p_cb"]
    amt_in = 120
    out_ac, _ = swap_exact_in_for_pool(
        p_ac,
        reserve_in=int(p_ac.reserve0),
        reserve_out=int(p_ac.reserve1),
        amount_in=amt_in,
    )
    out_cb, _ = swap_exact_in_for_pool(
        p_cb,
        reserve_in=int(p_cb.reserve1),
        reserve_out=int(p_cb.reserve0),
        amount_in=int(out_ac),
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=amt_in,
        amount_out=int(out_cb),
        legs=(
            RouteLeg(
                hops=(
                    RouteHop(pool_id="p_ac", asset_in="A", asset_out="C", amount_in=amt_in, amount_out=int(out_ac)),
                    RouteHop(pool_id="p_cb", asset_in="C", asset_out="B", amount_in=int(out_ac), amount_out=int(out_cb)),
                ),
                amount_in=amt_in,
                amount_out=int(out_cb),
            ),
        ),
    )
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_pool_reserves_for_hop_handles_forward_reverse_and_invalid_directions() -> None:
    pool = _pool("p_ab", "A", "B", 1000, 2000, 0)
    assert _pool_reserves_for_hop(pool, asset_in="A", asset_out="B") == (1000, 2000)
    assert _pool_reserves_for_hop(pool, asset_in="B", asset_out="A") == (2000, 1000)
    assert _pool_reserves_for_hop(pool, asset_in="A", asset_out="C") is None


def test_replay_and_apply_hop_exact_out_reverse_direction_and_mismatch() -> None:
    pool = _pool("p_ab", "A", "B", 1000, 2000, 0)
    amount_out = 150
    amount_in, (next_rin, next_rout) = swap_exact_out_for_pool(
        pool,
        reserve_in=int(pool.reserve1),
        reserve_out=int(pool.reserve0),
        amount_out=amount_out,
    )
    ok, err, next_pool = _replay_and_apply_hop(
        kind="exact_out",
        hop_data=_hop_data(pool, asset_in="B", asset_out="A", amount_in=int(amount_in) + 1, amount_out=amount_out),
    )
    assert not ok
    assert err == "hop_quote_mismatch"
    assert next_pool is None

    ok, err, next_pool = _replay_and_apply_hop(
        kind="exact_out",
        hop_data=_hop_data(pool, asset_in="B", asset_out="A", amount_in=int(amount_in), amount_out=amount_out),
    )
    assert ok
    assert err == "ok"
    assert next_pool is not None
    assert int(next_pool.reserve0) == int(next_rout)
    assert int(next_pool.reserve1) == int(next_rin)


def test_make_route_quote_receipt_rejects_invalid_kind() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    body = receipt["body"]
    quote = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in=body["asset_in"],
        asset_out=body["asset_out"],
        amount_in=body["amount_in"],
    )
    assert quote is not None
    with pytest.raises(ValueError, match="kind must be 'exact_in' or 'exact_out'"):
        make_route_quote_receipt(kind="bad_kind", quote=quote, pools_by_id=pools)


def test_make_route_quote_receipt_rejects_missing_pool_for_hop() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
        "p_ac": _pool("p_ac", "A", "C", 1_000, 1_000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1_000, 1_000, 0),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert quote is not None
    missing_pool_id = quote.legs[0].hops[0].pool_id
    pools_without_hop = {pid: pool for pid, pool in pools.items() if pid != missing_pool_id}
    with pytest.raises(ValueError, match=f"missing pool for hop\\.pool_id='{missing_pool_id}'"):
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools_without_hop)


def test_make_route_quote_receipt_rejects_bad_quote_epoch() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert quote is not None
    with pytest.raises(ValueError, match="quote_epoch must be a non-negative int"):
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=-1)


def test_make_route_quote_receipt_rejects_bool_amount_before_hashing() -> None:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    hop = RouteHop(pool_id="p_ab", asset_in="A", asset_out="B", amount_in=True, amount_out=90)
    leg = RouteLeg(hops=(hop,), amount_in=True, amount_out=90)
    quote = RouteQuote(asset_in="A", asset_out="B", amount_in=True, amount_out=90, legs=(leg,))

    with pytest.raises(TypeError, match="hop.amount_in must be an int"):
        make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools)


def test_make_route_quote_receipt_rejects_zero_amount_before_hashing() -> None:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    hop = RouteHop(pool_id="p_ab", asset_in="A", asset_out="B", amount_in=0, amount_out=90)
    leg = RouteLeg(hops=(hop,), amount_in=0, amount_out=90)
    quote = RouteQuote(asset_in="A", asset_out="B", amount_in=0, amount_out=90, legs=(leg,))

    with pytest.raises(ValueError, match="hop.amount_in must be positive"):
        make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools)


def test_pool_state_fingerprint_rejects_bool_numeric_field() -> None:
    pool = _pool("p_ab", "A", "B", 1_000, 1_000, 0)
    pool.reserve0 = True

    with pytest.raises(TypeError, match="pool.reserve0 must be an int"):
        pool_state_fingerprint(pool)


def _mutate_missing_body(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated.pop("body", None)
    return mutated, pools


def _mutate_missing_receipt_hash(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated.pop("receipt_hash", None)
    return mutated, pools


def _mutate_hash_mismatch(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["receipt_hash"] = "0xdeadbeef"
    return mutated, pools


def _mutate_bad_kind(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["kind"] = "strange"
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_schema(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["schema"] = "zenodex/route_quote_receipt/v999"
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_body_assets(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["asset_out"] = mutated["body"]["asset_in"]
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_quote_epoch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["quote_epoch"] = -1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_pools_shape(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["pools"] = []
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_missing_pool(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    return mutated, {}


def _mutate_bad_pool_fingerprint_shape(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["pools"]["p_ab"] = 123
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_hops_shape(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"] = []
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_legs_shape(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"] = []
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_leg_entry(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"] = [7]
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_leg_amounts(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["amount_in"] = 0
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_hop_entry(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"] = [7]
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_pool_id(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"][0]["pool_id"] = ""
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_assets_shape(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"][0]["asset_out"] = 7
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_leg_asset_in_mismatch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"][0]["asset_in"] = "Z"
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_hop_amounts(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"][0]["amount_in"] = 0
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_hop_chain_mismatch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"].append(
        {
            "pool_id": "p_ab",
            "asset_in": "B",
            "asset_out": "A",
            "amount_in": mutated["body"]["legs"][0]["hops"][0]["amount_out"] + 1,
            "amount_out": 1,
        }
    )
    mutated["body"]["legs"][0]["amount_out"] = 1
    mutated["body"]["amount_out"] = 1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_bad_pool_direction(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    hop = mutated["body"]["legs"][0]["hops"][0]
    hop["asset_in"] = "A"
    hop["asset_out"] = "C"
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_leg_asset_out_mismatch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["asset_out"] = "C"
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_leg_amount_in_mismatch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["amount_in"] += 1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_leg_amount_out_mismatch(
    receipt: dict[str, Any], pools: dict[str, PoolState]
) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["amount_out"] += 1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


def _mutate_totals_mismatch(receipt: dict[str, Any], pools: dict[str, PoolState]) -> tuple[dict[str, Any], dict[str, PoolState]]:
    mutated = copy.deepcopy(receipt)
    mutated["body"]["amount_out"] += 1
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    return mutated, pools


@pytest.mark.parametrize(
    ("mutator", "expected_err"),
    [
        (_mutate_missing_body, "missing_body"),
        (_mutate_missing_receipt_hash, "missing_receipt_hash"),
        (_mutate_hash_mismatch, "hash_mismatch"),
        (_mutate_bad_kind, "bad_kind"),
        (_mutate_bad_schema, "bad_schema"),
        (_mutate_bad_body_assets, "bad_body_assets"),
        (_mutate_bad_quote_epoch, "bad_quote_epoch"),
        (_mutate_bad_pools_shape, "bad_pools"),
        (_mutate_missing_pool, "missing_pool"),
        (_mutate_bad_pool_fingerprint_shape, "bad_pool_fingerprint"),
        (_mutate_bad_legs_shape, "bad_legs"),
        (_mutate_bad_leg_entry, "bad_leg"),
        (_mutate_bad_hops_shape, "bad_hops"),
        (_mutate_bad_leg_amounts, "bad_leg_amounts"),
        (_mutate_bad_hop_entry, "bad_hop"),
        (_mutate_bad_pool_id, "bad_pool_id"),
        (_mutate_bad_assets_shape, "bad_assets"),
        (_mutate_leg_asset_in_mismatch, "leg_asset_in_mismatch"),
        (_mutate_bad_hop_amounts, "bad_hop_amounts"),
        (_mutate_hop_chain_mismatch, "hop_chain_mismatch"),
        (_mutate_bad_pool_direction, "bad_pool_direction"),
        (_mutate_leg_asset_out_mismatch, "leg_asset_out_mismatch"),
        (_mutate_leg_amount_in_mismatch, "leg_amount_in_mismatch"),
        (_mutate_leg_amount_out_mismatch, "leg_amount_out_mismatch"),
        (_mutate_totals_mismatch, "totals_mismatch"),
    ],
)
def test_quote_receipt_verifier_rejects_malformed_single_hop_receipts(
    mutator: Callable[[dict[str, Any], dict[str, PoolState]], tuple[dict[str, Any], dict[str, PoolState]]],
    expected_err: str,
) -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated_receipt, mutated_pools = mutator(receipt, pools)
    ok, err = verify_route_quote_receipt(mutated_receipt, pools_by_id=mutated_pools)
    assert not ok
    assert err == expected_err


def test_quote_receipt_verifier_rejects_non_dict_receipt_type() -> None:
    ok, err = verify_route_quote_receipt(["not", "a", "receipt"], pools_by_id={})
    assert not ok
    assert err == "bad_receipt_type"


def test_quote_receipt_verifier_rejects_behavior_changing_pool_map_at_boundary() -> None:
    class InconsistentPools(dict[str, str]):
        def __iter__(self):
            return iter(())

        def __contains__(self, key: object) -> bool:
            return dict.__contains__(self, key)

    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    mutated["body"]["pools"] = InconsistentPools(mutated["body"]["pools"])
    with pytest.raises(TypeError, match="mapping subclasses"):
        receipt_hash(mutated["body"])
    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)
    assert not ok
    assert err == "bad_receipt_type"


def test_quote_receipt_verifier_rejects_oversized_pool_snapshot_map() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    mutated["body"]["pools"] = {
        f"pool-{index}": "0x" + f"{index:064x}"[-64:]
        for index in range(ROUTE_QUOTE_RECEIPT_MAX_POOLS + 1)
    }
    mutated["receipt_hash"] = receipt_hash(mutated["body"])

    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)

    assert not ok
    assert err == "bad_pools"


def test_quote_receipt_verifier_rejects_oversized_leg_list() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    leg = copy.deepcopy(mutated["body"]["legs"][0])
    mutated["body"]["legs"] = [copy.deepcopy(leg) for _ in range(ROUTE_QUOTE_RECEIPT_MAX_LEGS + 1)]
    mutated["receipt_hash"] = receipt_hash(mutated["body"])

    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)

    assert not ok
    assert err == "bad_legs"


def test_quote_receipt_verifier_rejects_oversized_hop_list() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    hop = copy.deepcopy(mutated["body"]["legs"][0]["hops"][0])
    mutated["body"]["legs"][0]["hops"] = [
        copy.deepcopy(hop)
        for _ in range(ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG + 1)
    ]
    mutated["receipt_hash"] = receipt_hash(mutated["body"])

    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)

    assert not ok
    assert err == "bad_hops"


def test_quote_receipt_builder_rejects_quote_outside_shape_limits() -> None:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    hop = RouteHop(pool_id="p_ab", asset_in="A", asset_out="B", amount_in=1, amount_out=1)
    leg = RouteLeg(hops=(hop,), amount_in=1, amount_out=1)
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=ROUTE_QUOTE_RECEIPT_MAX_LEGS + 1,
        amount_out=ROUTE_QUOTE_RECEIPT_MAX_LEGS + 1,
        legs=tuple(copy.deepcopy(leg) for _ in range(ROUTE_QUOTE_RECEIPT_MAX_LEGS + 1)),
    )

    with pytest.raises(ValueError, match="quote legs must be"):
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)


def test_quote_receipt_verifier_rejects_exact_out_impossible_hop_as_quote_error() -> None:
    receipt, pools = _single_hop_exact_out_receipt()
    mutated = copy.deepcopy(receipt)
    mutated["body"]["legs"][0]["hops"][0]["amount_out"] = 2_000
    mutated["body"]["legs"][0]["amount_out"] = 2_000
    mutated["body"]["amount_out"] = 2_000
    mutated["receipt_hash"] = receipt_hash(mutated["body"])
    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)
    assert not ok
    assert err == "hop_quote_error"


def test_quote_receipt_verifier_rejects_bool_like_body_amounts() -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    mutated = copy.deepcopy(receipt)
    mutated["body"]["amount_in"] = True
    mutated["receipt_hash"] = receipt_hash(mutated["body"])

    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)

    assert not ok
    assert err == "bad_body_amounts"


def test_replay_and_apply_hop_fail_closed_on_inconsistent_direction_contract(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt, pools = _single_hop_exact_in_receipt()
    pool = pools["p_ab"]
    hop = receipt["body"]["legs"][0]["hops"][0]

    monkeypatch.setattr(
        "src.core.quote_receipts._pool_reserves_for_hop",
        lambda *args, **kwargs: (int(pool.reserve0), int(pool.reserve1)),
    )

    ok, err, next_pool = _replay_and_apply_hop(
        kind="exact_in",
        hop_data=_hop_data(
            pool,
            asset_in="A",
            asset_out="C",
            amount_in=int(hop["amount_in"]),
            amount_out=int(hop["amount_out"]),
        ),
    )

    assert not ok
    assert err == "bad_pool_direction"
    assert next_pool is None

@pytest.mark.parametrize(("raw", "expected"), [(0, False), (1, True)])
def test_require_receipt_gate_flag_accepts_zero_one_ints(raw: int, expected: bool) -> None:
    assert _require_receipt_gate_flag(raw, name="flag") is expected


@pytest.mark.parametrize("raw", [2, -1, "1", None])
def test_require_receipt_gate_flag_rejects_non_boolish_values(raw: object) -> None:
    with pytest.raises(ValueError, match="flag must be a bool or 0/1 int"):
        _require_receipt_gate_flag(raw, name="flag")


@pytest.mark.parametrize(
    ("kwargs", "expected"),
    [
        (
            {
                "cert_present": False,
                "cert_dict_ok": True,
                "winner_quote_dict_ok": True,
                "asset_in_match": True,
                "asset_out_match": True,
                "amount_in_match": True,
                "amount_out_match": True,
                "legs_match": True,
            },
            QUOTE_RECEIPT_CERTIFICATE_OK,
        ),
        (
            {
                "cert_present": True,
                "cert_dict_ok": False,
                "winner_quote_dict_ok": True,
                "asset_in_match": True,
                "asset_out_match": True,
                "amount_in_match": True,
                "amount_out_match": True,
                "legs_match": True,
            },
            QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE,
        ),
        (
            {
                "cert_present": True,
                "cert_dict_ok": True,
                "winner_quote_dict_ok": True,
                "asset_in_match": False,
                "asset_out_match": True,
                "amount_in_match": True,
                "amount_out_match": True,
                "legs_match": True,
            },
            QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH,
        ),
        (
            {
                "cert_present": True,
                "cert_dict_ok": True,
                "winner_quote_dict_ok": True,
                "asset_in_match": True,
                "asset_out_match": False,
                "amount_in_match": True,
                "amount_out_match": True,
                "legs_match": True,
            },
            QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH,
        ),
        (
            {
                "cert_present": True,
                "cert_dict_ok": True,
                "winner_quote_dict_ok": True,
                "asset_in_match": True,
                "asset_out_match": True,
                "amount_in_match": True,
                "amount_out_match": False,
                "legs_match": True,
            },
            QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH,
        ),
        (
            {
                "cert_present": True,
                "cert_dict_ok": True,
                "winner_quote_dict_ok": True,
                "asset_in_match": True,
                "asset_out_match": True,
                "amount_in_match": True,
                "amount_out_match": True,
                "legs_match": False,
            },
            QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH,
        ),
    ],
)
def test_certificate_gate_direct_reject_code_matrix(
    kwargs: dict[str, bool],
    expected: str,
) -> None:
    outcome = evaluate_route_quote_receipt_certificate_gate(**kwargs)
    assert isinstance(outcome, RouteQuoteReceiptCertificateOutcome)
    assert outcome.reject_code == expected
    assert outcome.certificate_ok is (expected == QUOTE_RECEIPT_CERTIFICATE_OK)


@pytest.mark.parametrize(
    ("next_in", "next_out", "expected"),
    [
        (-1, 1, "next_reserve_in must be a non-negative int"),
        (1, -1, "next_reserve_out must be a non-negative int"),
        (None, 1, "next_reserve_in must be a non-negative int"),
        (1, None, "next_reserve_out must be a non-negative int"),
    ],
)
def test_hop_replay_gate_rejects_invalid_next_reserves(
    next_in: object,
    next_out: object,
    expected: str,
) -> None:
    with pytest.raises(ValueError, match=expected):
        evaluate_route_quote_receipt_hop_replay_gate(
            direction_ok=True,
            forward_direction=True,
            swap_ok=True,
            quote_matches=True,
            next_reserve_in=next_in,
            next_reserve_out=next_out,
        )
