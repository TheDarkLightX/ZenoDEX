"""Characterization corpus for ``verify_route_quote_receipt`` orchestration.

This corpus LOCKS the observable ``(ok, error_code)`` contract of
``src.core.quote_receipts.verify_route_quote_receipt`` -- including reject
*ordering* under multi-fault inputs and the no-op-on-reject guarantee -- so the
function can be refactored (complexity reduction) with byte-for-byte behavior
preservation.

It is the "characterization-corpus-first" safety net for the orchestrator
refactor: the JSON fixture is captured against the UNMODIFIED function and the
refactored function must reproduce every recorded ``(ok, err)`` exactly.

Regenerate the committed fixture with::

    PYTHONPATH=<harness>:<repo> python3 \
        tests/core/test_quote_receipts_orchestration_characterization.py --regen

(See the campaign report for the ``<harness>`` shim that works around the
PRE-EXISTING, unrelated ``MARK_PRICE_SOURCE_EXTERNAL_MEDIAN`` import break in
``src/core/perp_apply_funding_auto_gate.py`` on this branch's base. The shim is
out-of-scope to fix here and lives only on ``PYTHONPATH`` -- never in the repo.)

Notes on the contract being locked:

* The ``bad_pools`` / ``bad_legs`` / ``bad_body_assets`` strings are produced by
  the PRECHECK gate (``pools_object_ok`` / ``legs_list_ok`` / ``body_assets_ok``).
  The defensive type-narrowing blocks deeper in the function that re-emit those
  same strings are UNREACHABLE (precheck wins first), so the corpus binds those
  reject codes via their reachable precheck producers -- you cannot construct an
  input that reaches the narrowing blocks.
* ``no_op_on_reject``: ``PoolState`` is frozen and the verifier evolves a private
  ``working_pools`` dict of copies, so a mid-route reject must leave every caller
  pool fingerprint unchanged. The corpus asserts this explicitly.
"""

from __future__ import annotations

import copy
import json
import os
import sys
from contextlib import contextmanager
from dataclasses import replace
from typing import Any, Dict, Iterator, List, Tuple

import pytest

from src.core.amm_dispatch import swap_exact_in_for_pool
from src.core.quote_receipts import (
    make_route_quote_receipt,
    pool_state_fingerprint,
    receipt_hash,
    verify_route_quote_receipt,
)
from src.core.routing import best_route_exact_in_2hop
from src.state.pools import PoolState, PoolStatus

CORPUS_PATH = os.path.join(
    os.path.dirname(__file__),
    "fixtures",
    "quote_receipts_orchestration_characterization.json",
)

_CERT_MODULE = "src.integration.exact_in_route_certificate"
_CERT_ATTR = "verify_exact_in_route_canonical_certificate_payload"

JsonObj = Dict[str, Any]


# --------------------------------------------------------------------------- #
# Pool helpers + (de)serialization
# --------------------------------------------------------------------------- #
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


def _pool_to_json(p: PoolState) -> JsonObj:
    return {
        "pool_id": p.pool_id,
        "asset0": p.asset0,
        "asset1": p.asset1,
        "reserve0": int(p.reserve0),
        "reserve1": int(p.reserve1),
        "fee_bps": int(p.fee_bps),
        "lp_supply": int(p.lp_supply),
        "status": p.status.value,
        "created_at": int(p.created_at),
        "curve_tag": str(p.curve_tag),
        "curve_params": str(p.curve_params),
    }


def _pool_from_json(d: JsonObj) -> PoolState:
    return PoolState(
        pool_id=d["pool_id"],
        asset0=d["asset0"],
        asset1=d["asset1"],
        reserve0=int(d["reserve0"]),
        reserve1=int(d["reserve1"]),
        fee_bps=int(d["fee_bps"]),
        lp_supply=int(d["lp_supply"]),
        status=PoolStatus(d["status"]),
        created_at=int(d["created_at"]),
        curve_tag=str(d["curve_tag"]),
        curve_params=str(d["curve_params"]),
    )


def _pools_to_json(pools: Dict[str, PoolState]) -> JsonObj:
    return {pid: _pool_to_json(p) for pid, p in pools.items()}


class _InconsistentPools(dict):
    """A body['pools'] map that claims membership but yields nothing on iteration.

    Mirrors the existing fuzz test's construction: ``__contains__`` returns True
    for present keys (snapshot check + ``pid in pools`` see it) but ``__iter__``
    yields nothing, so ``working_pools`` is built empty -> the hop hits
    ``missing_working_pool``.
    """

    def __iter__(self) -> Iterator[Any]:  # type: ignore[override]
        return iter(())

    def __contains__(self, key: object) -> bool:
        return dict.__contains__(self, key)


class _GetItemBombDict(dict):
    """A dict subclass whose explicit indexing raises but whose C-slot reads work.

    ``.get(...)``, ``.items()``, ``.keys()``, iteration, ``in`` and JSON/canonical
    encoding all read the real underlying storage (C slots, not ``__getitem__``),
    so receipts containing this object hash and verify normally -- but any
    ``obj[key]`` re-read raises. Pins the verifier's single-read contract: every
    receipt-data mapping key must be read exactly once via ``.get``.
    """

    def __getitem__(self, key: object) -> Any:
        raise RuntimeError(f"adversarial __getitem__({key!r})")


@contextmanager
def _cert_payload_stub() -> Iterator[None]:
    """Force the canonical-route-certificate payload verifier to accept.

    Used (exactly as the existing tests do) so multi-fault corpus cases can reach
    the certificate *gate* (winner-quote consistency) rather than being rejected
    at the payload-verification step first.
    """
    from src.integration import exact_in_route_certificate as m  # noqa: WPS433

    orig = getattr(m, _CERT_ATTR)
    setattr(m, _CERT_ATTR, lambda _payload: (True, "ok"))
    try:
        yield
    finally:
        setattr(m, _CERT_ATTR, orig)


def _replay_hop(p: PoolState, asset_in: str, asset_out: str, amount_in: int) -> Tuple[int, PoolState]:
    """Replay one exact-in hop exactly like the verifier does (forward/reverse)."""
    forward = asset_in == p.asset0 and asset_out == p.asset1
    rin = int(p.reserve0) if forward else int(p.reserve1)
    rout = int(p.reserve1) if forward else int(p.reserve0)
    out, (nin, nout) = swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
    n0, n1 = (nin, nout) if forward else (nout, nin)
    return int(out), replace(p, reserve0=int(n0), reserve1=int(n1))


def _rehash(receipt: JsonObj) -> JsonObj:
    receipt["receipt_hash"] = receipt_hash(receipt["body"])
    return receipt


# --------------------------------------------------------------------------- #
# Base receipts (each returns (receipt_json, caller_pools_runtime))
# --------------------------------------------------------------------------- #
def _base_single_hop_exact_in() -> Tuple[JsonObj, Dict[str, PoolState]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    pool = pools["p_ab"]
    amount_in = 100
    out, _ = swap_exact_in_for_pool(
        pool, reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), amount_in=amount_in
    )
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": amount_in,
        "amount_out": int(out),
        "legs": [
            {
                "amount_in": amount_in,
                "amount_out": int(out),
                "hops": [
                    {
                        "pool_id": "p_ab",
                        "asset_in": "A",
                        "asset_out": "B",
                        "amount_in": amount_in,
                        "amount_out": int(out),
                    }
                ],
            }
        ],
        "pools": {"p_ab": pool_state_fingerprint(pool)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_single_hop_exact_in_with_epoch(epoch: int) -> Tuple[JsonObj, Dict[str, PoolState]]:
    receipt, pools = _base_single_hop_exact_in()
    receipt["body"]["quote_epoch"] = int(epoch)
    return _rehash(receipt), pools


def _base_single_hop_exact_out() -> Tuple[JsonObj, Dict[str, PoolState]]:
    from src.core.amm_dispatch import swap_exact_out_for_pool  # noqa: WPS433

    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    pool = pools["p_ab"]
    amount_out = 50
    amount_in, _ = swap_exact_out_for_pool(
        pool, reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), amount_out=amount_out
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
        "pools": {"p_ab": pool_state_fingerprint(pool)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_two_hop_exact_in() -> Tuple[JsonObj, Dict[str, PoolState]]:
    """One leg, two hops A->C->B (distinct pools)."""
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 10_000, 10_000, 0),
        "p_cb": _pool("p_cb", "C", "B", 10_000, 10_000, 0),
    }
    work = {k: replace(v) for k, v in pools.items()}
    leg_in = 200
    out1, work["p_ac"] = _replay_hop(work["p_ac"], "A", "C", leg_in)
    out2, work["p_cb"] = _replay_hop(work["p_cb"], "C", "B", out1)
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": leg_in,
        "amount_out": out2,
        "legs": [
            {
                "amount_in": leg_in,
                "amount_out": out2,
                "hops": [
                    {"pool_id": "p_ac", "asset_in": "A", "asset_out": "C", "amount_in": leg_in, "amount_out": out1},
                    {"pool_id": "p_cb", "asset_in": "C", "asset_out": "B", "amount_in": out1, "amount_out": out2},
                ],
            }
        ],
        "pools": {pid: pool_state_fingerprint(pools[pid]) for pid in sorted(pools)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_two_leg_two_hop_exact_in() -> Tuple[JsonObj, Dict[str, PoolState]]:
    """VALID 2-leg, multi-hop exact_in over SHARED pools (stateful reserve evolution)."""
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 10_000, 10_000, 0),
        "p_cb": _pool("p_cb", "C", "B", 10_000, 10_000, 0),
    }
    work = {k: replace(v) for k, v in pools.items()}
    legs: List[JsonObj] = []
    total_in = 0
    total_out = 0
    for leg_in in (200, 150):
        out1, work["p_ac"] = _replay_hop(work["p_ac"], "A", "C", leg_in)
        out2, work["p_cb"] = _replay_hop(work["p_cb"], "C", "B", out1)
        legs.append(
            {
                "amount_in": leg_in,
                "amount_out": out2,
                "hops": [
                    {"pool_id": "p_ac", "asset_in": "A", "asset_out": "C", "amount_in": leg_in, "amount_out": out1},
                    {"pool_id": "p_cb", "asset_in": "C", "asset_out": "B", "amount_in": out1, "amount_out": out2},
                ],
            }
        )
        total_in += leg_in
        total_out += out2
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": total_in,
        "amount_out": total_out,
        "legs": legs,
        "pools": {pid: pool_state_fingerprint(pools[pid]) for pid in sorted(pools)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_two_pool_split_exact_in() -> Tuple[JsonObj, Dict[str, PoolState]]:
    """2 legs, one hop each, over DISTINCT pools (independent legs)."""
    pools = {
        "p1": _pool("p1", "A", "B", 10_000, 10_000, 0),
        "p2": _pool("p2", "A", "B", 20_000, 20_000, 0),
    }
    legs: List[JsonObj] = []
    total_in = 0
    total_out = 0
    for pid, leg_in in (("p1", 100), ("p2", 100)):
        pool = pools[pid]
        out, _ = swap_exact_in_for_pool(
            pool, reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), amount_in=leg_in
        )
        legs.append(
            {
                "amount_in": leg_in,
                "amount_out": int(out),
                "hops": [
                    {"pool_id": pid, "asset_in": "A", "asset_out": "B", "amount_in": leg_in, "amount_out": int(out)}
                ],
            }
        )
        total_in += leg_in
        total_out += int(out)
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": total_in,
        "amount_out": total_out,
        "legs": legs,
        "pools": {pid: pool_state_fingerprint(pools[pid]) for pid in sorted(pools)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_stale_second_leg_exact_in() -> Tuple[JsonObj, Dict[str, PoolState]]:
    """2 legs on the SAME pool, second leg priced as if the first never ran.

    Leg 0 verifies (and mutates the verifier's working pool); leg 1 fails with
    ``hop_quote_mismatch``. Doubles as the no-op-on-reject witness: caller pools
    must be unchanged after the mid-route reject.
    """
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    pool = pools["p_ab"]
    amount_in_leg = 100
    out1, _ = swap_exact_in_for_pool(
        pool, reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), amount_in=amount_in_leg
    )
    leg = {
        "amount_in": amount_in_leg,
        "amount_out": int(out1),
        "hops": [
            {"pool_id": "p_ab", "asset_in": "A", "asset_out": "B", "amount_in": amount_in_leg, "amount_out": int(out1)}
        ],
    }
    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 2 * amount_in_leg,
        "amount_out": 2 * int(out1),
        "legs": [copy.deepcopy(leg), copy.deepcopy(leg)],
        "pools": {"p_ab": pool_state_fingerprint(pool)},
    }
    return {"body": body, "receipt_hash": receipt_hash(body)}, pools


def _base_exact_in_with_certificate() -> Tuple[JsonObj, Dict[str, PoolState]]:
    """Valid exact_in receipt that carries a canonical_route_certificate."""
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1_000, 1_000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1_000, 1_000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    assert "canonical_route_certificate" in receipt["body"]
    # Round-trip through json so the committed corpus is self-consistent.
    receipt = json.loads(json.dumps(receipt))
    return receipt, pools


# --------------------------------------------------------------------------- #
# Corpus construction
# --------------------------------------------------------------------------- #
def _case(
    case_id: str,
    category: str,
    stage: str,
    receipt: Any,
    pools: Dict[str, PoolState],
    expected_ok: bool,
    expected_err: str,
    *,
    expected_quote_epoch: int | None = None,
    cert_stub_ok: bool = False,
    pools_body_inconsistent: bool = False,
    assert_no_op: bool = False,
) -> JsonObj:
    return {
        "id": case_id,
        "category": category,
        "stage": stage,
        "receipt": receipt,
        "pools": _pools_to_json(pools),
        "expected_quote_epoch": expected_quote_epoch,
        "directives": {
            "cert_stub_ok": cert_stub_ok,
            "pools_body_inconsistent": pools_body_inconsistent,
            "assert_no_op": assert_no_op,
        },
        "expected_ok": expected_ok,
        "expected_err": expected_err,
    }


def build_corpus() -> List[JsonObj]:  # noqa: WPS213 - deliberately explicit & flat
    cases: List[JsonObj] = []

    # ---- VALID ----------------------------------------------------------- #
    r, p = _base_two_leg_two_hop_exact_in()
    cases.append(_case("valid_two_leg_two_hop_exact_in", "valid", "ok", r, p, True, "ok"))
    r, p = _base_single_hop_exact_in()
    cases.append(_case("valid_single_hop_exact_in", "valid", "ok", r, p, True, "ok"))
    r, p = _base_single_hop_exact_out()
    cases.append(_case("valid_single_hop_exact_out", "valid", "ok", r, p, True, "ok"))
    r, p = _base_exact_in_with_certificate()
    cases.append(_case("valid_exact_in_with_certificate", "valid", "ok", r, p, True, "ok"))

    # ---- receipt-level --------------------------------------------------- #
    cases.append(_case("bad_receipt_type", "single_fault", "receipt_type", ["not", "a", "receipt"], {}, False, "bad_receipt_type"))
    r, p = _base_single_hop_exact_in()
    r.pop("body", None)
    cases.append(_case("missing_body", "single_fault", "body", r, p, False, "missing_body"))

    # ---- precheck gate --------------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["schema"] = "zenodex/route_quote_receipt/v999"
    cases.append(_case("precheck_bad_schema", "single_fault", "precheck", _rehash(r), p, False, "bad_schema"))

    r, p = _base_single_hop_exact_in()
    r.pop("receipt_hash", None)
    cases.append(_case("precheck_missing_receipt_hash", "single_fault", "precheck", r, p, False, "missing_receipt_hash"))

    r, p = _base_single_hop_exact_in()
    r["receipt_hash"] = "0xdeadbeef"
    cases.append(_case("precheck_hash_mismatch", "single_fault", "precheck", r, p, False, "hash_mismatch"))

    r, p = _base_single_hop_exact_in()
    r["body"]["kind"] = "strange"
    cases.append(_case("precheck_bad_kind", "single_fault", "precheck", _rehash(r), p, False, "bad_kind"))

    r, p = _base_single_hop_exact_out()
    r["body"]["canonical_route_certificate"] = {"winner_quote": {}}
    cases.append(
        _case(
            "precheck_unexpected_canonical_route_certificate",
            "single_fault",
            "precheck",
            _rehash(r),
            p,
            False,
            "unexpected_canonical_route_certificate",
        )
    )

    r, p = _base_single_hop_exact_in()
    r["body"]["asset_out"] = r["body"]["asset_in"]
    cases.append(_case("precheck_bad_body_assets", "single_fault", "precheck", _rehash(r), p, False, "bad_body_assets"))

    r, p = _base_single_hop_exact_in()
    r["body"]["quote_epoch"] = -1
    cases.append(_case("precheck_bad_quote_epoch", "single_fault", "precheck", _rehash(r), p, False, "bad_quote_epoch"))

    r, p = _base_single_hop_exact_in()
    r["body"]["pools"] = []
    cases.append(_case("precheck_bad_pools", "single_fault", "precheck", _rehash(r), p, False, "bad_pools"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"] = []
    cases.append(_case("precheck_bad_legs", "single_fault", "precheck", _rehash(r), p, False, "bad_legs"))

    # ---- expected_quote_epoch binding ------------------------------------ #
    r, p = _base_single_hop_exact_in()
    cases.append(
        _case("epoch_bad_expected", "single_fault", "epoch", r, p, False, "bad_expected_quote_epoch", expected_quote_epoch=-1)
    )
    r, p = _base_single_hop_exact_in()
    cases.append(
        _case("epoch_missing_quote_epoch", "single_fault", "epoch", r, p, False, "missing_quote_epoch", expected_quote_epoch=7)
    )
    r, p = _base_single_hop_exact_in_with_epoch(7)
    cases.append(
        _case("epoch_quote_epoch_mismatch", "single_fault", "epoch", r, p, False, "quote_epoch_mismatch", expected_quote_epoch=8)
    )

    # ---- certificate gate (payload + winner-quote consistency) ----------- #
    r, p = _base_exact_in_with_certificate()
    cert = r["body"]["canonical_route_certificate"]
    cert["winner_index"] = int(cert["winner_index"]) + 1
    cases.append(
        _case(
            "cert_payload_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:certificate payload mismatch",
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"] = ["not", "a", "dict"]
    cases.append(
        _case(
            "cert_bad_type",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate_type",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"] = 7
    cases.append(
        _case(
            "cert_bad_winner",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate_winner",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"]["asset_in"] = "Z"
    cases.append(
        _case(
            "cert_asset_in_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "canonical_route_certificate_asset_in_mismatch",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"]["asset_out"] = "Z"
    cases.append(
        _case(
            "cert_asset_out_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "canonical_route_certificate_asset_out_mismatch",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"]["amount_in"] = (
        int(r["body"]["canonical_route_certificate"]["winner_quote"]["amount_in"]) + 1
    )
    cases.append(
        _case(
            "cert_amount_in_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "canonical_route_certificate_amount_in_mismatch",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"]["amount_out"] = (
        int(r["body"]["canonical_route_certificate"]["winner_quote"]["amount_out"]) + 1
    )
    cases.append(
        _case(
            "cert_amount_out_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "canonical_route_certificate_amount_out_mismatch",
            cert_stub_ok=True,
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["winner_quote"]["legs"] = []
    cases.append(
        _case(
            "cert_legs_mismatch",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "canonical_route_certificate_legs_mismatch",
            cert_stub_ok=True,
        )
    )

    # ---- pool-snapshot gate ---------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["pools"]["p_ab"] = 123
    cases.append(_case("snapshot_bad_pool_fingerprint", "single_fault", "snapshot", _rehash(r), p, False, "bad_pool_fingerprint"))

    r, p = _base_single_hop_exact_in()
    cases.append(_case("snapshot_missing_pool", "single_fault", "snapshot", r, {}, False, "missing_pool"))

    r, p = _base_single_hop_exact_in()
    p["p_ab"] = replace(p["p_ab"], reserve0=int(p["p_ab"].reserve0) + 1)
    cases.append(_case("snapshot_pool_snapshot_mismatch", "single_fault", "snapshot", r, p, False, "pool_snapshot_mismatch"))

    # ---- leg structure --------------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["legs"] = [7]
    cases.append(_case("leg_bad_leg", "single_fault", "leg", _rehash(r), p, False, "bad_leg"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"] = []
    cases.append(_case("leg_bad_hops", "single_fault", "leg", _rehash(r), p, False, "bad_hops"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["amount_in"] = 0
    cases.append(_case("leg_bad_leg_amounts", "single_fault", "leg", _rehash(r), p, False, "bad_leg_amounts"))

    # ---- hop structure --------------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"] = [7]
    cases.append(_case("hop_bad_hop", "single_fault", "hop_structure", _rehash(r), p, False, "bad_hop"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["pool_id"] = ""
    cases.append(_case("hop_bad_pool_id", "single_fault", "hop_structure", _rehash(r), p, False, "bad_pool_id"))

    r, p = _base_single_hop_exact_in()
    r["body"]["pools"] = {}
    cases.append(
        _case("hop_missing_pool_fingerprint", "single_fault", "hop_structure", _rehash(r), p, False, "missing_pool_fingerprint")
    )

    r, p = _base_single_hop_exact_in()
    cases.append(
        _case(
            "hop_missing_working_pool",
            "single_fault",
            "hop_structure",
            r,
            p,
            False,
            "missing_working_pool",
            pools_body_inconsistent=True,
        )
    )

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["asset_out"] = 7
    cases.append(_case("hop_bad_assets", "single_fault", "hop_structure", _rehash(r), p, False, "bad_assets"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["asset_in"] = "Z"
    cases.append(_case("hop_leg_asset_in_mismatch", "single_fault", "hop_structure", _rehash(r), p, False, "leg_asset_in_mismatch"))

    r, p = _base_two_hop_exact_in()
    r["body"]["legs"][0]["hops"][1]["asset_in"] = "Z"
    cases.append(
        _case("hop_hop_asset_chain_mismatch", "single_fault", "hop_structure", _rehash(r), p, False, "hop_asset_chain_mismatch")
    )

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["amount_in"] = 0
    cases.append(_case("hop_bad_hop_amounts", "single_fault", "hop_structure", _rehash(r), p, False, "bad_hop_amounts"))

    r, p = _base_two_hop_exact_in()
    r["body"]["legs"][0]["hops"][1]["amount_in"] = int(r["body"]["legs"][0]["hops"][0]["amount_out"]) + 1
    cases.append(_case("hop_hop_chain_mismatch", "single_fault", "hop_structure", _rehash(r), p, False, "hop_chain_mismatch"))

    # ---- hop replay (direction + quote semantics) ------------------------ #
    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["asset_in"] = "A"
    r["body"]["legs"][0]["hops"][0]["asset_out"] = "C"
    cases.append(_case("replay_bad_pool_direction", "single_fault", "hop_replay", _rehash(r), p, False, "bad_pool_direction"))

    r, p = _base_single_hop_exact_out()
    r["body"]["legs"][0]["hops"][0]["amount_out"] = 2_000
    r["body"]["legs"][0]["amount_out"] = 2_000
    r["body"]["amount_out"] = 2_000
    cases.append(_case("replay_hop_quote_error", "single_fault", "hop_replay", _rehash(r), p, False, "hop_quote_error"))

    r, p = _base_stale_second_leg_exact_in()
    cases.append(_case("replay_hop_quote_mismatch", "single_fault", "hop_replay", r, p, False, "hop_quote_mismatch"))

    # ---- leg summary ----------------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["asset_out"] = "C"
    cases.append(_case("leg_summary_asset_out_mismatch", "single_fault", "leg_summary", _rehash(r), p, False, "leg_asset_out_mismatch"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["amount_in"] = int(r["body"]["legs"][0]["amount_in"]) + 1
    cases.append(_case("leg_summary_amount_in_mismatch", "single_fault", "leg_summary", _rehash(r), p, False, "leg_amount_in_mismatch"))

    r, p = _base_single_hop_exact_in()
    r["body"]["legs"][0]["amount_out"] = int(r["body"]["legs"][0]["amount_out"]) + 1
    cases.append(_case("leg_summary_amount_out_mismatch", "single_fault", "leg_summary", _rehash(r), p, False, "leg_amount_out_mismatch"))

    # ---- totals ---------------------------------------------------------- #
    r, p = _base_single_hop_exact_in()
    r["body"]["amount_in"] = True
    cases.append(_case("totals_bad_body_amounts", "single_fault", "totals", _rehash(r), p, False, "bad_body_amounts"))

    r, p = _base_single_hop_exact_in()
    r["body"]["amount_out"] = int(r["body"]["amount_out"]) + 1
    cases.append(_case("totals_mismatch", "single_fault", "totals", _rehash(r), p, False, "totals_mismatch"))

    # ---- DOUBLE-FAULT ORDERING (pin precedence) -------------------------- #
    # precheck beats a later-stage fault.
    r, p = _base_single_hop_exact_in()
    r["body"]["schema"] = "zenodex/route_quote_receipt/v999"  # precheck: bad_schema
    r["body"]["legs"][0]["hops"][0]["amount_in"] = 0  # later: would be bad_hop_amounts
    cases.append(_case("df_precheck_beats_hop", "double_fault", "precheck<hop", _rehash(r), p, False, "bad_schema"))

    # leg[0] beats leg[1].
    r, p = _base_two_pool_split_exact_in()
    r["body"]["legs"][0]["amount_in"] = 0  # leg0: bad_leg_amounts
    r["body"]["legs"][1]["hops"] = []  # leg1: would be bad_hops
    cases.append(_case("df_leg0_beats_leg1", "double_fault", "leg0<leg1", _rehash(r), p, False, "bad_leg_amounts"))

    # hop[0] beats hop[1] within a leg.
    r, p = _base_two_hop_exact_in()
    r["body"]["legs"][0]["hops"][0]["amount_in"] = 0  # hop0: bad_hop_amounts
    r["body"]["legs"][0]["hops"][1]["asset_in"] = "Z"  # hop1: would be hop_asset_chain_mismatch
    cases.append(_case("df_hop0_beats_hop1", "double_fault", "hop0<hop1", _rehash(r), p, False, "bad_hop_amounts"))

    # snapshot gate beats a hop fault.
    r, p = _base_single_hop_exact_in()
    p["p_ab"] = replace(p["p_ab"], reserve0=int(p["p_ab"].reserve0) + 1)  # snapshot: pool_snapshot_mismatch
    r["body"]["legs"][0]["hops"][0]["amount_in"] = 0  # later: would be bad_hop_amounts
    cases.append(_case("df_snapshot_beats_hop", "double_fault", "snapshot<hop", _rehash(r), p, False, "pool_snapshot_mismatch"))

    # ---- NO-OP ON REJECT ------------------------------------------------- #
    r, p = _base_stale_second_leg_exact_in()
    cases.append(
        _case(
            "no_op_on_mid_route_reject",
            "no_op_on_reject",
            "hop_replay",
            r,
            p,
            False,
            "hop_quote_mismatch",
            assert_no_op=True,
        )
    )

    # ---- APPENDED (Codex review of 683d207b, finding 2): real-path -------- #
    # certificate payload passthrough sub-codes. These exercise the REAL
    # verify_exact_in_route_canonical_certificate_payload (NO monkeypatch),
    # whose extract step emits passthrough sub-codes BEFORE the local
    # certificate gate. Expected values were generated via the pristine-oracle
    # protocol: the UNMODIFIED ad96b74d module (git show
    # ad96b74d:src/core/quote_receipts.py, importlib-loaded under a separate
    # module name) produced these exact (ok, err) pairs and the refactored
    # module must reproduce them. Appended at the END so the committed fixture
    # diff is append-only (existing case objects stay byte-stable).
    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"] = "tampered-not-a-dict"
    cases.append(
        _case(
            "cert_real_payload_not_dict",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:certificate payload must be a dict",
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["candidates"] = []
    cases.append(
        _case(
            "cert_real_candidates_empty",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:certificate payload must include non-empty candidates",
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"].pop("candidates")
    cases.append(
        _case(
            "cert_real_candidates_missing",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:certificate payload must include non-empty candidates",
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["candidates"][0] = 7
    cases.append(
        _case(
            "cert_real_candidate_not_dict",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:certificate candidate must be a dict",
        )
    )

    r, p = _base_exact_in_with_certificate()
    r["body"]["canonical_route_certificate"]["candidates"][0]["quote"] = 7
    cases.append(
        _case(
            "cert_real_candidate_quote_not_dict",
            "single_fault",
            "certificate",
            _rehash(r),
            p,
            False,
            "bad_canonical_route_certificate:route quote payload must be a dict",
        )
    )

    return cases


# --------------------------------------------------------------------------- #
# Materialization + execution
# --------------------------------------------------------------------------- #
def _materialize(case: JsonObj) -> Tuple[Any, Dict[str, PoolState]]:
    receipt = copy.deepcopy(case["receipt"])
    pools = {pid: _pool_from_json(pj) for pid, pj in case["pools"].items()}
    if case["directives"].get("pools_body_inconsistent"):
        body = receipt["body"]
        body["pools"] = _InconsistentPools(body["pools"])
        receipt["receipt_hash"] = receipt_hash(body)
    return receipt, pools


def _run_case(case: JsonObj) -> Tuple[bool, str, Dict[str, str], Dict[str, str]]:
    receipt, pools = _materialize(case)
    before_fps = {pid: pool_state_fingerprint(pool) for pid, pool in pools.items()}
    kwargs: Dict[str, Any] = {"pools_by_id": pools}
    if case["expected_quote_epoch"] is not None:
        kwargs["expected_quote_epoch"] = case["expected_quote_epoch"]
    if case["directives"].get("cert_stub_ok"):
        with _cert_payload_stub():
            ok, err = verify_route_quote_receipt(receipt, **kwargs)
    else:
        ok, err = verify_route_quote_receipt(receipt, **kwargs)
    after_fps = {pid: pool_state_fingerprint(pool) for pid, pool in pools.items()}
    return ok, err, before_fps, after_fps


# --------------------------------------------------------------------------- #
# Tests
# --------------------------------------------------------------------------- #
def _load_corpus() -> List[JsonObj]:
    # Tolerate a missing fixture only during the bootstrap --regen run; pytest
    # always runs against the committed fixture.
    if not os.path.exists(CORPUS_PATH):
        return []
    with open(CORPUS_PATH, "r", encoding="utf-8") as fh:
        data = json.load(fh)
    assert isinstance(data, dict)
    assert data.get("schema") == "zenodex/quote_receipts_orchestration_characterization/v1"
    cases = data["cases"]
    assert isinstance(cases, list) and cases
    return cases


_CORPUS = _load_corpus()


@pytest.mark.parametrize("case", _CORPUS, ids=[c["id"] for c in _CORPUS])
def test_orchestration_characterization_reproduces_corpus(case: JsonObj) -> None:
    ok, err, before_fps, after_fps = _run_case(case)
    assert (ok, err) == (case["expected_ok"], case["expected_err"]), case["id"]
    if case["directives"].get("assert_no_op"):
        # No-op on reject: a mid-route reject must not mutate any caller pool.
        assert not ok
        assert before_fps == after_fps, f"{case['id']}: caller pools mutated by rejecting verify"


def test_corpus_covers_every_reachable_reject_code() -> None:
    """Guard: the committed corpus must lock every reachable reject code + 'ok'."""
    expected = {
        "ok",
        "bad_receipt_type",
        "missing_body",
        "bad_schema",
        "missing_receipt_hash",
        "hash_mismatch",
        "bad_kind",
        "unexpected_canonical_route_certificate",
        "bad_body_assets",
        "bad_quote_epoch",
        "bad_pools",
        "bad_legs",
        "bad_expected_quote_epoch",
        "missing_quote_epoch",
        "quote_epoch_mismatch",
        "bad_canonical_route_certificate:certificate payload mismatch",
        "bad_canonical_route_certificate:certificate payload must be a dict",
        "bad_canonical_route_certificate:certificate payload must include non-empty candidates",
        "bad_canonical_route_certificate:certificate candidate must be a dict",
        "bad_canonical_route_certificate:route quote payload must be a dict",
        "bad_canonical_route_certificate_type",
        "bad_canonical_route_certificate_winner",
        "canonical_route_certificate_asset_in_mismatch",
        "canonical_route_certificate_asset_out_mismatch",
        "canonical_route_certificate_amount_in_mismatch",
        "canonical_route_certificate_amount_out_mismatch",
        "canonical_route_certificate_legs_mismatch",
        "bad_pool_fingerprint",
        "missing_pool",
        "pool_snapshot_mismatch",
        "bad_leg",
        "bad_hops",
        "bad_leg_amounts",
        "bad_hop",
        "bad_pool_id",
        "missing_pool_fingerprint",
        "missing_working_pool",
        "bad_assets",
        "leg_asset_in_mismatch",
        "hop_asset_chain_mismatch",
        "bad_hop_amounts",
        "hop_chain_mismatch",
        "bad_pool_direction",
        "hop_quote_error",
        "hop_quote_mismatch",
        "leg_asset_out_mismatch",
        "leg_amount_in_mismatch",
        "leg_amount_out_mismatch",
        "bad_body_amounts",
        "totals_mismatch",
    }
    seen = {c["expected_err"] for c in _CORPUS}
    missing = expected - seen
    assert not missing, f"corpus missing reject codes: {sorted(missing)}"


def test_hop_pool_id_single_read_contract_under_adversarial_mapping() -> None:
    """Finding-1 regression (Codex review of 683d207b): pool_id is read ONCE.

    The hop is a dict subclass whose ``.get("pool_id")`` returns the valid pid
    but whose ``__getitem__`` raises. The pristine ad96b74d verifier read
    ``pool_id`` exactly once via ``.get`` (then assigned ``working_pools[pid]``
    through the local), so it ACCEPTED this receipt. Expected value below was
    generated from that pristine module via the pristine-oracle protocol
    (git show ad96b74d:src/core/quote_receipts.py, importlib-loaded):
    pristine -> (True, "ok"). The pre-fix refactor re-indexed
    ``working_pools[hop["pool_id"]]`` and RAISED RuntimeError here.

    Not part of the JSON corpus: a dict subclass is not JSON-representable.
    """
    receipt, pools = _base_single_hop_exact_in()
    hop = receipt["body"]["legs"][0]["hops"][0]
    receipt["body"]["legs"][0]["hops"][0] = _GetItemBombDict(hop)
    receipt["receipt_hash"] = receipt_hash(receipt["body"])

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)

    assert (ok, err) == (True, "ok")  # pristine-oracle value (ad96b74d)


def test_receipt_pools_map_never_indexed_under_adversarial_mapping() -> None:
    """Companion single-read lock for body['pools'] (audited: no re-read exists).

    The receipt's pools map is only iterated (``.items()``, ``for pid in``,
    ``in``) and never indexed, in both the pristine ad96b74d verifier and the
    refactored one. Expected value generated from the pristine module via the
    pristine-oracle protocol: pristine -> (True, "ok"). Locks that no future
    change introduces a ``pools[...]`` re-read on the receipt-supplied map.
    """
    receipt, pools = _base_single_hop_exact_in()
    receipt["body"]["pools"] = _GetItemBombDict(receipt["body"]["pools"])
    receipt["receipt_hash"] = receipt_hash(receipt["body"])

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)

    assert (ok, err) == (True, "ok")  # pristine-oracle value (ad96b74d)


def _write_corpus() -> int:
    cases = build_corpus()
    # Verify each case against the CURRENT function before committing it: this
    # asserts the corpus is internally consistent (the intended reject code is
    # actually produced) and pins the no-op guarantee.
    failures: List[str] = []
    for case in cases:
        ok, err, before_fps, after_fps = _run_case(case)
        if (ok, err) != (case["expected_ok"], case["expected_err"]):
            failures.append(f"{case['id']}: got {(ok, err)} expected {(case['expected_ok'], case['expected_err'])}")
        if case["directives"].get("assert_no_op") and before_fps != after_fps:
            failures.append(f"{case['id']}: caller pools mutated by rejecting verify")
    if failures:
        for line in failures:
            print(f"CORPUS BUILD FAILURE: {line}", file=sys.stderr)
        return 1
    payload = {
        "schema": "zenodex/quote_receipts_orchestration_characterization/v1",
        "description": (
            "Characterization corpus locking verify_route_quote_receipt's (ok, error_code) "
            "contract incl. reject ordering and no-op-on-reject. Regenerate with --regen."
        ),
        "case_count": len(cases),
        "cases": cases,
    }
    os.makedirs(os.path.dirname(CORPUS_PATH), exist_ok=True)
    with open(CORPUS_PATH, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True, ensure_ascii=False)
        fh.write("\n")
    print(f"wrote {len(cases)} cases -> {CORPUS_PATH}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    if "--regen" in sys.argv[1:]:
        raise SystemExit(_write_corpus())
    print("pass --regen to (re)write the corpus fixture", file=sys.stderr)
    raise SystemExit(2)
