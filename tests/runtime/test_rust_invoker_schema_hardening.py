"""Fail-closed schema checks for Rust authority bridge outputs."""

from __future__ import annotations

import copy
import sys
from pathlib import Path
from typing import Any, Callable

import pytest

from src.runtime import rust_invoker

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
if str(TOOLS_RUNTIME) not in sys.path:
    sys.path.insert(0, str(TOOLS_RUNTIME))

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402

ROOT = "0x" + "00" * 32


def _fee_acc() -> dict[str, Any]:
    return {
        "dust_by_stream": [],
        "cum_buyburn": [],
        "cum_stakers": [],
        "cum_reserve": [],
        "cum_hosts": [],
    }


def _fee_receipt() -> dict[str, str]:
    return {
        "source": "dex",
        "asset": "0x" + "11" * 32,
        "amount": "100",
        "buyburn": "40",
        "stakers": "30",
        "reserve": "20",
        "hosts": "10",
        "dust": "0",
    }


def _cpmm_pool() -> dict[str, Any]:
    return {"initialized": True, "reserve0": "1000", "reserve1": "1000", "fee_bps": "30"}


def _cpmm_receipt() -> dict[str, Any]:
    return {
        "kind": "swap_exact_in",
        "zero_for_one": True,
        "amount_in": "10",
        "amount_out": "9",
        "fee_total": "1",
        "amount_out_quote": "9",
        "overdelivery_gap": "0",
        "gap_bps": "0",
        "new_reserve0": "1010",
        "new_reserve1": "991",
    }


def _zusd_state() -> dict[str, Any]:
    strings = {
        "now_epoch",
        "oracle_last_update_epoch",
        "price_e8",
        "price_pending_e8",
        "max_oracle_staleness_epochs",
        "collateral_e8",
        "debt_e8",
        "free_debt_e8",
        "sp_debt_e8",
        "sp_coll_e8",
        "protocol_collateral_e8",
        "protocol_revenue_zusd_cum_e8",
        "liquidator_compensation_collateral_cum_e8",
        "mcr_bps",
        "ccr_bps",
        "min_debt_open_e8",
        "max_debt_e8",
        "max_debt_supply_e8",
        "max_sp_coll_e8",
        "max_protocol_coll_e8",
        "base_rate_bps",
        "base_rate_last_epoch",
        "base_rate_decay_per_epoch_bps",
        "base_rate_borrow_bump_bps",
        "base_rate_redeem_bump_bps",
        "borrow_fee_floor_bps",
        "borrow_fee_max_bps",
        "redemption_fee_floor_bps",
        "redemption_fee_max_bps",
        "liquidation_gas_comp_fixed_collateral_e8",
        "liquidation_gas_comp_bps",
    }
    out: dict[str, Any] = {key: "0" for key in strings}
    out["oracle_seen"] = True
    return out


def _accepted_outputs() -> list[tuple[str, dict[str, Any], Callable[[], Any]]]:
    return [
        (
            "canonical",
            {"version": 1, "results": [{"index": 0, "ok": True, "hash": ROOT}]},
            lambda: rust_invoker.canonical_domain_json_hash("label", {}),
        ),
        (
            "state_root",
            {"version": 1, "results": [{"index": 0, "ok": True, "state_root": ROOT}]},
            lambda: rust_invoker.state_root_hash({}),
        ),
        (
            "replay_guard",
            {
                "version": 1,
                "kernel": "replay_guard",
                "accept": True,
                "reject_reason": None,
                "receipt_hash": ROOT,
                "receipt": {"sender": "0x" + "aa" * 48, "nonce": 1, "prev_nonce": 0},
                "pre_state_root": ROOT,
                "post_state_root": ROOT,
                "post_state_entries": [{"sender": "0x" + "aa" * 48, "last_nonce": 1}],
            },
            lambda: rust_invoker.replay_guard_admit(state_entries=[], sender="0x" + "aa" * 48, nonce=1),
        ),
        (
            "balance",
            {
                "version": 1,
                "kernel": "balances",
                "accept": True,
                "reject_reason": None,
                "receipt_hash": ROOT,
                "receipt": {
                    "kind": "credit",
                    "sender": None,
                    "recipient": "0x" + "aa" * 48,
                    "asset": "0x" + "11" * 32,
                    "amount": "1",
                },
                "pre_state_root": ROOT,
                "post_state_root": ROOT,
                "post_state_entries": [{"pubkey": "0x" + "aa" * 48, "asset": "0x" + "11" * 32, "amount": "1"}],
            },
            lambda: rust_invoker.balance_op(
                state_entries=[],
                tx={"kind": "credit", "recipient": "0x" + "aa" * 48, "asset": "0x" + "11" * 32, "amount": 1},
            ),
        ),
        (
            "fee",
            {
                "version": 1,
                "kernel": "fee_router",
                "accept": True,
                "reject_reason": None,
                "receipt_hash": ROOT,
                "receipt": _fee_receipt(),
                "pre_state_root": ROOT,
                "post_state_root": ROOT,
                "post_accumulator": _fee_acc(),
            },
            lambda: rust_invoker.fee_route(accumulator={}, tx={}),
        ),
        (
            "burn",
            {
                "version": 1,
                "kernel": "burn_receipts",
                "initial_state_root": ROOT,
                "final_state_root": ROOT,
                "results": [
                    {
                        "index": 0,
                        "accept": True,
                        "reject_reason": None,
                        "receipt_hash": ROOT,
                        "pre_state_root": ROOT,
                        "post_state_root": ROOT,
                    }
                ],
            },
            lambda: rust_invoker.burn_rails_verify(tx={}),
        ),
        (
            "cpmm",
            {
                "version": 1,
                "kernel": "cpmm_settlement",
                "accept": True,
                "reject_reason": None,
                "receipt_hash": ROOT,
                "receipt": _cpmm_receipt(),
                "pre_state_root": ROOT,
                "post_state_root": ROOT,
                "post_pool": _cpmm_pool(),
            },
            lambda: rust_invoker.cpmm_op(pool={}, tx={}),
        ),
        (
            "perp_math",
            {"version": 1, "results": [{"index": 0, "ok": True, "value": "1"}]},
            lambda: rust_invoker.perp_math_eval({"op": "pnl_quote"}),
        ),
        (
            "perp_stateful_case",
            {"version": 1, "results": [{"index": 0, "ok": True}]},
            lambda: rust_invoker.perp_stateful_case("advance-epoch", {}),
        ),
        (
            "zusd",
            {
                "version": 1,
                "kernel": "zusd",
                "accept": True,
                "reject_reason": None,
                "receipt_hash": ROOT,
                "receipt": {"tag": "advance_epoch"},
                "pre_state_root": ROOT,
                "post_state_root": ROOT,
                "post_state": _zusd_state(),
            },
            lambda: rust_invoker.zusd_op(state={}, tx={}),
        ),
    ]


@pytest.mark.parametrize("label,output,call", _accepted_outputs())
def test_trusted_core_invokers_reject_extra_top_level_fields(monkeypatch, label, output, call):
    mutated = copy.deepcopy(output)
    mutated["debug"] = label
    monkeypatch.setattr(rust_invoker, "invoke", lambda *args, **kwargs: mutated)

    with pytest.raises(rust_invoker.RustInvocationError, match="unexpected fields"):
        call()


def test_trusted_core_invokers_reject_extra_nested_fields(monkeypatch):
    cases: list[tuple[dict[str, Any], Callable[[], Any]]] = []
    for label, output, call in _accepted_outputs():
        mutated = copy.deepcopy(output)
        if label == "replay_guard":
            mutated["receipt"]["debug"] = "x"
        elif label == "balance":
            mutated["post_state_entries"][0]["debug"] = "x"
        elif label == "fee":
            mutated["post_accumulator"]["dust_by_stream"] = [
                {
                    "source": "dex",
                    "asset": "0x" + "11" * 32,
                    "amount": "0",
                    "buyburn_remainder": "0",
                    "stakers_remainder": "0",
                    "reserve_remainder": "0",
                    "hosts_remainder": "0",
                    "debug": "x",
                }
            ]
        elif label == "burn":
            mutated["results"][0]["debug"] = "x"
        elif label == "cpmm":
            mutated["post_pool"]["debug"] = "x"
        elif label == "zusd":
            mutated["post_state"]["debug"] = "x"
        else:
            continue
        cases.append((mutated, call))

    for mutated, call in cases:
        monkeypatch.setattr(rust_invoker, "invoke", lambda *args, _mutated=mutated, **kwargs: _mutated)
        with pytest.raises(rust_invoker.RustInvocationError, match="unexpected fields"):
            call()


def test_state_root_invoker_rejects_uncommitted_extra_sections(monkeypatch):
    # REVIEW [B -> A-]: Rust verify-state-root previously ignored unknown state
    # sections, so `{}` and `{"perps": ...}` produced the same commitment. The
    # invoker must fail closed when caller input carries state the v5 root does
    # not explicitly commit.
    try:
        rust_bin = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust runtime unavailable: {exc}")
    monkeypatch.setenv("ZENODEX_RUNTIME_BIN", str(rust_bin))

    with pytest.raises(rust_invoker.RustInvocationError, match="unknown_field:perps"):
        rust_invoker.state_root_hash({"perps": {"position": "uncommitted"}})


def test_zusd_invoker_forwards_production_oracle_gate_fields(monkeypatch):
    captured: dict[str, Any] = {}

    def fake_invoke(subcommand, request, **kwargs):
        captured["subcommand"] = subcommand
        captured["request"] = request
        return {
            "version": 1,
            "kernel": "zusd",
            "accept": False,
            "reject_reason": "oracle_authorization_not_accepted",
            "receipt_hash": None,
            "receipt": None,
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_state": _zusd_state(),
        }

    facts = {
        "oracle_authorization_ok": False,
        "query_id": "sha256:" + "11" * 32,
        "action_kind": "mint",
        "runtime_value_e8": 100_000_000,
    }
    monkeypatch.setattr(rust_invoker, "invoke", fake_invoke)

    out = rust_invoker.zusd_op(
        state={},
        tx={"kind": "mint_zusd", "amount_e8": 20_000_000_000},
        facts=facts,
        require_oracle_authorization=True,
    )

    assert out["accept"] is False
    assert captured["subcommand"] == "zusd-op"
    assert captured["request"]["facts"] == facts
    assert captured["request"]["require_oracle_authorization"] is True
