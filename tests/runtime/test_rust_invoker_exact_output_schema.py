"""Rust invoker output-schema hardening regressions."""

from __future__ import annotations

import pytest

from src.runtime import rust_invoker
from src.runtime.rust_invoker import RustInvocationError


ROOT = "0x00"


def test_canonical_hash_rejects_extra_result_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": True, "hash": ROOT, "extra": 1}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="canonical-hash result: unexpected fields"):
        rust_invoker.canonical_domain_json_hash("label", {"x": 1}, version=1)


def test_canonical_hash_rejects_non_bool_ok(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": 1, "hash": ROOT}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="canonical-hash: result.ok must be a bool"):
        rust_invoker.canonical_domain_json_hash("label", {"x": 1}, version=1)


def test_canonical_hash_rejects_index_mismatch(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 1, "ok": True, "hash": ROOT}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="canonical-hash: result index mismatch"):
        rust_invoker.canonical_domain_json_hash("label", {"x": 1}, version=1)


def test_state_root_rejects_extra_result_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": True, "state_root": ROOT, "extra": 1}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="verify-state-root result: unexpected fields"):
        rust_invoker.state_root_hash({})


def test_state_root_rejects_non_bool_ok(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": 1, "state_root": ROOT}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="verify-state-root: result.ok must be a bool"):
        rust_invoker.state_root_hash({})


def test_state_root_rejects_index_mismatch(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [{"index": 1, "ok": True, "state_root": ROOT}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="verify-state-root: result index mismatch"):
        rust_invoker.state_root_hash({})


def test_replay_guard_rejects_extra_top_level_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "replay_guard",
            "accept": False,
            "reject_reason": "invalid_nonce",
            "receipt_hash": None,
            "receipt": None,
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_state_entries": [],
            "extra": 1,
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="replay-guard-admit output: unexpected fields"):
        rust_invoker.replay_guard_admit(state_entries=[], sender="alice", nonce=1)


def test_balance_op_rejects_extra_state_entry_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "balances",
            "accept": False,
            "reject_reason": "invalid_amount",
            "receipt_hash": None,
            "receipt": None,
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_state_entries": [{"pubkey": "alice", "asset": "zUSD", "amount": "1", "extra": 1}],
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="balance-op state entry: unexpected fields"):
        rust_invoker.balance_op(state_entries=[], tx={"kind": "credit", "recipient": "alice"})


def test_fee_route_rejects_extra_dust_entry_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "fee_router",
            "accept": False,
            "reject_reason": "negative_amount",
            "receipt_hash": None,
            "receipt": None,
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_accumulator": {
                "dust_by_stream": [
                    {
                        "source": "dex",
                        "asset": "zUSD",
                        "amount": "1",
                        "buyburn_remainder": "0",
                        "stakers_remainder": "0",
                        "reserve_remainder": "0",
                        "hosts_remainder": "0",
                        "extra": "metadata",
                    }
                ],
                "cum_buyburn": [],
                "cum_stakers": [],
                "cum_reserve": [],
                "cum_hosts": [],
            },
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="fee-route dust entry: unexpected fields"):
        rust_invoker.fee_route(accumulator={}, tx={})


def test_burn_rails_rejects_extra_result_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "burn_receipts",
            "initial_state_root": ROOT,
            "final_state_root": ROOT,
            "results": [
                {
                    "index": 0,
                    "accept": False,
                    "reject_reason": "bad_request",
                    "receipt_hash": None,
                    "pre_state_root": ROOT,
                    "post_state_root": ROOT,
                    "extra": 1,
                }
            ],
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="verify-burn-trace result: unexpected fields"):
        rust_invoker.burn_rails_verify(tx={})


def test_cpmm_op_rejects_extra_receipt_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "cpmm_settlement",
            "accept": True,
            "reject_reason": None,
            "receipt_hash": ROOT,
            "receipt": {
                "kind": "swap_exact_in",
                "zero_for_one": True,
                "amount_in": "1",
                "amount_out": "1",
                "fee_total": "0",
                "amount_out_quote": "1",
                "overdelivery_gap": "0",
                "gap_bps": "0",
                "new_reserve0": "2",
                "new_reserve1": "1",
                "extra": "metadata",
            },
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_pool": {"initialized": True, "reserve0": "2", "reserve1": "1", "fee_bps": "0"},
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="cpmm-op receipt: unexpected fields"):
        rust_invoker.cpmm_op(pool={}, tx={})


def test_zusd_op_rejects_extra_post_state_field(monkeypatch):
    post_state = {
        key: "0"
        for key in (
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
        )
    }
    post_state["oracle_seen"] = False
    post_state["extra"] = "metadata"

    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "kernel": "zusd",
            "accept": False,
            "reject_reason": "not_positive_int",
            "receipt_hash": None,
            "receipt": None,
            "pre_state_root": ROOT,
            "post_state_root": ROOT,
            "post_state": post_state,
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="zusd-op post_state: unexpected fields"):
        rust_invoker.zusd_op(state={}, tx={})


def test_perp_stateful_case_rejects_extra_output_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"version": 1, "results": [], "extra": "metadata"}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="advance-epoch output: unexpected fields"):
        rust_invoker.perp_stateful_case("advance-epoch", {})


def test_perp_stateful_case_rejects_extra_accept_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "results": [
                {
                    "index": 0,
                    "ok": True,
                    "now_epoch": "2",
                    "epoch_phase": "1",
                    "oracle_last_update_epoch": "2",
                    "extra": "metadata",
                }
            ],
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="advance-epoch result: unexpected fields"):
        rust_invoker.perp_stateful_case("advance-epoch", {})


def test_perp_stateful_case_rejects_extra_funding_account_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "version": 1,
            "results": [
                {
                    "index": 0,
                    "ok": True,
                    "accounts": [
                        {
                            "key": "acct",
                            "position_base": "1",
                            "collateral_quote": "1000",
                            "funding_paid_cumulative": "0",
                            "funding_last_applied_epoch": "1",
                            "extra": "metadata",
                        }
                    ],
                    "funding_rate_bps": "1",
                    "fee_pool_quote": "0",
                    "fee_income": "0",
                    "insurance_balance": "0",
                    "projected_net": "0",
                }
            ],
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="funding-auto account: unexpected fields"):
        rust_invoker.perp_stateful_case("funding-auto", {})


def test_perp_isolated_op_rejects_extra_accept_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {
            "accept": True,
            "post": {"quote_asset": "zUSD", "global_state": {}, "accounts": []},
            "effects": {},
            "extra": "metadata",
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="perp-isolated-op accepted output: unexpected fields"):
        rust_invoker.perp_isolated_op({})


def test_perp_isolated_op_rejects_extra_reject_field(monkeypatch):
    def malformed_invoke(*_args, **_kwargs):
        return {"accept": False, "reject_reason": "op_not_materialized", "effects": {}}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError, match="perp-isolated-op rejected output: unexpected fields"):
        rust_invoker.perp_isolated_op({})
