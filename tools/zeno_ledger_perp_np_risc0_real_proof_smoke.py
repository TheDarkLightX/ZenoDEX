#!/usr/bin/env python3
"""Run real RISC0 proof smokes for the N-party perps clearinghouse transition.

The smoke builds the unified `tau-state-proof-risc0-cli` method with
`RISC0_FORCE_BUILD=1`, proves dynamic 4+ wallet perps epochs, verifies the
receipt through the strict verifier command, and runs fail-closed negative
cases. Python independently re-derives the snapshot app hashes fed into the
request and cross-checks verifier-bound guest metadata; the report remains
scoped evidence, not a production security claim.

This remains evidence for a scoped circuit surface:
`risc0.zenodex_perps_np_transition.v1`. It does not flip
`production_security_claim`.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

BPS_SCALE = 10_000
PROOF_TYPE = "risc0.zenodex_perps_np_transition.v1"

CHAIN_ID = "zenodex-local-risc0-smoke-1"
MARKET_ID = "perp:chnp:ETH-PERP"

PRE_ROOT_DOMAIN = b"zenodex.perps_np.pre_state_root.v1:"
POST_ROOT_DOMAIN = b"zenodex.perps_np.post_state_root.v1:"


def _hex(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _u32(n: int) -> bytes:
    return n.to_bytes(4, "big", signed=False)


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "big", signed=False)


def _i64(n: int) -> bytes:
    if not (-(2**63) <= n < 2**63):
        raise ValueError(f"value out of i64 range: {n}")
    return n.to_bytes(8, "big", signed=True)


def _i32(n: int) -> bytes:
    if not (-(2**31) <= n < 2**31):
        raise ValueError(f"value out of i32 range: {n}")
    return n.to_bytes(4, "big", signed=True)


def _i128(n: int) -> bytes:
    if not (-(2**127) <= n < 2**127):
        raise ValueError(f"value out of i128 range: {n}")
    return n.to_bytes(16, "big", signed=True)


def _write_str(h: "hashlib._Hash", value: str) -> None:
    raw = value.encode("utf-8")
    h.update(_u32(len(raw)))
    h.update(raw)


def _hash_current_params(h: "hashlib._Hash", params: dict[str, int]) -> None:
    h.update(_u32(int(params["initial_margin_bps"])))
    h.update(_u32(int(params["maintenance_margin_bps"])))
    h.update(_u32(int(params["depeg_buffer_bps"])))
    h.update(_u32(int(params["liquidation_penalty_bps"])))
    h.update(_u32(int(params["max_oracle_move_bps"])))
    h.update(_i32(int(params["funding_cap_bps"])))
    h.update(_i128(int(params["max_position_abs"])))
    h.update(_i128(int(params["min_notional_for_bounty_e8"])))


def _hash_current_account(h: "hashlib._Hash", account: dict[str, Any]) -> None:
    _write_str(h, str(account["pubkey"]))
    h.update(_i128(int(account["position_base"])))
    h.update(_i128(int(account["entry_price_e8"])))
    h.update(_i128(int(account["collateral_e8"])))
    h.update(_i128(int(account["funding_paid_cum_e8"])))
    h.update(_u64(int(account["nonce"])))


def _hash_current_intent(h: "hashlib._Hash", intent: dict[str, Any]) -> None:
    _write_str(h, str(intent["pubkey"]))
    h.update(_i128(int(intent["target_base"])))
    h.update(_i128(int(intent.get("limit_price_e8", 0))))
    h.update(_i128(int(intent.get("min_fill_base", 0))))
    h.update(_u64(int(intent.get("expiry_epoch", 1 << 62))))
    h.update(_u64(int(intent["nonce"])))


def _canonical_current_intents(intents: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted((copy.deepcopy(i) for i in intents), key=lambda i: (str(i["pubkey"]), int(i["nonce"])))


def _current_snapshot_hash(snapshot: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.perps_np.snapshot.v1:")
    h.update(_u32(int(snapshot["version"])))
    _write_str(h, str(snapshot["market_id"]))
    _write_str(h, str(snapshot["collateral_asset"]))
    h.update(_i128(int(snapshot["index_price_e8"])))
    _hash_current_params(h, snapshot["params"])
    accounts = sorted(snapshot.get("accounts", []), key=lambda a: str(a["pubkey"]))
    h.update(_u32(len(accounts)))
    for account in accounts:
        _hash_current_account(h, account)
    pending = _canonical_current_intents(snapshot.get("pending_intents", []))
    h.update(_u32(len(pending)))
    for intent in pending:
        _hash_current_intent(h, intent)
    h.update(_u64(int(snapshot["now_epoch"])))
    h.update(_i128(int(snapshot["fee_pool_e8"])))
    h.update(_i128(int(snapshot["insurance_e8"])))
    h.update(_i128(int(snapshot["insurance_ext_e8"])))
    h.update(_i128(int(snapshot["claims_paid_e8"])))
    h.update(_i128(int(snapshot["net_deposited_e8"])))
    return h.hexdigest()


def _participant_set_hash(chain_id: str, market_id: str, accounts: list[dict[str, Any]]) -> str:
    del chain_id, market_id
    h = hashlib.sha256()
    h.update(b"zenodex.participant_set.v1:")
    participants = sorted({str(account["pubkey"]) for account in accounts})
    h.update(_u32(len(participants)))
    for pubkey in participants:
        _write_str(h, pubkey)
    return h.hexdigest()


def _state_root(
    domain: bytes,
    *,
    chain_id: str,
    market_id: str,
    now_epoch: int,
    index_price_e8: int,
    net_deposited_e8: int,
    fee_pool_e8: int,
    insurance_e8: int,
    insurance_ext_e8: int,
    claims_paid_e8: int,
    accounts: list[dict[str, Any]],
) -> str:
    h = hashlib.sha256()
    h.update(domain)
    _write_str(h, chain_id)
    _write_str(h, market_id)
    h.update(_u64(now_epoch))
    h.update(_i64(index_price_e8))
    h.update(_i64(net_deposited_e8))
    h.update(_i64(fee_pool_e8))
    h.update(_i64(insurance_e8))
    h.update(_i64(insurance_ext_e8))
    h.update(_i64(claims_paid_e8))
    h.update(_u32(len(accounts)))
    for account in accounts:
        _write_str(h, str(account["pubkey"]))
        h.update(_i64(int(account["position_base"])))
        h.update(_i64(int(account["entry_price_e8"])))
        h.update(_i64(int(account["collateral_e8"])))
        h.update(_i64(int(account["funding_paid_cum_e8"])))
        h.update(_u64(int(account["nonce"])))
    return h.hexdigest()


def _receipts_root(receipts: list[dict[str, Any]]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.perps_np.receipts.v1:")
    h.update(_u32(len(receipts)))
    for receipt in receipts:
        _write_str(h, str(receipt["pubkey"]))
        h.update(_u64(int(receipt["nonce"])))
        _write_str(h, "rejected" if receipt["rejected"] else "filled")
        h.update(_i128(int(receipt["delta"])))
        if receipt["rejected"]:
            h.update(bytes([1]))
            _write_str(h, str(receipt["reject_code"]))
        else:
            h.update(bytes([0]))
    return h.hexdigest()


def _state_delta_hash(
    *,
    chain_id: str,
    market_id: str,
    pre_state_root: str,
    post_state_root: str,
    operation_hash: str,
    receipts_root: str,
) -> str:
    del chain_id, market_id, operation_hash, receipts_root
    h = hashlib.sha256()
    h.update(b"zenodex.state_delta.v1:")
    h.update(bytes.fromhex(pre_state_root))
    h.update(bytes.fromhex(post_state_root))
    return h.hexdigest()


def _params() -> dict[str, int]:
    return {
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 500,
        "max_oracle_move_bps": 1_000,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000,
        "min_notional_for_bounty_e8": 0,
    }


def _account(pubkey: str, pos: int, entry: int, collateral: int, nonce: int = 0) -> dict[str, Any]:
    return {
        "pubkey": pubkey,
        "position_base": pos,
        "entry_price_e8": entry,
        "collateral_e8": collateral,
        "funding_paid_cum_e8": 0,
        "nonce": nonce,
    }


def _intent(
    pubkey: str,
    target: int,
    *,
    nonce: int = 1,
    price: int = 100,
    expiry: int = 10,
    min_fill: int = 0,
) -> dict[str, Any]:
    return {
        "pubkey": pubkey,
        "target_base": target,
        "limit_price_e8": price,
        "min_fill_base": min_fill,
        "expiry_epoch": expiry,
        "nonce": nonce,
    }


def _margin_req(position: int, price: int, margin_bps: int) -> int:
    return (abs(position) * price * margin_bps + BPS_SCALE - 1) // BPS_SCALE


def _increases_risk(current: int, target: int) -> bool:
    return (current > 0 and target < 0) or (current < 0 and target > 0) or abs(target) > abs(current)


def _settle_price(clearing: int, index: int, max_move_bps: int) -> int:
    diff = abs(clearing - index)
    if diff * BPS_SCALE <= max_move_bps * index:
        return clearing
    max_delta = (max_move_bps * index + BPS_SCALE - 1) // BPS_SCALE
    return index + max_delta if clearing > index else index - max_delta


def _maintenance_req(position: int, price: int, params: dict[str, int]) -> int:
    bps = int(params["maintenance_margin_bps"]) + int(params["depeg_buffer_bps"])
    return (abs(position) * price * bps + BPS_SCALE - 1) // BPS_SCALE


def _liq_penalty(notional: int, collateral: int, params: dict[str, int]) -> int:
    if notional < int(params["min_notional_for_bounty_e8"]):
        return 0
    raw = (notional * int(params["liquidation_penalty_bps"])) // BPS_SCALE
    return min(raw, max(collateral, 0))


def _apply_liquidation_adl(
    accounts: list[dict[str, Any]],
    pnl_map: list[int],
    *,
    price: int,
    params: dict[str, int],
    fee_pool_e8: int,
    insurance_e8: int,
    claims_paid_e8: int,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    liquidated = [
        idx
        for idx, account in enumerate(accounts)
        if int(account["position_base"]) != 0
        and int(account["collateral_e8"]) < _maintenance_req(int(account["position_base"]), price, params)
    ]
    if not liquidated:
        if any(int(a["collateral_e8"]) < 0 for a in accounts):
            raise ValueError("settle would drive collateral negative")
        return accounts, {
            "fee_pool_e8": fee_pool_e8,
            "insurance_e8": insurance_e8,
            "claims_paid_e8": claims_paid_e8,
        }

    for idx in liquidated:
        account = accounts[idx]
        penalty = _liq_penalty(abs(int(account["position_base"])) * price, int(account["collateral_e8"]), params)
        account["collateral_e8"] = int(account["collateral_e8"]) - penalty
        fee_pool_e8 += penalty

    bad_debt = sum(-int(accounts[idx]["collateral_e8"]) for idx in liquidated if int(accounts[idx]["collateral_e8"]) < 0)
    d_ins = min(bad_debt, insurance_e8)
    residual = bad_debt - d_ins
    winners = sorted(
        (
            (idx, min(int(pnl_map[idx]), int(accounts[idx]["collateral_e8"])))
            for idx in range(len(accounts))
            if idx not in liquidated and int(pnl_map[idx]) > 0 and int(accounts[idx]["collateral_e8"]) > 0
        ),
        key=lambda item: (-item[1], str(accounts[item[0]]["pubkey"])),
    )
    budget = sum(profit for _, profit in winners)
    if residual > budget:
        raise ValueError("np settle insolvent")
    insurance_e8 -= d_ins
    claims_paid_e8 += d_ins

    for idx in liquidated:
        if int(accounts[idx]["collateral_e8"]) < 0:
            accounts[idx]["collateral_e8"] = 0
    if residual > 0:
        weights = [(rank, profit) for rank, (_, profit) in enumerate(winners)]
        haircuts = _ration(weights, residual)
        for rank, haircut in haircuts:
            account_idx = winners[rank][0]
            accounts[account_idx]["collateral_e8"] = int(accounts[account_idx]["collateral_e8"]) - haircut

    net_liq = sum(int(accounts[idx]["position_base"]) for idx in liquidated)
    for idx in liquidated:
        accounts[idx]["position_base"] = 0
        accounts[idx]["entry_price_e8"] = 0

    if net_liq != 0:
        want_short_side = net_liq > 0
        candidates = [
            idx
            for idx, account in enumerate(accounts)
            if idx not in liquidated
            and int(account["position_base"]) != 0
            and (int(account["position_base"]) < 0) == want_short_side
        ]
        candidates.sort(key=lambda idx: (-int(pnl_map[idx]), str(accounts[idx]["pubkey"])))
        remaining = abs(net_liq)
        step = 1 if net_liq > 0 else -1
        for idx in candidates:
            if remaining == 0:
                break
            take = min(abs(int(accounts[idx]["position_base"])), remaining)
            new_pos = int(accounts[idx]["position_base"]) + step * take
            accounts[idx]["position_base"] = new_pos
            accounts[idx]["entry_price_e8"] = 0 if new_pos == 0 else price
            remaining -= take
        if remaining != 0:
            raise ValueError("ADL could not rebalance")

    if any(int(a["collateral_e8"]) < 0 for a in accounts):
        raise ValueError("settle would drive collateral negative")
    return accounts, {
        "fee_pool_e8": fee_pool_e8,
        "insurance_e8": insurance_e8,
        "claims_paid_e8": claims_paid_e8,
    }


def _ration(weights: list[tuple[int, int]], volume: int) -> list[tuple[int, int]]:
    total = sum(weight for _, weight in weights)
    out: list[tuple[int, int]] = []
    remainders: list[tuple[int, int]] = []
    allocated = 0
    for idx, weight in weights:
        product = weight * volume
        base = product // total
        allocated += base
        out.append((idx, base))
        remainders.append((product - base * total, idx))
    leftover = volume - allocated
    for _, winner in sorted(remainders, key=lambda item: (-item[0], item[1]))[:leftover]:
        out = [(idx, value + 1 if idx == winner else value) for idx, value in out]
    return out


def _ration_net_zero(desired: list[int]) -> list[int]:
    buys = [(idx, value) for idx, value in enumerate(desired) if value > 0]
    sells = [(idx, -value) for idx, value in enumerate(desired) if value < 0]
    volume = min(sum(value for _, value in buys), sum(value for _, value in sells))
    out = [0 for _ in desired]
    if volume == 0:
        return out
    for idx, amount in _ration(buys, volume):
        out[idx] = amount
    for idx, amount in _ration(sells, volume):
        out[idx] = -amount
    return out


def _simulate_match(
    accounts: list[dict[str, Any]],
    intents: list[dict[str, Any]],
    *,
    price: int,
    now_epoch: int,
    params: dict[str, int],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    next_accounts = [copy.deepcopy(a) for a in accounts]
    account_by_pk = {str(account["pubkey"]): idx for idx, account in enumerate(next_accounts)}
    sorted_intents = sorted((copy.deepcopy(i) for i in intents), key=lambda i: (str(i["pubkey"]), int(i["nonce"])))
    survivors: list[tuple[dict[str, Any], int, int]] = []
    receipts: dict[tuple[str, int], dict[str, Any]] = {}

    def emit(intent: dict[str, Any], delta: int, rejected: bool, code: str) -> None:
        # Rust uses BTreeMap<(pubkey, nonce), receipt>; duplicate nonce
        # rejects collapse to one deterministic receipt for that key.
        receipts[(str(intent["pubkey"]), int(intent["nonce"]))] = _receipt(intent, delta, rejected, code)

    cursor = 0
    while cursor < len(sorted_intents):
        pubkey = str(sorted_intents[cursor]["pubkey"])
        start = cursor
        while cursor < len(sorted_intents) and str(sorted_intents[cursor]["pubkey"]) == pubkey:
            cursor += 1
        if pubkey not in account_by_pk:
            for intent in sorted_intents[start:cursor]:
                emit(intent, 0, True, "REJ_ACCOUNT")
            continue
        account_index = account_by_pk[pubkey]
        account = next_accounts[account_index]
        chosen: dict[str, Any] | None = None
        nonce_counts: dict[int, int] = {}
        for intent in sorted_intents[start:cursor]:
            nonce_counts[int(intent["nonce"])] = nonce_counts.get(int(intent["nonce"]), 0) + 1
        nonce_cursor = int(account["nonce"])
        for intent in sorted_intents[start:cursor]:
            nonce = int(intent["nonce"])
            if nonce_counts[nonce] > 1:
                emit(intent, 0, True, "REJ_DUP_NONCE")
                continue
            if nonce != nonce_cursor + 1:
                emit(intent, 0, True, "REJ_BAD_NONCE")
                continue
            nonce_cursor = nonce
            if int(intent["expiry_epoch"]) < now_epoch:
                emit(intent, 0, True, "REJ_EXPIRED")
                continue
            target = int(intent["target_base"])
            if abs(target) > int(params["max_position_abs"]):
                emit(intent, 0, True, "REJ_POS_BOUND")
                continue
            desired = target - int(account["position_base"])
            if int(intent["limit_price_e8"]) and desired:
                limit = int(intent["limit_price_e8"])
                if desired > 0 and price > limit:
                    emit(intent, 0, True, "REJ_PRICE")
                    continue
                if desired < 0 and price < limit:
                    emit(intent, 0, True, "REJ_PRICE")
                    continue
            if _increases_risk(int(account["position_base"]), target):
                req = _margin_req(target, price, int(params["initial_margin_bps"]))
                if int(account["collateral_e8"]) < req:
                    emit(intent, 0, True, "REJ_MARGIN")
                    continue
            if chosen is not None:
                emit(chosen, 0, True, "REJ_SUPERSEDED")
            chosen = intent
        if chosen is not None:
            desired = int(chosen["target_base"]) - int(account["position_base"])
            survivors.append((chosen, desired, account_index))

    revoked = [False for _ in survivors]
    while True:
        desired_pass = [0 if revoked[idx] else desired for idx, (_, desired, _) in enumerate(survivors)]
        deltas = _ration_net_zero(desired_pass)
        changed = False
        for idx, (intent, _, _) in enumerate(survivors):
            if revoked[idx]:
                continue
            if 0 < abs(deltas[idx]) < int(intent["min_fill_base"]):
                revoked[idx] = True
                changed = True
        if not changed:
            break

    for idx, (intent, _, account_index) in enumerate(survivors):
        delta = 0 if revoked[idx] else deltas[idx]
        account = next_accounts[account_index]
        new_position = int(account["position_base"]) + delta
        if _increases_risk(int(account["position_base"]), new_position):
            req = _margin_req(new_position, price, int(params["initial_margin_bps"]))
            if int(account["collateral_e8"]) < req:
                emit(intent, 0, True, "REJ_INVARIANT")
                continue
        account["position_base"] = new_position
        account["entry_price_e8"] = 0 if new_position == 0 else price
        account["nonce"] = max(int(account["nonce"]), int(intent["nonce"]))
        emit(intent, delta, False, "")

    next_accounts.sort(key=lambda a: str(a["pubkey"]))
    ordered_receipts = sorted(receipts.values(), key=lambda r: (str(r["pubkey"]), int(r["nonce"])))
    return next_accounts, ordered_receipts


def _receipt(intent: dict[str, Any], delta: int, rejected: bool, code: str) -> dict[str, Any]:
    return {
        "pubkey": str(intent["pubkey"]),
        "nonce": int(intent["nonce"]),
        "delta": delta,
        "rejected": rejected,
        "reject_code": code,
    }


def _complete_input(
    *,
    accounts: list[dict[str, Any]],
    intents: list[dict[str, Any]],
    now_epoch: int = 1,
    index_price: int = 100,
    clearing_price: int = 100,
    fee_pool_e8: int = 0,
    insurance_ext_e8: int = 0,
    claims_paid_e8: int = 0,
    net_deposited_override: int | None = None,
    params_override: dict[str, int] | None = None,
) -> dict[str, Any]:
    params = _params()
    if params_override:
        params.update(params_override)
    pre_accounts = sorted((copy.deepcopy(a) for a in accounts), key=lambda a: str(a["pubkey"]))
    insurance_e8 = insurance_ext_e8 - claims_paid_e8
    computed_net_deposited_e8 = (
        sum(int(a["collateral_e8"]) for a in pre_accounts)
        + fee_pool_e8
        + insurance_e8
        - insurance_ext_e8
    )
    net_deposited_e8 = (
        computed_net_deposited_e8 if net_deposited_override is None else int(net_deposited_override)
    )
    participant_hash = _participant_set_hash(CHAIN_ID, MARKET_ID, pre_accounts)
    pre_root = _state_root(
        PRE_ROOT_DOMAIN,
        chain_id=CHAIN_ID,
        market_id=MARKET_ID,
        now_epoch=now_epoch,
        index_price_e8=index_price,
        net_deposited_e8=net_deposited_e8,
        fee_pool_e8=fee_pool_e8,
        insurance_e8=insurance_e8,
        insurance_ext_e8=insurance_ext_e8,
        claims_paid_e8=claims_paid_e8,
        accounts=pre_accounts,
    )

    settle = _settle_price(clearing_price, index_price, int(params["max_oracle_move_bps"]))
    settled = [copy.deepcopy(a) for a in pre_accounts]
    price_delta = settle - index_price
    pnl_map: list[int] = []
    for account in settled:
        pnl = int(account["position_base"]) * price_delta
        pnl_map.append(pnl)
        account["collateral_e8"] = int(account["collateral_e8"]) + pnl
        account["entry_price_e8"] = 0 if int(account["position_base"]) == 0 else settle
    settled, post_ledgers = _apply_liquidation_adl(
        settled,
        pnl_map,
        price=settle,
        params=params,
        fee_pool_e8=fee_pool_e8,
        insurance_e8=insurance_e8,
        claims_paid_e8=claims_paid_e8,
    )
    post_accounts, receipts = _simulate_match(
        settled,
        intents,
        price=settle,
        now_epoch=now_epoch + 1,
        params=params,
    )
    post_root = _state_root(
        POST_ROOT_DOMAIN,
        chain_id=CHAIN_ID,
        market_id=MARKET_ID,
        now_epoch=now_epoch + 1,
        index_price_e8=settle,
        net_deposited_e8=net_deposited_e8,
        fee_pool_e8=post_ledgers["fee_pool_e8"],
        insurance_e8=post_ledgers["insurance_e8"],
        insurance_ext_e8=insurance_ext_e8,
        claims_paid_e8=post_ledgers["claims_paid_e8"],
        accounts=post_accounts,
    )
    receipts_root = _receipts_root(receipts)
    operation_hash = _hex("perps-np-smoke-operation")
    current_pre_snapshot = {
        "version": 1,
        "market_id": MARKET_ID,
        "collateral_asset": "zUSD",
        "index_price_e8": index_price,
        "params": params,
        "accounts": pre_accounts,
        "pending_intents": [],
        "now_epoch": now_epoch,
        "fee_pool_e8": fee_pool_e8,
        "insurance_e8": insurance_e8,
        "insurance_ext_e8": insurance_ext_e8,
        "claims_paid_e8": claims_paid_e8,
        "net_deposited_e8": net_deposited_e8,
    }
    current_post_snapshot = {
        "version": 1,
        "market_id": MARKET_ID,
        "collateral_asset": "zUSD",
        "index_price_e8": settle,
        "params": params,
        "accounts": post_accounts,
        "pending_intents": [],
        "now_epoch": now_epoch + 1,
        "fee_pool_e8": post_ledgers["fee_pool_e8"],
        "insurance_e8": post_ledgers["insurance_e8"],
        "insurance_ext_e8": insurance_ext_e8,
        "claims_paid_e8": post_ledgers["claims_paid_e8"],
        "net_deposited_e8": net_deposited_e8,
    }
    current_pre_app_hash = _current_snapshot_hash(current_pre_snapshot)
    current_post_app_hash = _current_snapshot_hash(current_post_snapshot)
    delta_hash = _state_delta_hash(
        chain_id=CHAIN_ID,
        market_id=MARKET_ID,
        pre_state_root=current_pre_app_hash,
        post_state_root=current_post_app_hash,
        operation_hash=operation_hash,
        receipts_root=receipts_root,
    )

    return {
        "chain_id": CHAIN_ID,
        "market_id": MARKET_ID,
        "pre_app_hash": current_pre_app_hash,
        "expected_post_app_hash": current_post_app_hash,
        "operation_hash": operation_hash,
        "expected_state_delta_hash": delta_hash,
        "oracle_binding_hash": _hex("perps-np-oracle-binding"),
        "expected_participant_set_hash": participant_hash,
        "expected_pre_state_root": pre_root,
        "expected_post_state_root": post_root,
        "now_epoch": now_epoch,
        "index_price_e8": index_price,
        "clearing_price_e8": clearing_price,
        "funding_rate_bps": 0,
        "net_deposited_e8": net_deposited_e8,
        "fee_pool_e8": fee_pool_e8,
        "insurance_e8": insurance_e8,
        "insurance_ext_e8": insurance_ext_e8,
        "claims_paid_e8": claims_paid_e8,
        "post_fee_pool_e8": post_ledgers["fee_pool_e8"],
        "post_insurance_e8": post_ledgers["insurance_e8"],
        "post_claims_paid_e8": post_ledgers["claims_paid_e8"],
        "params": params,
        "accounts": accounts,
        "intents": intents,
        "_current_pre_state": current_pre_snapshot,
        "_current_post_state": current_post_snapshot,
        "_current_pre_app_hash": current_pre_app_hash,
        "_current_post_app_hash": current_post_app_hash,
        "_python_expected": {
            "pre_state_root": pre_root,
            "post_state_root": post_root,
            "pre_app_hash": current_pre_app_hash,
            "post_app_hash": current_post_app_hash,
            "participant_set_hash": participant_hash,
            "state_delta_hash": delta_hash,
            "receipts_root": receipts_root,
            "settle_price_e8": settle,
            "participant_count": len(pre_accounts),
            "intent_count": len(intents),
            "filled_intent_count": sum(1 for r in receipts if not r["rejected"] and int(r["delta"]) != 0),
            "zero_delta_fill_count": sum(1 for r in receipts if not r["rejected"] and int(r["delta"]) == 0),
            "reject_codes": sorted(
                {str(r["reject_code"]) for r in receipts if r["rejected"] and str(r["reject_code"])}
            ),
            "fee_pool_e8_after": post_ledgers["fee_pool_e8"],
            "insurance_e8_after": post_ledgers["insurance_e8"],
            "claims_paid_e8_after": post_ledgers["claims_paid_e8"],
        },
    }


def _rebind_pre_state(input_obj: dict[str, Any]) -> None:
    accounts = sorted((copy.deepcopy(a) for a in input_obj["accounts"]), key=lambda a: str(a["pubkey"]))
    chain_id = str(input_obj["chain_id"])
    market_id = str(input_obj["market_id"])
    participant_hash = _participant_set_hash(chain_id, market_id, accounts)
    pre_root = _state_root(
        PRE_ROOT_DOMAIN,
        chain_id=chain_id,
        market_id=market_id,
        now_epoch=int(input_obj["now_epoch"]),
        index_price_e8=int(input_obj["index_price_e8"]),
        net_deposited_e8=int(input_obj["net_deposited_e8"]),
        fee_pool_e8=int(input_obj["fee_pool_e8"]),
        insurance_e8=int(input_obj["insurance_e8"]),
        insurance_ext_e8=int(input_obj["insurance_ext_e8"]),
        claims_paid_e8=int(input_obj["claims_paid_e8"]),
        accounts=accounts,
    )
    input_obj["expected_participant_set_hash"] = participant_hash
    input_obj["expected_pre_state_root"] = pre_root
    input_obj["pre_app_hash"] = _current_snapshot_hash(_current_pre_state_from_input(input_obj))


def _base_four_wallet() -> dict[str, Any]:
    accounts = [
        _account("wallet-dd", 0, 0, 10_000),
        _account("wallet-aa", 5, 100, 10_000),
        _account("wallet-cc", 0, 0, 10_000),
        _account("wallet-bb", -5, 100, 10_000),
    ]
    intents = [
        _intent("wallet-aa", 10),
        _intent("wallet-bb", -6),
        _intent("wallet-cc", -4),
        _intent("wallet-dd", 0),
    ]
    return _complete_input(accounts=accounts, intents=intents)


def _base_five_wallet() -> dict[str, Any]:
    accounts = [
        _account("wallet-aa", 10, 100, 20_000),
        _account("wallet-bb", -6, 100, 20_000),
        _account("wallet-cc", -4, 100, 20_000),
        _account("wallet-dd", 0, 0, 20_000),
        _account("wallet-ee", 0, 0, 20_000),
    ]
    intents = [
        _intent("wallet-aa", 8, price=102),
        _intent("wallet-bb", -4, price=102),
        _intent("wallet-cc", -7, price=102),
        _intent("wallet-dd", 2, price=102),
        _intent("wallet-ee", 1, price=102),
    ]
    return _complete_input(
        accounts=accounts,
        intents=intents,
        index_price=100,
        clearing_price=102,
        fee_pool_e8=50,
        insurance_ext_e8=1_000,
        claims_paid_e8=100,
    )


def _base_adl_wallet() -> dict[str, Any]:
    accounts = [
        _account("wallet-aa", 10, 100, 450),
        _account("wallet-bb", -10, 100, 1_000),
        _account("wallet-cc", 0, 0, 1_000),
        _account("wallet-dd", 0, 0, 1_000),
    ]
    return _complete_input(
        accounts=accounts,
        intents=[],
        now_epoch=7,
        index_price=100,
        clearing_price=50,
        insurance_ext_e8=30,
        params_override={
            "max_oracle_move_bps": 10_000,
            "min_notional_for_bounty_e8": 0,
        },
    )


def _base_reject_paths_oracle_clamp() -> dict[str, Any]:
    accounts = [
        _account("wallet-aa", 0, 0, 10_000),
        _account("wallet-bb", 0, 0, 10_000),
        _account("wallet-cc", 0, 0, 10_000),
        _account("wallet-dd", 0, 0, 10_000),
        _account("wallet-ee", 0, 0, 0),
        _account("wallet-ff", 0, 0, 10_000),
    ]
    intents = [
        _intent("wallet-aa", 1, nonce=1, price=110),
        _intent("wallet-aa", 2, nonce=2, price=110),
        _intent("wallet-bb", -2, price=110),
        _intent("wallet-cc", 1, price=110, min_fill=2),
        _intent("wallet-dd", 1, price=90),
        _intent("wallet-ee", 1, price=110),
        _intent("wallet-ff", 2_000, price=110),
    ]
    return _complete_input(
        accounts=accounts,
        intents=intents,
        now_epoch=4,
        index_price=100,
        clearing_price=200,
        params_override={"max_oracle_move_bps": 1_000},
    )


def _cases() -> dict[str, dict[str, Any]]:
    four = _base_four_wallet()
    five = _base_five_wallet()
    adl = _base_adl_wallet()
    reject_paths = _base_reject_paths_oracle_clamp()

    floor = _complete_input(
        accounts=[
            _account("wallet-aa", 5, 100, 10_000),
            _account("wallet-bb", -5, 100, 10_000),
            _account("wallet-cc", 0, 0, 10_000),
        ],
        intents=[_intent("wallet-aa", 5), _intent("wallet-bb", -5)],
    )
    duplicate = copy.deepcopy(four)
    duplicate["intents"].append(copy.deepcopy(duplicate["intents"][0]))

    expired = copy.deepcopy(four)
    expired["intents"][0]["expiry_epoch"] = 0

    wrong_post = copy.deepcopy(four)
    wrong_post["_current_post_app_hash"] = _hex("wrong-post-app-hash")

    nonzero_funding = copy.deepcopy(four)
    nonzero_funding["funding_rate_bps"] = 1

    negative_ledger = copy.deepcopy(four)
    negative_ledger["net_deposited_e8"] = -1
    _rebind_pre_state(negative_ledger)

    epoch_overflow = copy.deepcopy(four)
    epoch_overflow["now_epoch"] = (1 << 64) - 1
    _rebind_pre_state(epoch_overflow)

    return {
        "four_wallet": {"input": four, "must_prove": True},
        "five_wallet": {"input": five, "must_prove": True},
        "adl_wallet": {"input": adl, "must_prove": True},
        "reject_paths_oracle_clamp": {"input": reject_paths, "must_prove": True},
        "neg_participant_floor": {"input": floor, "must_prove": False},
        "neg_duplicate_nonce": {"input": duplicate, "must_prove": False},
        "neg_expired_intent": {"input": expired, "must_prove": False},
        "neg_wrong_post_state_root": {"input": wrong_post, "must_prove": False},
        "neg_nonzero_funding": {"input": nonzero_funding, "must_prove": False},
        "neg_negative_ledger": {"input": negative_ledger, "must_prove": False},
        "neg_epoch_overflow": {"input": epoch_overflow, "must_prove": False},
    }


def _strip_private(input_obj: dict[str, Any]) -> dict[str, Any]:
    clean = copy.deepcopy(input_obj)
    clean.pop("_python_expected", None)
    clean.pop("_current_pre_state", None)
    clean.pop("_current_post_state", None)
    clean.pop("_current_pre_app_hash", None)
    clean.pop("_current_post_app_hash", None)
    return clean


def _current_pre_state_from_input(input_obj: dict[str, Any]) -> dict[str, Any]:
    insurance_e8 = int(input_obj.get("insurance_e8", 0))
    if "insurance_e8" not in input_obj:
        insurance_e8 = int(input_obj.get("insurance_ext_e8", 0)) - int(input_obj.get("claims_paid_e8", 0))
    return {
        "version": 1,
        "market_id": str(input_obj["market_id"]),
        "collateral_asset": "zUSD",
        "index_price_e8": int(input_obj["index_price_e8"]),
        "params": copy.deepcopy(input_obj["params"]),
        "accounts": sorted((copy.deepcopy(a) for a in input_obj["accounts"]), key=lambda a: str(a["pubkey"])),
        "pending_intents": [],
        "now_epoch": int(input_obj["now_epoch"]),
        "fee_pool_e8": int(input_obj["fee_pool_e8"]),
        "insurance_e8": insurance_e8,
        "insurance_ext_e8": int(input_obj["insurance_ext_e8"]),
        "claims_paid_e8": int(input_obj["claims_paid_e8"]),
        "net_deposited_e8": int(input_obj["net_deposited_e8"]),
    }


def _current_oracle(name: str, input_obj: dict[str, Any]) -> dict[str, Any]:
    return {
        "oracle_bridge_id": f"zenodex-perps-np-smoke-{name}",
        "oracle_bridge_hash": _hex(f"{name}:oracle_bridge"),
        "price_e8": int(input_obj["clearing_price_e8"]),
        "price_timestamp": int(input_obj["now_epoch"]),
        "max_staleness_seconds": 3600,
        "observed_at": int(input_obj["now_epoch"]),
        "pre_price_batch_commitment": _hex(f"{name}:pre_price_batch"),
    }


def _current_actions(name: str, input_obj: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "kind": "run_epoch",
            "oracle": _current_oracle(name, input_obj),
            "clearing_price_e8": int(input_obj["clearing_price_e8"]),
            "funding_rate_bps": int(input_obj["funding_rate_bps"]),
            "intents": [copy.deepcopy(intent) for intent in input_obj["intents"]],
        }
    ]


def _current_generate_request(name: str, input_obj: dict[str, Any]) -> dict[str, Any]:
    pre_state = _current_pre_state_from_input(input_obj)
    pre_app_hash = _current_snapshot_hash(pre_state)
    post_app_hash = str(input_obj.get("_current_post_app_hash") or input_obj.get("expected_post_app_hash") or _hex(name))
    return {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "proof_type": PROOF_TYPE,
        "state_hash": _hex(f"{name}:state_hash"),
        "chain_id": str(input_obj["chain_id"]),
        "context": {
            "chain_id": str(input_obj["chain_id"]),
            "execution_context_hash": _hex(f"{name}:execution_context"),
            "app_hash_pre": pre_app_hash,
            "perps_state_pre": pre_state,
        },
        "pre_state": pre_state,
        "actions": _current_actions(name, input_obj),
        "expected_post_app_hash": post_app_hash,
        "tau_state": {"app_hash": post_app_hash},
    }


def _run_cli(*, repo: Path, request: dict[str, Any], target_dir: Path, timeout: int) -> tuple[int, str, str]:
    env = os.environ.copy()
    env["RISC0_FORCE_BUILD"] = "1"
    env["CARGO_TARGET_DIR"] = str(target_dir)
    build = subprocess.run(
        [
            "cargo",
            "build",
            "--release",
            "--manifest-path",
            str(repo / "zk/state_proof_risc0/Cargo.toml"),
            "-q",
            "-p",
            "tau-state-proof-risc0-cli",
        ],
        cwd=repo,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    if build.returncode != 0:
        return build.returncode, build.stdout, build.stderr
    cli_bin = target_dir / "release" / "tau-state-proof-risc0-cli"
    if not cli_bin.exists():
        return 2, "", f"missing built RISC0 CLI: {cli_bin}"
    command = [str(cli_bin)]
    if request.get("schema") == "tau_state_proof_verify":
        context = request.get("context")
        if not isinstance(context, dict):
            return 2, "", "verify context must be an object"
        expected_context_hash = context.get("execution_context_hash")
        if not isinstance(expected_context_hash, str) or not expected_context_hash:
            return 2, "", "verify execution_context_hash missing"
        command.extend(
            ["--expected-execution-context-hash", expected_context_hash]
        )
    proc = subprocess.run(
        command,
        cwd=repo,
        env=env,
        input=json.dumps(request, separators=(",", ":")),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, proc.stdout, proc.stderr


def _run_cli_json(*, repo: Path, request: dict[str, Any], target_dir: Path, timeout: int) -> dict[str, Any]:
    rc, out, err = _run_cli(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
    if rc != 0:
        raise RuntimeError(f"cli failed exit={rc}\nstdout={out[-2000:]}\nstderr={err[-4000:]}")
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"cli returned invalid JSON: {exc}\nstdout={out[-2000:]}\nstderr={err[-2000:]}") from exc
    if not isinstance(parsed, dict):
        raise RuntimeError("cli returned non-object JSON")
    return parsed


def _expected_from_meta(meta: dict[str, Any]) -> dict[str, Any]:
    keys = (
        "execution_context_hash",
        "chain_id",
        "pre_app_hash",
        "post_app_hash",
        "operation_hash",
        "state_delta_hash",
        "oracle_binding_hash",
        "collateral_binding_hash",
        "participant_set_hash",
        "receipt_root",
        "participant_count",
        "net_position_base",
        "total_collateral_e8",
        "funding_residual_e8",
        "matched_base_volume",
    )
    return {key: meta[key] for key in keys}


def _verify(
    *,
    repo: Path,
    proof: dict[str, Any],
    expected: dict[str, Any],
    actions: list[dict[str, Any]],
    target_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    context = {
        "chain_id": expected["chain_id"],
        "execution_context_hash": expected["execution_context_hash"],
        "app_hash_pre": expected["pre_app_hash"],
        "operation_hash": expected["operation_hash"],
        "state_delta_hash": expected["state_delta_hash"],
        "oracle_binding_hash": expected["oracle_binding_hash"],
        "collateral_binding_hash": expected["collateral_binding_hash"],
        "participant_set_hash": expected["participant_set_hash"],
        "receipt_root": expected["receipt_root"],
    }
    return _run_cli_json(
        repo=repo,
        target_dir=target_dir,
        timeout=timeout,
        request={
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": proof["state_hash"],
            "chain_id": expected["chain_id"],
            "proof": proof,
            "tau_state": {"app_hash": expected["post_app_hash"]},
            "context": context,
            "actions": actions,
        },
    )


def _assert_verify_rejects(
    *,
    repo: Path,
    proof: dict[str, Any],
    expected: dict[str, Any],
    actions: list[dict[str, Any]],
    target_dir: Path,
    timeout: int,
    label: str,
) -> str:
    result = _verify(repo=repo, proof=proof, expected=expected, actions=actions, target_dir=target_dir, timeout=timeout)
    if result.get("ok") is not False:
        raise RuntimeError(f"{label}: verifier accepted tampered request: {result}")
    return str(result.get("error", ""))


def _run_case(
    *,
    name: str,
    case: dict[str, Any],
    repo: Path,
    out_dir: Path,
    target_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    case_input = case["input"]
    request = _current_generate_request(name, case_input)
    actions = copy.deepcopy(request["actions"])

    if not case["must_prove"]:
        rc, out, err = _run_cli(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
        if rc == 0:
            raise RuntimeError(f"negative case {name} unexpectedly proved\nstdout={out[-2000:]}")
        return {
            "case": name,
            "kind": "negative",
            "ok": True,
            "rejected_as_expected": True,
            "exit_code": rc,
            "reject_signal": (err.strip().splitlines()[-1] if err.strip() else "")[:300],
        }

    proof = _run_cli_json(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
    meta = proof.get("meta")
    if not isinstance(meta, dict):
        raise RuntimeError(f"{name}: proof.meta missing")
    if proof.get("proof_type") != PROOF_TYPE:
        raise RuntimeError(f"{name}: wrong proof type: {proof.get('proof_type')}")

    if meta.get("pre_app_hash") != request["context"]["app_hash_pre"]:
        raise RuntimeError(f"{name}: pre_app_hash mismatch")
    if meta.get("post_app_hash") != request["expected_post_app_hash"]:
        raise RuntimeError(f"{name}: post_app_hash mismatch")
    if int(meta.get("participant_count", 0)) < 4:
        raise RuntimeError(f"{name}: participant_count below multi-party floor")
    if str(meta.get("net_position_base")) != "0":
        raise RuntimeError(f"{name}: net_position_base is not zero")

    expected = _expected_from_meta(meta)
    verified = _verify(repo=repo, proof=proof, expected=expected, actions=actions, target_dir=target_dir, timeout=timeout)
    if verified.get("ok") is not True:
        raise RuntimeError(f"{name}: strict verifier rejected proof: {verified}")

    tamper_errors: dict[str, str] = {}
    bad_proof = copy.deepcopy(proof)
    bad_proof["proof_type"] = "risc0.zenodex_spot_transition.v1"
    tamper_errors["wrong_proof_type"] = _assert_verify_rejects(
        repo=repo,
        proof=bad_proof,
        expected=expected,
        actions=actions,
        target_dir=target_dir,
        timeout=timeout,
        label=f"{name}:wrong_proof_type",
    )
    bad_proof = copy.deepcopy(proof)
    bad_meta = bad_proof.setdefault("meta", {})
    if isinstance(bad_meta, dict):
        bad_meta["risc0_image_id"] = _hex(f"{name}-wrong-image-id")
    tamper_errors["wrong_image_id"] = _assert_verify_rejects(
        repo=repo,
        proof=bad_proof,
        expected=expected,
        actions=actions,
        target_dir=target_dir,
        timeout=timeout,
        label=f"{name}:wrong_image_id",
    )
    for field, value in (
        ("chain_id", "wrong-chain"),
        ("pre_app_hash", _hex(f"{name}-wrong-pre-app")),
        ("post_app_hash", _hex(f"{name}-wrong-post-app")),
        ("participant_set_hash", _hex(f"{name}-wrong-participants")),
        ("operation_hash", _hex(f"{name}-wrong-operation")),
        ("oracle_binding_hash", _hex(f"{name}-wrong-oracle")),
        ("collateral_binding_hash", _hex(f"{name}-wrong-collateral")),
        ("receipt_root", _hex(f"{name}-wrong-receipt-root")),
        ("state_delta_hash", _hex(f"{name}-wrong-delta")),
    ):
        bad_expected = copy.deepcopy(expected)
        bad_expected[field] = value
        tamper_errors[field] = _assert_verify_rejects(
            repo=repo,
            proof=proof,
            expected=bad_expected,
            actions=actions,
            target_dir=target_dir,
            timeout=timeout,
            label=f"{name}:{field}",
        )

    proof_path = out_dir / f"{name}_perps_np_risc0_proof.json"
    proof_path.write_text(json.dumps(proof, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    return {
        "case": name,
        "kind": "positive",
        "ok": True,
        "proof_type": proof.get("proof_type"),
        "participant_count": meta.get("participant_count"),
        "intent_count": len(actions[0]["intents"]) if actions else 0,
        "matched_base_volume": meta.get("matched_base_volume"),
        "net_position_base": meta.get("net_position_base"),
        "funding_residual_e8": meta.get("funding_residual_e8"),
        "risc0_image_id": meta.get("risc0_image_id"),
        "current_surface_binding_check": True,
        "strict_verify": True,
        "tamper_rejections": sorted(tamper_errors),
        "proof_base64_len": len(proof.get("proof", "")) if isinstance(proof.get("proof"), str) else 0,
        "proof_path": str(proof_path),
    }


def run_smoke(*, repo: Path, out_dir: Path, target_dir: Path, timeout: int, case_name: str) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    cases = _cases()
    selected = list(cases) if case_name == "all" else [case_name]
    unknown = [case for case in selected if case not in cases]
    if unknown:
        raise ValueError(f"unknown smoke case(s): {', '.join(unknown)}")

    reports = [
        _run_case(name=name, case=cases[name], repo=repo, out_dir=out_dir, target_dir=target_dir, timeout=timeout)
        for name in selected
    ]
    report = {
        "schema": "zenodex.perps_np_risc0_real_proof_smoke.v1",
        "ok": all(bool(r.get("ok")) for r in reports),
        "proof_surface": PROOF_TYPE,
        "case_count": len(reports),
        "positive": sum(1 for r in reports if r.get("kind") == "positive"),
        "negative": sum(1 for r in reports if r.get("kind") == "negative"),
        "production_security_claim": False,
        "dynamic_membership_floor": 4,
        "cases": reports,
    }
    report_path = out_dir / "perps_np_risc0_real_proof_smoke_report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zenodex_perps_np_risc0_real_proof_smoke"))
    parser.add_argument("--target-dir", type=Path, default=Path("/tmp/zenodex_perps_np_risc0_target"))
    parser.add_argument("--timeout", type=int, default=360)
    parser.add_argument("--case", choices=tuple(list(_cases()) + ["all"]), default="four_wallet")
    args = parser.parse_args(argv)

    report = run_smoke(
        repo=args.repo.resolve(),
        out_dir=args.out_dir.resolve(),
        target_dir=args.target_dir.resolve(),
        timeout=args.timeout,
        case_name=args.case,
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
