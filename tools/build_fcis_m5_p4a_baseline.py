#!/usr/bin/env python3
"""Deterministic final legacy golden baseline builder for FCIS M5-P4A.

Executes the currently mounted LEGACY path only.  Never calls the exact FCIS
evaluator to populate legacy results.  Produces a byte-deterministic JSON
artifact binding every mounted command variant with accepted and rejected
fixtures, canonical bytes/hashes, and complete observable projections.

M5-P4A-GOLDEN-001: builder is byte-deterministic (run twice -> identical).
M5-P4A-GOLDEN-002: legacy provenance cannot be substituted.
M5-P4A-GOLDEN-003: each mounted command has accepted/rejected coverage.
"""

from __future__ import annotations

import hashlib
import json
import platform
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex import DexConfig, DexState, step
from src.core.fees import FeeAccumulatorState, FeeSplitParams, split_fee_with_dust_carry
from src.core.liquidity import create_pool
from src.core.settlement import Settlement
from src.integration.dex_snapshot import snapshot_from_state
from src.state import BalanceTable, LPTable
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from src.state.state_root import compute_state_root
from src.state.support_root import compute_support_state_root_for_batch

_REPO_ROOT = Path(__file__).resolve().parents[1]
_ARTIFACT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-legacy-baseline/v1"

_PUBKEY_A = "0x" + "11" * 48
_PUBKEY_B = "0x" + "22" * 48
_ASSET_0 = "0x" + "01" * 32
_ASSET_1 = "0x" + "02" * 32
_ASSET_2 = "0x" + "03" * 32


def _iid(value: int) -> str:
    return "0x" + f"{value:064x}"


def _canonical_bytes(value: Any) -> bytes:
    return canonical_json_bytes(value)


def _settlement_op_dict(settlement: Settlement) -> dict[str, Any]:
    from src.integration.operations import create_settlement_operation

    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("settlement operation must be an object")
    return op


def _intent_dict(intent: Intent) -> dict[str, Any]:
    from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1

    return build_dex_intent_signing_dict_v1(intent)


def _state_root(state: DexState) -> str:
    return compute_state_root(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        fee_accumulator=state.fee_accumulator,
    )


def _support_root_v4(
    intents: list[Intent],
    state: DexState,
) -> str:
    return compute_support_state_root_for_batch(
        intents=intents,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
    )


def _snapshot_bytes(state: DexState, version: int = 4) -> bytes:
    return snapshot_from_state(state, version=version).canonical_bytes()


def _snapshot_root(state: DexState, version: int = 4) -> str:
    return snapshot_from_state(state, version=version).commitment_hex()


@dataclass(frozen=True)
class _FixtureInput:
    fixture_id: str
    command_kind: str
    intents: list[Intent]
    state: DexState
    config: DexConfig
    category: str
    description: str


def _base_pool_state() -> tuple[DexState, str]:
    pool_id, pool, lp_minted = create_pool(
        asset0=_ASSET_0,
        asset1=_ASSET_1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=_PUBKEY_A,
    )
    balances = BalanceTable()
    balances.set(_PUBKEY_A, _ASSET_0, 10_000_000)
    balances.set(_PUBKEY_A, _ASSET_1, 10_000_000)
    balances.set(_PUBKEY_B, _ASSET_0, 10_000_000)
    balances.set(_PUBKEY_B, _ASSET_1, 10_000_000)
    lp_balances = LPTable()
    lp_balances.set(_PUBKEY_A, pool_id, lp_minted)
    lp_balances.set("0x" + "00" * 48, pool_id, pool.lp_supply - lp_minted)
    lp_balances.set_last_mint_timestamp(_PUBKEY_A, pool_id, 100)
    state = DexState(
        balances=balances,
        pools={pool_id: pool},
        lp_balances=lp_balances,
    )
    return state, pool_id


def _second_pool_state(
    state: DexState,
    pool_id_0: str,
) -> tuple[DexState, str]:
    pool_id_1, pool_1, lp_minted_1 = create_pool(
        asset0=_ASSET_1,
        asset1=_ASSET_2,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=_PUBKEY_A,
    )
    new_balances = BalanceTable()
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        new_balances.set(pubkey, asset, amount)
    new_balances.set(_PUBKEY_A, _ASSET_2, 10_000_000)
    new_balances.set(_PUBKEY_B, _ASSET_2, 10_000_000)
    new_pools = dict(state.pools)
    new_pools[pool_id_1] = pool_1
    new_lp = LPTable()
    for (pubkey, pool_pid), amount in state.lp_balances.get_all_balances().items():
        new_lp.set(pubkey, pool_pid, amount)
    for (pubkey, pool_pid), ts in state.lp_balances.get_all_last_mint_timestamps().items():
        new_lp.set_last_mint_timestamp(pubkey, pool_pid, ts)
    new_lp.set(_PUBKEY_A, pool_id_1, lp_minted_1)
    new_lp.set("0x" + "00" * 48, pool_id_1, pool_1.lp_supply - lp_minted_1)
    new_lp.set_last_mint_timestamp(_PUBKEY_A, pool_id_1, 100)
    return (
        DexState(
            balances=new_balances,
            pools=new_pools,
            lp_balances=new_lp,
        ),
        pool_id_1,
    )


def _config_default() -> DexConfig:
    return DexConfig(
        settlement_validation="strong_proof_carrying",
        reject_settlements_with_rejected_intents=True,
        require_all_nonces=True,
        protocol_fee_share_bps=0,
        protocol_fee_recipient_pubkey=None,
    )


def _config_with_fee() -> DexConfig:
    return DexConfig(
        settlement_validation="strong_proof_carrying",
        reject_settlements_with_rejected_intents=True,
        require_all_nonces=True,
        fee_split_params=FeeSplitParams(3_333, 3_333, 3_334),
        protocol_fee_share_bps=0,
        protocol_fee_recipient_pubkey=None,
    )


def _config_nonce_free() -> DexConfig:
    return DexConfig(
        settlement_validation="strong_proof_carrying",
        reject_settlements_with_rejected_intents=True,
        require_all_nonces=False,
        allow_legacy_nonce_free_steps=True,
    )


def _build_fixture_inputs() -> list[_FixtureInput]:
    fixtures: list[_FixtureInput] = []
    base_state, pool_id = _base_pool_state()

    # --- SWAP_EXACT_IN: smallest valid accepted ---
    swap_in_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 1,
            "min_amount_out": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_smallest_accepted",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_intent],
        state=base_state,
        config=_config_default(),
        category="smallest_valid_accepted",
        description="smallest valid exact-in swap (amount_in=1)",
    ))

    # --- SWAP_EXACT_IN: boundary valid ---
    swap_in_boundary = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 500_000,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_boundary_valid",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_boundary],
        state=base_state,
        config=_config_default(),
        category="boundary_valid",
        description="boundary exact-in swap (large amount_in)",
    ))

    # --- SWAP_EXACT_IN: rejected (insufficient balance) ---
    swap_in_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(3),
        sender_pubkey=_PUBKEY_B,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000_000,
            "min_amount_out": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_insufficient_balance_rejected",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_reject],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="exact-in swap with insufficient balance",
    ))

    # --- SWAP_EXACT_IN: recipient different from sender ---
    swap_in_recipient = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(4),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000,
            "min_amount_out": 1,
            "recipient": _PUBKEY_B,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_recipient_differs",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_recipient],
        state=base_state,
        config=_config_default(),
        category="recipient_different_from_sender",
        description="exact-in swap with recipient != sender",
    ))

    # --- SWAP_EXACT_IN: expired/finality ---
    swap_in_expired = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(5),
        sender_pubkey=_PUBKEY_A,
        deadline=1,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_expired_rejected",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_expired],
        state=base_state,
        config=_config_default(),
        category="expired_finality",
        description="exact-in swap with expired deadline",
    ))

    # --- SWAP_EXACT_IN: nonce/replay ---
    swap_in_nonce = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(6),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000,
            "min_amount_out": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_missing_nonce_rejected",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_in_nonce],
        state=base_state,
        config=_config_default(),
        category="nonce_replay",
        description="exact-in swap missing nonce (require_all_nonces=True)",
    ))

    # --- SWAP_EXACT_OUT: smallest valid accepted ---
    swap_out_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(7),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_out": 1,
            "max_amount_in": 1_000_000,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_out_smallest_accepted",
        command_kind="SWAP_EXACT_OUT",
        intents=[swap_out_intent],
        state=base_state,
        config=_config_default(),
        category="smallest_valid_accepted",
        description="smallest valid exact-out swap (amount_out=1)",
    ))

    # --- SWAP_EXACT_OUT: boundary valid ---
    swap_out_boundary = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(8),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_out": 500_000,
            "max_amount_in": 1_000_000,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_out_boundary_valid",
        command_kind="SWAP_EXACT_OUT",
        intents=[swap_out_boundary],
        state=base_state,
        config=_config_default(),
        category="boundary_valid",
        description="boundary exact-out swap (large amount_out)",
    ))

    # --- SWAP_EXACT_OUT: rejected (max_amount_in too low) ---
    swap_out_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(9),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_out": 500_000,
            "max_amount_in": 1,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_out_max_in_too_low_rejected",
        command_kind="SWAP_EXACT_OUT",
        intents=[swap_out_reject],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="exact-out swap with max_amount_in too low",
    ))

    # --- SWAP_EXACT_OUT: recipient different from sender ---
    swap_out_recipient = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(10),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_out": 100_000,
            "max_amount_in": 1_000_000,
            "recipient": _PUBKEY_B,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_out_recipient_differs",
        command_kind="SWAP_EXACT_OUT",
        intents=[swap_out_recipient],
        state=base_state,
        config=_config_default(),
        category="recipient_different_from_sender",
        description="exact-out swap with recipient != sender",
    ))

    # --- CREATE_POOL: smallest valid accepted ---
    create_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(11),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "asset0": _ASSET_2,
            "asset1": _ASSET_0,
            "fee_bps": 30,
            "amount0": 1_000_000,
            "amount1": 1_000_000,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="create_pool_smallest_accepted",
        command_kind="CREATE_POOL",
        intents=[create_intent],
        state=base_state,
        config=_config_default(),
        category="smallest_valid_accepted",
        description="smallest valid create pool",
    ))

    # --- CREATE_POOL: rejected (duplicate pool) ---
    create_dup = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(12),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "asset0": _ASSET_0,
            "asset1": _ASSET_1,
            "fee_bps": 30,
            "amount0": 1_000_000,
            "amount1": 1_000_000,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="create_pool_duplicate_rejected",
        command_kind="CREATE_POOL",
        intents=[create_dup],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="create pool with duplicate asset pair",
    ))

    # --- ADD_LIQUIDITY: smallest valid accepted ---
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(13),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 1,
            "amount1_desired": 1,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="add_liquidity_smallest_accepted",
        command_kind="ADD_LIQUIDITY",
        intents=[add_liq],
        state=base_state,
        config=_config_default(),
        category="smallest_valid_accepted",
        description="smallest valid add liquidity",
    ))

    # --- ADD_LIQUIDITY: boundary valid ---
    add_liq_boundary = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(14),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 1_000_000,
            "amount1_desired": 1_000_000,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="add_liquidity_boundary_valid",
        command_kind="ADD_LIQUIDITY",
        intents=[add_liq_boundary],
        state=base_state,
        config=_config_default(),
        category="boundary_valid",
        description="boundary add liquidity (large amounts)",
    ))

    # --- ADD_LIQUIDITY: rejected (pool not found) ---
    add_liq_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(15),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": "0x" + "ff" * 32,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="add_liquidity_pool_not_found_rejected",
        command_kind="ADD_LIQUIDITY",
        intents=[add_liq_reject],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="add liquidity to nonexistent pool",
    ))

    # --- REMOVE_LIQUIDITY: smallest valid accepted ---
    remove_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(16),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="remove_liquidity_smallest_accepted",
        command_kind="REMOVE_LIQUIDITY",
        intents=[remove_liq],
        state=base_state,
        config=_config_default(),
        category="smallest_valid_accepted",
        description="smallest valid remove liquidity",
    ))

    # --- REMOVE_LIQUIDITY: boundary valid ---
    remove_liq_boundary = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(17),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "lp_amount": 500_000,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="remove_liquidity_boundary_valid",
        command_kind="REMOVE_LIQUIDITY",
        intents=[remove_liq_boundary],
        state=base_state,
        config=_config_default(),
        category="boundary_valid",
        description="boundary remove liquidity (large lp_amount)",
    ))

    # --- REMOVE_LIQUIDITY: rejected (insufficient LP) ---
    remove_liq_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(18),
        sender_pubkey=_PUBKEY_B,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "lp_amount": 100_000_000,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="remove_liquidity_insufficient_lp_rejected",
        command_kind="REMOVE_LIQUIDITY",
        intents=[remove_liq_reject],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="remove liquidity with insufficient LP balance",
    ))

    # --- Fee/dust/rounding: swap with fee split ---
    swap_fee = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(19),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_fee_dust_rounding",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_fee],
        state=base_state,
        config=_config_with_fee(),
        category="fee_dust_rounding",
        description="exact-in swap with fee split and dust carry",
    ))

    # --- Nonce/replay: nonce-free legacy mode accepted ---
    swap_nonce_free = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(20),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_1,
            "amount_in": 100_000,
            "min_amount_out": 1,
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="swap_exact_in_nonce_free_legacy_accepted",
        command_kind="SWAP_EXACT_IN",
        intents=[swap_nonce_free],
        state=base_state,
        config=_config_nonce_free(),
        category="nonce_replay",
        description="exact-in swap accepted in legacy nonce-free mode",
    ))

    # --- ROUTE_EXACT_IN: multi-leg ---
    two_pool_state, pool_id_1 = _second_pool_state(base_state, pool_id)
    from src.core.route_settlement import RouteBinding, RouteLegBinding, route_binding_to_fields

    route_binding = RouteBinding(
        kind="exact_in",
        asset_in=_ASSET_0,
        asset_out=_ASSET_2,
        total_amount_in=50_000,
        total_amount_out=48_000,
        legs=(
            RouteLegBinding(pool_id=pool_id, asset_in=_ASSET_0, asset_out=_ASSET_1, amount_in=50_000, amount_out=49_000),
            RouteLegBinding(pool_id=pool_id_1, asset_in=_ASSET_1, asset_out=_ASSET_2, amount_in=49_000, amount_out=48_000),
        ),
        pool_fingerprints={pool_id: pool_id, pool_id_1: pool_id_1},
    )
    route_in_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_IN,
        intent_id=_iid(21),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "quote_receipt_hash": "0x" + "aa" * 32,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_2,
            "leg_indices": [0, 1],
            "total_amount_in": 50_000,
            "total_min_amount_out": 1,
            "nonce": 1,
            **route_binding_to_fields(route_binding),
        },
    )
    route_settlement = compute_settlement(
        [route_in_intent],
        two_pool_state.pools,
        two_pool_state.balances,
        two_pool_state.lp_balances,
        route_bindings={route_in_intent.intent_id: route_binding},
    )
    fixtures.append(_FixtureInput(
        fixture_id="route_exact_in_multi_leg_accepted",
        command_kind="ROUTE_EXACT_IN",
        intents=[route_in_intent],
        state=two_pool_state,
        config=_config_default(),
        category="route_multi_leg",
        description="multi-leg route exact-in swap",
    ))

    # --- ROUTE_EXACT_IN: rejected (pool not found) ---
    route_in_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_IN,
        intent_id=_iid(22),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "quote_receipt_hash": "0x" + "bb" * 32,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_2,
            "leg_indices": [0, 1],
            "total_amount_in": 50_000,
            "total_min_amount_out": 1,
            "nonce": 1,
            **route_binding_to_fields(route_binding),
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="route_exact_in_pool_not_found_rejected",
        command_kind="ROUTE_EXACT_IN",
        intents=[route_in_reject],
        state=base_state,
        config=_config_default(),
        category="stable_rejected",
        description="multi-leg route exact-in with missing second pool",
    ))

    # --- ROUTE_EXACT_OUT: multi-leg ---
    route_out_binding = RouteBinding(
        kind="exact_out",
        asset_in=_ASSET_0,
        asset_out=_ASSET_2,
        total_amount_in=51_000,
        total_amount_out=49_000,
        legs=(
            RouteLegBinding(pool_id=pool_id, asset_in=_ASSET_0, asset_out=_ASSET_1, amount_in=51_000, amount_out=50_000),
            RouteLegBinding(pool_id=pool_id_1, asset_in=_ASSET_1, asset_out=_ASSET_2, amount_in=50_000, amount_out=49_000),
        ),
        pool_fingerprints={pool_id: pool_id, pool_id_1: pool_id_1},
    )
    route_out_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_OUT,
        intent_id=_iid(23),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "quote_receipt_hash": "0x" + "cc" * 32,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_2,
            "leg_indices": [0, 1],
            "total_amount_out": 49_000,
            "total_max_amount_in": 100_000,
            "nonce": 1,
            **route_binding_to_fields(route_out_binding),
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="route_exact_out_multi_leg_accepted",
        command_kind="ROUTE_EXACT_OUT",
        intents=[route_out_intent],
        state=two_pool_state,
        config=_config_default(),
        category="route_multi_leg",
        description="multi-leg route exact-out swap",
    ))

    # --- ROUTE_EXACT_OUT: rejected (max_amount_in too low) ---
    route_out_reject = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_OUT,
        intent_id=_iid(24),
        sender_pubkey=_PUBKEY_A,
        deadline=10_000,
        fields={
            "quote_receipt_hash": "0x" + "dd" * 32,
            "asset_in": _ASSET_0,
            "asset_out": _ASSET_2,
            "leg_indices": [0, 1],
            "total_amount_out": 49_000,
            "total_max_amount_in": 1,
            "nonce": 1,
            **route_binding_to_fields(route_out_binding),
        },
    )
    fixtures.append(_FixtureInput(
        fixture_id="route_exact_out_max_in_too_low_rejected",
        command_kind="ROUTE_EXACT_OUT",
        intents=[route_out_reject],
        state=two_pool_state,
        config=_config_default(),
        category="stable_rejected",
        description="multi-leg route exact-out with max_amount_in too low",
    ))

    return fixtures


def _execute_legacy(
    fixture: _FixtureInput,
) -> dict[str, Any]:
    """Execute the mounted legacy path only via ``step()`` in ``dex.py``."""

    result = step(
        config=fixture.config,
        state=fixture.state,
        intents=fixture.intents,
    )
    pre_state_root = _state_root(fixture.state)
    pre_support_root_v4 = _support_root_v4(fixture.intents, fixture.state)
    pre_snapshot_bytes = _snapshot_bytes(fixture.state)
    pre_snapshot_root = _snapshot_root(fixture.state)
    command_bytes_list = [
        _canonical_bytes(_intent_dict(intent)) for intent in fixture.intents
    ]
    command_root = sha256_hex(
        domain_sep_bytes("fcis_command_batch", version=1)
        + b"".join(command_bytes_list)
    )
    settlement = None
    settlement_bytes = b""
    settlement_hash = ""
    if result.ok and result.state is not None:
        settlement = result.effects.get("settlement") if result.effects else None
    if settlement is not None:
        settlement_bytes = _canonical_bytes(_settlement_op_dict(settlement))
        settlement_hash = sha256_hex(
            domain_sep_bytes("fcis_settlement", version=1) + settlement_bytes
        )
    next_state_root = ""
    next_snapshot_bytes = b""
    next_snapshot_root = ""
    next_support_root_v4 = ""
    if result.ok and result.state is not None:
        next_state_root = _state_root(result.state)
        next_snapshot_bytes = _snapshot_bytes(result.state)
        next_snapshot_root = _snapshot_root(result.state)
        next_support_root_v4 = _support_root_v4(fixture.intents, result.state)
    total_fees = 0
    fee_split = None
    if settlement is not None:
        total_fees = sum(fill.fee_paid or 0 for fill in settlement.fills)
        if fixture.config.fee_split_params is not None:
            fee_split_result, _next_fee = split_fee_with_dust_carry(
                fee_amount=total_fees,
                params=fixture.config.fee_split_params,
                state=fixture.state.fee_accumulator,
            )
            fee_split = {
                "buyback_amount": fee_split_result.buyback_amount,
                "treasury_amount": fee_split_result.treasury_amount,
                "rewards_amount": fee_split_result.rewards_amount,
                "dust_carried": fee_split_result.dust_carried,
            }
    nonce_ok = True
    nonce_error: str | None = None
    next_nonces_hash = ""
    if fixture.intents:
        ok, err, next_nonces = validate_and_apply_intent_nonce_batch(
            nonces=fixture.state.nonces,
            intents=fixture.intents,
            require_all_nonces=fixture.config.requires_complete_nonce_coverage(),
        )
        nonce_ok = ok
        nonce_error = err
        if ok and next_nonces is not None:
            next_nonces_hash = sha256_hex(
                domain_sep_bytes("fcis_nonce_table", version=1)
                + _canonical_bytes(
                    sorted(next_nonces.get_all().items())
                )
            )
    balance_deltas = []
    reserve_deltas = []
    lp_deltas = []
    fills_summary = []
    events = []
    if settlement is not None:
        for delta in settlement.balance_deltas:
            balance_deltas.append({
                "pubkey": delta.pubkey,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            })
        for delta in settlement.reserve_deltas:
            reserve_deltas.append({
                "pool_id": delta.pool_id,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            })
        for delta in settlement.lp_deltas:
            lp_deltas.append({
                "pubkey": delta.pubkey,
                "pool_id": delta.pool_id,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            })
        for fill in settlement.fills:
            fills_summary.append({
                "intent_id": fill.intent_id,
                "action": fill.action.value,
                "amount_in_filled": fill.amount_in_filled,
                "amount_out_filled": fill.amount_out_filled,
                "fee_paid": fill.fee_paid,
                "protocol_fee_paid": fill.protocol_fee_paid,
                "amount0_used": fill.amount0_used,
                "amount1_used": fill.amount1_used,
                "lp_minted": fill.lp_minted,
                "amount0_out": fill.amount0_out,
                "amount1_out": fill.amount1_out,
                "lp_burned": fill.lp_burned,
                "reason": fill.reason,
            })
        if settlement.events is not None:
            for event in settlement.events:
                events.append(_canonical_bytes(event).hex())
    return {
        "fixture_id": fixture.fixture_id,
        "command_kind": fixture.command_kind,
        "category": fixture.category,
        "description": fixture.description,
        "accepted": result.ok,
        "error": result.error,
        "canonical_command_bytes": [b.hex() for b in command_bytes_list],
        "canonical_command_hash": sha256_hex(b"".join(command_bytes_list)),
        "command_root": command_root,
        "pre_state_root": pre_state_root,
        "pre_state_snapshot_bytes": pre_snapshot_bytes.hex(),
        "pre_state_snapshot_root": pre_snapshot_root,
        "pre_support_root_v4": pre_support_root_v4,
        "settlement_bytes": settlement_bytes.hex(),
        "settlement_hash": settlement_hash,
        "next_state_root": next_state_root,
        "next_state_snapshot_bytes": next_snapshot_bytes.hex(),
        "next_state_snapshot_root": next_snapshot_root,
        "next_support_root_v4": next_support_root_v4,
        "total_swap_fees": total_fees,
        "fee_split": fee_split,
        "nonce_ok": nonce_ok,
        "nonce_error": nonce_error,
        "next_nonces_hash": next_nonces_hash,
        "observable_projection": {
            "accept_reject_kind": "accept" if result.ok else "reject",
            "error": result.error,
            "balance_deltas": balance_deltas,
            "reserve_deltas": reserve_deltas,
            "lp_deltas": lp_deltas,
            "fills": fills_summary,
            "events": events,
            "next_state_root": next_state_root,
            "next_support_root_v4": next_support_root_v4,
            "total_swap_fees": total_fees,
            "fee_split": fee_split,
        },
        "version_deltas": {
            "support_root_version": 4,
            "snapshot_version": 4,
            "algorithm_id": "legacy_dex_step",
            "algorithm_version": 1,
            "schema_version": 1,
            "codec_version": 1,
        },
    }


def _source_tree_hash() -> str:
    """Compute a deterministic hash of the input source tree."""

    relevant_files: list[Path] = []
    for pattern in (
        "src/core/dex.py",
        "src/core/batch_clearing.py",
        "src/core/settlement.py",
        "src/core/settlement_strong_validator.py",
        "src/core/route_settlement.py",
        "src/core/fees.py",
        "src/core/liquidity.py",
        "src/core/cpmm.py",
        "src/state/intents.py",
        "src/state/balances.py",
        "src/state/pools.py",
        "src/state/lp.py",
        "src/state/nonces.py",
        "src/state/state_root.py",
        "src/state/support_root.py",
        "src/state/canonical.py",
        "src/state/legacy_state_snapshots.py",
        "src/integration/dex_snapshot.py",
        "src/integration/operations.py",
        "src/integration/dex_engine.py",
    ):
        path = _REPO_ROOT / pattern
        if path.exists():
            relevant_files.append(path)
    hasher = hashlib.sha256()
    for path in sorted(relevant_files):
        hasher.update(str(path).encode("utf-8"))
        hasher.update(b"\x00")
        hasher.update(path.read_bytes())
        hasher.update(b"\x00")
    return "0x" + hasher.hexdigest()


def _generator_hash() -> str:
    """Hash of this builder source."""

    return "0x" + hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()


def _git_head_sha() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=10,
        )
        return result.stdout.strip()
    except Exception:
        return ""


def _build_artifact() -> dict[str, Any]:
    fixtures = _build_fixture_inputs()
    fixture_results: list[dict[str, Any]] = []
    command_kinds_seen: set[str] = set()
    for fixture in fixtures:
        result = _execute_legacy(fixture)
        fixture_results.append(result)
        command_kinds_seen.add(fixture.command_kind)
    inventory = _build_command_inventory()
    artifact: dict[str, Any] = {
        "schema": _SCHEMA,
        "generator_hash": _generator_hash(),
        "source_tree_hash": _source_tree_hash(),
        "git_head_sha": _git_head_sha(),
        "python_version": platform.python_version(),
        "python_executable": sys.executable,
        "generation_command": "python3 tools/build_fcis_m5_p4a_baseline.py",
        "command_inventory": inventory,
        "fixtures": fixture_results,
        "fixture_count": len(fixture_results),
        "command_kinds_covered": sorted(command_kinds_seen),
    }
    artifact_bytes = _canonical_bytes(artifact)
    artifact["artifact_sha256"] = "0x" + hashlib.sha256(artifact_bytes).hexdigest()
    return artifact


def _build_command_inventory() -> list[dict[str, Any]]:
    """Source-derived command inventory from the mounted dispatch."""

    return [
        {
            "command_kind": "CREATE_POOL",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:178 IntentKind.CREATE_POOL",
            "dispatch": "compute_settlement -> _try_create_pool",
        },
        {
            "command_kind": "ADD_LIQUIDITY",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:752 IntentKind.ADD_LIQUIDITY",
            "dispatch": "compute_settlement -> _apply_add_liquidity",
        },
        {
            "command_kind": "REMOVE_LIQUIDITY",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:772 IntentKind.REMOVE_LIQUIDITY",
            "dispatch": "compute_settlement -> _apply_remove_liquidity",
        },
        {
            "command_kind": "SWAP_EXACT_IN",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:706 IntentKind.SWAP_EXACT_IN",
            "dispatch": "compute_settlement -> clear_batch_single_pool",
        },
        {
            "command_kind": "SWAP_EXACT_OUT",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:706 IntentKind.SWAP_EXACT_OUT",
            "dispatch": "compute_settlement -> clear_batch_single_pool",
        },
        {
            "command_kind": "ROUTE_EXACT_IN",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:182 is_route_intent_kind -> ROUTE_EXACT_IN",
            "dispatch": "compute_settlement -> _clear_route_intent_against_locals",
        },
        {
            "command_kind": "ROUTE_EXACT_OUT",
            "mounted": True,
            "supported": True,
            "classification": "supported_and_mounted",
            "source_evidence": "src/core/batch_clearing.py:182 is_route_intent_kind -> ROUTE_EXACT_OUT",
            "dispatch": "compute_settlement -> _clear_route_intent_against_locals",
        },
    ]


def _write_artifact(artifact: dict[str, Any]) -> None:
    _ARTIFACT_PATH.parent.mkdir(parents=True, exist_ok=True)
    artifact_bytes = canonical_json_bytes(artifact)
    _ARTIFACT_PATH.write_bytes(artifact_bytes)


def main() -> int:
    check_mode = "--check" in sys.argv
    artifact = _build_artifact()
    if check_mode:
        if not _ARTIFACT_PATH.exists():
            print("ERROR: baseline artifact does not exist", file=sys.stderr)
            return 1
        existing = _ARTIFACT_PATH.read_bytes()
        new_bytes = canonical_json_bytes(artifact)
        existing_hash = "0x" + hashlib.sha256(existing).hexdigest()
        new_hash = "0x" + hashlib.sha256(new_bytes).hexdigest()
        if existing != new_bytes:
            print(
                f"ERROR: baseline artifact changed (existing={existing_hash}, new={new_hash})",
                file=sys.stderr,
            )
            return 1
        print(f"OK: baseline artifact matches (sha256={new_hash})")
        return 0
    _write_artifact(artifact)
    print(f"OK: wrote {_ARTIFACT_PATH} (sha256={artifact['artifact_sha256']})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
