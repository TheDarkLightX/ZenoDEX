from __future__ import annotations

import pytest

import src.integration.zeno_ledger_conflict_graph_v0 as conflict_graph
from src.integration.zeno_ledger_conflict_graph_v0 import (
    GLOBAL_DEX_CELL_V0,
    build_conflict_graph_v0,
    build_conflict_schedule_v0,
    touched_cells_for_transaction_v0,
    transactions_conflict_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.pools import compute_pool_id
from tools.zeno_ledger_conflict_graph import build_conflict_graph_report_v0

SENDER_A = "0x" + "aa" * 48
SENDER_B = "0x" + "bb" * 48
ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ASSET_C = "0x" + "33" * 32


def _swap_tx(
    *,
    sender: str,
    pool_id: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
    recipient: str | None = None,
) -> dict[str, object]:
    return {
        "tx_id": f"swap-{nonce}",
        "tx_sender_pubkey": sender,
        "operations": {
            "2": [
                {
                    "kind": "SWAP_EXACT_IN",
                    "sender_pubkey": sender,
                    "recipient": recipient or sender,
                    "pool_id": pool_id,
                    "asset_in": asset_in,
                    "asset_out": asset_out,
                    "amount_in": 10,
                    "min_amount_out": 1,
                    "nonce": nonce,
                }
            ]
        },
    }


def test_same_pool_swaps_conflict_even_for_different_users() -> None:
    pool_id = compute_pool_id(ASSET_A, ASSET_B, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_id, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_id, asset_in=ASSET_B, asset_out=ASSET_A, nonce=2)
    assert transactions_conflict_v0(left, right)
    graph = build_conflict_graph_v0([left, right])
    assert graph["edge_count"] == 1
    assert graph["component_count"] == 1
    assert "pool:" + pool_id in graph["edges"][0]["shared_cells"]


def test_disjoint_pools_with_disjoint_users_do_not_conflict() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_bc = compute_pool_id(ASSET_B, ASSET_C, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_ab, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_bc, asset_in=ASSET_C, asset_out=ASSET_B, nonce=2)
    assert not transactions_conflict_v0(left, right)
    graph = build_conflict_graph_v0([left, right])
    assert graph["edge_count"] == 0
    assert graph["component_count"] == 2
    schedule = build_conflict_schedule_v0([left, right])
    assert schedule["wave_count"] == 1
    assert schedule["waves"][0]["parallel_task_count"] == 2
    assert schedule["tasks"][0]["requires_sequential_order"] is False
    assert schedule["tasks"][1]["requires_sequential_order"] is False


def test_conflict_schedule_chunks_parallel_components_when_width_is_limited() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_bc = compute_pool_id(ASSET_B, ASSET_C, 30)
    first = _swap_tx(sender=SENDER_A, pool_id=pool_ab, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    second = _swap_tx(sender=SENDER_B, pool_id=pool_bc, asset_in=ASSET_C, asset_out=ASSET_B, nonce=2)
    schedule = build_conflict_schedule_v0([first, second], max_parallel_components=1)
    assert schedule["task_count"] == 2
    assert schedule["wave_count"] == 2
    assert schedule["waves"][0]["task_ids"] == [0]
    assert schedule["waves"][1]["task_ids"] == [1]


def test_conflict_schedule_marks_multi_tx_components_as_sequential() -> None:
    pool_id = compute_pool_id(ASSET_A, ASSET_B, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_id, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_id, asset_in=ASSET_B, asset_out=ASSET_A, nonce=2)
    schedule = build_conflict_schedule_v0([left, right])
    assert schedule["task_count"] == 1
    assert schedule["wave_count"] == 1
    assert schedule["tasks"][0]["transaction_indices"] == [0, 1]
    assert schedule["tasks"][0]["requires_sequential_order"] is True


def _liquidity_tx(
    *,
    kind: str,
    sender: str,
    recipient: str,
    pool_id: str,
    nonce: int,
    asset0: str | None = None,
    asset1: str | None = None,
) -> dict[str, object]:
    intent: dict[str, object] = {
        "kind": kind,
        "sender_pubkey": sender,
        "recipient": recipient,
        "pool_id": pool_id,
        "nonce": nonce,
    }
    if asset0 is not None:
        intent["asset0"] = asset0
    if asset1 is not None:
        intent["asset1"] = asset1
    return {
        "tx_id": f"liquidity-{kind.lower()}-{nonce}",
        "tx_sender_pubkey": sender,
        "operations": {"2": [intent]},
    }


def test_add_liquidity_conflicts_with_swap_crediting_sender_pool_asset() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_ca = compute_pool_id(ASSET_A, ASSET_C, 30)
    add_liquidity = _liquidity_tx(
        kind="ADD_LIQUIDITY",
        sender=SENDER_A,
        recipient=SENDER_A,
        pool_id=pool_ab,
        nonce=1,
        asset0=ASSET_A,
        asset1=ASSET_B,
    )
    swap_crediting_sender = _swap_tx(
        sender=SENDER_B,
        pool_id=pool_ca,
        asset_in=ASSET_C,
        asset_out=ASSET_A,
        nonce=2,
        recipient=SENDER_A,
    )

    assert transactions_conflict_v0(add_liquidity, swap_crediting_sender)
    graph = build_conflict_graph_v0([add_liquidity, swap_crediting_sender])
    assert graph["edge_count"] == 1
    assert f"balance:{SENDER_A}:{ASSET_A}" in graph["edges"][0]["shared_cells"]
    schedule = build_conflict_schedule_v0([add_liquidity, swap_crediting_sender])
    assert schedule["task_count"] == 1


def test_remove_liquidity_conflicts_with_swap_debiting_recipient_pool_asset() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_ac = compute_pool_id(ASSET_A, ASSET_C, 30)
    remove_liquidity = _liquidity_tx(
        kind="REMOVE_LIQUIDITY",
        sender=SENDER_B,
        recipient=SENDER_A,
        pool_id=pool_ab,
        nonce=1,
        asset0=ASSET_A,
        asset1=ASSET_B,
    )
    swap_debiting_recipient = _swap_tx(
        sender=SENDER_A,
        pool_id=pool_ac,
        asset_in=ASSET_A,
        asset_out=ASSET_C,
        nonce=2,
    )

    assert transactions_conflict_v0(remove_liquidity, swap_debiting_recipient)
    graph = build_conflict_graph_v0([remove_liquidity, swap_debiting_recipient])
    assert graph["edge_count"] == 1
    assert f"balance:{SENDER_A}:{ASSET_A}" in graph["edges"][0]["shared_cells"]


def test_liquidity_without_pool_assets_uses_global_wildcard_conflict() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_ca = compute_pool_id(ASSET_A, ASSET_C, 30)
    add_liquidity = _liquidity_tx(
        kind="ADD_LIQUIDITY",
        sender=SENDER_A,
        recipient=SENDER_A,
        pool_id=pool_ab,
        nonce=1,
    )
    swap = _swap_tx(
        sender=SENDER_B,
        pool_id=pool_ca,
        asset_in=ASSET_C,
        asset_out=ASSET_A,
        nonce=2,
    )

    assert GLOBAL_DEX_CELL_V0 in touched_cells_for_transaction_v0(add_liquidity)
    assert transactions_conflict_v0(add_liquidity, swap)
    graph = build_conflict_graph_v0([add_liquidity, swap])
    assert graph["edge_count"] == 1
    assert graph["edges"][0]["shared_cells"] == [GLOBAL_DEX_CELL_V0]




def test_liquidity_with_spoofed_assets_still_conflicts_conservatively() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_ca = compute_pool_id(ASSET_A, ASSET_C, 30)
    add_liquidity_spoofed = _liquidity_tx(
        kind="ADD_LIQUIDITY",
        sender=SENDER_A,
        recipient=SENDER_A,
        pool_id=pool_ab,
        nonce=1,
        asset0=ASSET_C,
        asset1=ASSET_C,
    )
    swap_touching_real_asset = _swap_tx(
        sender=SENDER_B,
        pool_id=pool_ca,
        asset_in=ASSET_C,
        asset_out=ASSET_A,
        nonce=2,
        recipient=SENDER_A,
    )

    touched = touched_cells_for_transaction_v0(add_liquidity_spoofed)
    assert GLOBAL_DEX_CELL_V0 in touched
    assert transactions_conflict_v0(add_liquidity_spoofed, swap_touching_real_asset)

def test_token_create_conflicts_by_registry_symbol_or_asset() -> None:
    asset = hash_v0("test_asset", {"symbol": "tMANGO"})
    left = {
        "kind": "ZENODEX_TESTNET_TOKEN_CREATE",
        "asset": asset,
        "symbol": "tMANGO",
    }
    same_symbol = {
        "kind": "ZENODEX_TESTNET_TOKEN_CREATE",
        "asset": hash_v0("test_asset", {"symbol": "tOTHER"}),
        "symbol": "tMANGO",
    }
    same_asset = {
        "kind": "ZENODEX_TESTNET_TOKEN_CREATE",
        "asset": asset,
        "symbol": "tOTHER",
    }
    assert transactions_conflict_v0(left, same_symbol)
    assert transactions_conflict_v0(left, same_asset)


def test_unknown_or_malformed_transactions_are_global_conflicts() -> None:
    unknown = {"operations": {"2": [{"kind": "FUTURE_KIND"}]}}
    malformed = {"tx_id": "missing-operations"}
    assert GLOBAL_DEX_CELL_V0 in touched_cells_for_transaction_v0(unknown)
    assert GLOBAL_DEX_CELL_V0 in touched_cells_for_transaction_v0(malformed)
    assert transactions_conflict_v0(unknown, malformed)


def test_create_pool_conflict_cells_surface_compute_pool_id_programmer_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tx = {
        "operations": {
            "2": [
                {
                    "kind": "CREATE_POOL",
                    "sender_pubkey": SENDER_A,
                    "asset0": ASSET_A,
                    "asset1": ASSET_B,
                    "fee_bps": 30,
                    "nonce": 1,
                }
            ]
        }
    }

    def broken_compute_pool_id(*args, **kwargs):  # noqa: ANN001, ANN002, ANN003
        raise RuntimeError("synthetic compute_pool_id bug")

    monkeypatch.setattr(conflict_graph, "compute_pool_id", broken_compute_pool_id)

    with pytest.raises(RuntimeError, match="synthetic compute_pool_id bug"):
        touched_cells_for_transaction_v0(tx)


def test_graph_hash_is_mutation_sensitive() -> None:
    pool_id = compute_pool_id(ASSET_A, ASSET_B, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_id, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_id, asset_in=ASSET_B, asset_out=ASSET_A, nonce=2)
    base = build_conflict_graph_v0([left, right])
    mutated = build_conflict_graph_v0([right, left])
    assert base["conflict_graph_hash"] != mutated["conflict_graph_hash"]


def test_conflict_graph_report_reads_transaction_list(tmp_path) -> None:
    pool_id = compute_pool_id(ASSET_A, ASSET_B, 30)
    txs = [
        _swap_tx(sender=SENDER_A, pool_id=pool_id, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1),
        _swap_tx(sender=SENDER_B, pool_id=pool_id, asset_in=ASSET_B, asset_out=ASSET_A, nonce=2),
    ]
    txs_path = tmp_path / "txs.json"
    import json

    txs_path.write_text(json.dumps(txs, sort_keys=True), encoding="utf-8")
    report = build_conflict_graph_report_v0(txs_path=txs_path)
    assert report["ok"] is True
    assert report["transaction_count"] == 2
    assert report["edge_count"] == 1
    assert report["parallel_component_count"] == 1
    assert report["conflict_schedule"]["task_count"] == 1
