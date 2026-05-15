from __future__ import annotations

from src.integration.zeno_ledger_conflict_graph_v0 import (
    GLOBAL_DEX_CELL_V0,
    build_conflict_graph_v0,
    touched_cells_for_transaction_v0,
    transactions_conflict_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.pools import compute_pool_id


SENDER_A = "0x" + "aa" * 48
SENDER_B = "0x" + "bb" * 48
ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ASSET_C = "0x" + "33" * 32


def _swap_tx(*, sender: str, pool_id: str, asset_in: str, asset_out: str, nonce: int) -> dict[str, object]:
    return {
        "tx_id": f"swap-{nonce}",
        "tx_sender_pubkey": sender,
        "operations": {
            "2": [
                {
                    "kind": "SWAP_EXACT_IN",
                    "sender_pubkey": sender,
                    "recipient": sender,
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
    assert "pool:" + pool_id in graph["edges"][0]["shared_cells"]


def test_disjoint_pools_with_disjoint_users_do_not_conflict() -> None:
    pool_ab = compute_pool_id(ASSET_A, ASSET_B, 30)
    pool_bc = compute_pool_id(ASSET_B, ASSET_C, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_ab, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_bc, asset_in=ASSET_C, asset_out=ASSET_B, nonce=2)
    assert not transactions_conflict_v0(left, right)
    graph = build_conflict_graph_v0([left, right])
    assert graph["edge_count"] == 0


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


def test_graph_hash_is_mutation_sensitive() -> None:
    pool_id = compute_pool_id(ASSET_A, ASSET_B, 30)
    left = _swap_tx(sender=SENDER_A, pool_id=pool_id, asset_in=ASSET_A, asset_out=ASSET_B, nonce=1)
    right = _swap_tx(sender=SENDER_B, pool_id=pool_id, asset_in=ASSET_B, asset_out=ASSET_A, nonce=2)
    base = build_conflict_graph_v0([left, right])
    mutated = build_conflict_graph_v0([right, left])
    assert base["conflict_graph_hash"] != mutated["conflict_graph_hash"]

