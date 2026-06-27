"""Conservative ZenoLedger conflict graph for scalable batch execution.

This module extracts the state cells touched by a ZenoLedger transaction. It is
an admission aid for parallel execution and proof planning. Unknown or malformed
intents are mapped to a global cell so they cannot be parallelized unsafely.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import hash_v0, tx_hash_v0
from src.state.pools import compute_pool_id

CONFLICT_GRAPH_SCHEMA_V0 = "zenodex/zeno_ledger/conflict_graph/v0"
CONFLICT_SCHEDULE_SCHEMA_V0 = "zenodex/zeno_ledger/conflict_schedule/v0"
GLOBAL_DEX_CELL_V0 = "global:dex_state"


def _mapping(value: object) -> Mapping[str, Any] | None:
    return value if isinstance(value, Mapping) else None


def _cell(kind: str, *parts: object) -> str:
    text_parts = [str(part) for part in parts if part is not None and str(part) != ""]
    if not text_parts:
        return kind
    return kind + ":" + ":".join(text_parts)


def _add_if_present(cells: set[str], kind: str, *parts: object) -> None:
    if all(part is not None and str(part) != "" for part in parts):
        cells.add(_cell(kind, *parts))


def _add_liquidity_balance_cells(
    cells: set[str],
    *,
    owner: object,
    asset0: object,
    asset1: object,
) -> None:
    """Add concrete balance cells for a liquidity intent.

    DbC precondition: callers pass the account whose token balances are mutated.
    DbC postcondition: both pool-asset balance cells are present when both assets
    are known; otherwise the global cell is present so scheduling is conservative.
    """

    _add_if_present(cells, "balance", owner, asset0)
    _add_if_present(cells, "balance", owner, asset1)
    # Liquidity execution resolves real assets from pool state, not intent extras.
    # Always include the global cell to prevent spoofed-asset underconflicts.
    cells.add(GLOBAL_DEX_CELL_V0)


def _shared_conflict_cells_v0(left_cells: set[str], right_cells: set[str]) -> list[str]:
    """Return shared conflict cells, treating the global cell as a wildcard.

    DbC invariant: any transaction mapped to the global cell conflicts with every
    other transaction, preventing unsafe parallel execution when state access is
    unknown or only partially known.
    """

    shared = left_cells & right_cells
    if shared:
        return sorted(shared)
    if GLOBAL_DEX_CELL_V0 in left_cells or GLOBAL_DEX_CELL_V0 in right_cells:
        return [GLOBAL_DEX_CELL_V0]
    return []


def _pool_id_for_create_pool(intent: Mapping[str, Any]) -> str | None:
    pool_id = intent.get("pool_id")
    if isinstance(pool_id, str) and pool_id:
        return pool_id
    asset0 = intent.get("asset0")
    asset1 = intent.get("asset1")
    fee_bps = intent.get("fee_bps")
    if not isinstance(asset0, str) or not isinstance(asset1, str):
        return None
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
        return None
    try:
        left, right = (asset0, asset1) if asset0 < asset1 else (asset1, asset0)
        return compute_pool_id(left, right, fee_bps)
    except (TypeError, ValueError):
        return None


def _extract_operation_intents_v0(tx: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    operations = _mapping(tx.get("operations"))
    if operations is None:
        return []
    intents: list[Mapping[str, Any]] = []
    for value in operations.values():
        if isinstance(value, list):
            for item in value:
                obj = _mapping(item)
                if obj is not None:
                    intents.append(obj)
        else:
            obj = _mapping(value)
            if obj is not None:
                intents.append(obj)
    return intents


def touched_cells_for_intent_v0(intent: Mapping[str, Any]) -> set[str]:
    """Return conservative state-cell keys touched by one DEX intent."""

    cells: set[str] = set()
    kind = str(intent.get("kind", "UNKNOWN"))
    sender = intent.get("sender_pubkey")
    recipient = intent.get("recipient", sender)
    _add_if_present(cells, "nonce", sender)

    if kind in {"SWAP_EXACT_IN", "SWAP_EXACT_OUT"}:
        pool_id = intent.get("pool_id")
        asset_in = intent.get("asset_in")
        asset_out = intent.get("asset_out")
        _add_if_present(cells, "pool", pool_id)
        _add_if_present(cells, "pool_reserve", pool_id, asset_in)
        _add_if_present(cells, "pool_reserve", pool_id, asset_out)
        _add_if_present(cells, "balance", sender, asset_in)
        _add_if_present(cells, "balance", recipient, asset_out)
        return cells or {GLOBAL_DEX_CELL_V0}

    if kind == "CREATE_POOL":
        pool_id = _pool_id_for_create_pool(intent)
        asset0 = intent.get("asset0")
        asset1 = intent.get("asset1")
        _add_if_present(cells, "pool", pool_id)
        _add_if_present(cells, "pool_reserve", pool_id, asset0)
        _add_if_present(cells, "pool_reserve", pool_id, asset1)
        _add_if_present(cells, "balance", sender, asset0)
        _add_if_present(cells, "balance", sender, asset1)
        _add_if_present(cells, "lp_position", recipient, pool_id)
        return cells or {GLOBAL_DEX_CELL_V0}

    if kind == "ADD_LIQUIDITY":
        pool_id = intent.get("pool_id")
        _add_if_present(cells, "pool", pool_id)
        _add_if_present(cells, "lp_position", recipient, pool_id)
        _add_if_present(cells, "liquidity_actor", sender, pool_id)
        _add_liquidity_balance_cells(
            cells,
            owner=sender,
            asset0=intent.get("asset0"),
            asset1=intent.get("asset1"),
        )
        return cells or {GLOBAL_DEX_CELL_V0}

    if kind == "REMOVE_LIQUIDITY":
        pool_id = intent.get("pool_id")
        _add_if_present(cells, "pool", pool_id)
        _add_if_present(cells, "lp_position", sender, pool_id)
        _add_if_present(cells, "balance_actor", recipient, pool_id)
        _add_liquidity_balance_cells(
            cells,
            owner=recipient,
            asset0=intent.get("asset0"),
            asset1=intent.get("asset1"),
        )
        return cells or {GLOBAL_DEX_CELL_V0}

    return {GLOBAL_DEX_CELL_V0, _cell("unknown_intent_kind", kind)}


def touched_cells_for_transaction_v0(tx: Mapping[str, Any]) -> set[str]:
    """Return conservative state-cell keys touched by one ZenoLedger transaction."""

    kind = tx.get("kind")
    if kind == "ZENODEX_TESTNET_FAUCET":
        cells = {_cell("testnet_faucet")}
        _add_if_present(cells, "balance", tx.get("to_pubkey"), tx.get("asset"))
        return cells

    if kind == "ZENODEX_TESTNET_TOKEN_CREATE":
        cells = {_cell("token_registry")}
        _add_if_present(cells, "token_symbol", tx.get("symbol"))
        _add_if_present(cells, "token_asset", tx.get("asset"))
        return cells

    intents = _extract_operation_intents_v0(tx)
    if not intents:
        return {GLOBAL_DEX_CELL_V0}
    cells: set[str] = set()
    for intent in intents:
        cells.update(touched_cells_for_intent_v0(intent))
    return cells or {GLOBAL_DEX_CELL_V0}


def transactions_conflict_v0(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
    """Return true when two transactions share at least one touched state cell."""

    left_cells = touched_cells_for_transaction_v0(left)
    right_cells = touched_cells_for_transaction_v0(right)
    return bool(_shared_conflict_cells_v0(left_cells, right_cells))


def build_conflict_graph_v0(transactions: list[object]) -> dict[str, Any]:
    """Build an ordered conflict graph over transaction touched-cell sets."""

    if not isinstance(transactions, list):
        raise TypeError("transactions must be a list")
    vertices: list[dict[str, Any]] = []
    for index, tx in enumerate(transactions):
        obj = _mapping(tx)
        if obj is None:
            cells = {GLOBAL_DEX_CELL_V0}
            tx_hash = hash_v0("malformed_tx_conflict_v0", {"index": index, "repr": repr(tx)})
        else:
            cells = touched_cells_for_transaction_v0(obj)
            tx_hash = tx_hash_v0(obj)
        vertices.append(
            {
                "index": index,
                "tx_hash": tx_hash,
                "touched_cells": sorted(cells),
                "touched_cell_count": len(cells),
            }
        )

    edges: list[dict[str, Any]] = []
    for left_index in range(len(vertices)):
        left_cells = set(vertices[left_index]["touched_cells"])
        for right_index in range(left_index + 1, len(vertices)):
            right_cells = set(vertices[right_index]["touched_cells"])
            shared = _shared_conflict_cells_v0(left_cells, right_cells)
            if shared:
                edges.append(
                    {
                        "left_index": left_index,
                        "right_index": right_index,
                        "shared_cells": shared,
                    }
                )

    parent = list(range(len(vertices)))

    def find(index: int) -> int:
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index

    def union(left: int, right: int) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    for edge in edges:
        union(int(edge["left_index"]), int(edge["right_index"]))

    components_by_root: dict[int, list[int]] = {}
    for index in range(len(vertices)):
        components_by_root.setdefault(find(index), []).append(index)
    components = [
        {
            "component_id": component_index,
            "transaction_indices": indices,
            "transaction_count": len(indices),
        }
        for component_index, indices in enumerate(sorted(components_by_root.values(), key=lambda items: items[0]))
    ]

    graph_body = {
        "schema": CONFLICT_GRAPH_SCHEMA_V0,
        "transaction_count": len(vertices),
        "vertices": vertices,
        "edges": edges,
        "edge_count": len(edges),
        "components": components,
        "component_count": len(components),
    }
    return {**graph_body, "conflict_graph_hash": hash_v0("conflict_graph_v0", graph_body)}


def build_conflict_schedule_v0(
    transactions: list[object],
    *,
    max_parallel_components: int | None = None,
) -> dict[str, Any]:
    """Build deterministic parallel execution waves from conflict components."""

    if max_parallel_components is not None and max_parallel_components <= 0:
        raise ValueError("max_parallel_components must be positive when provided")

    graph = build_conflict_graph_v0(transactions)
    vertices_by_index = {int(vertex["index"]): vertex for vertex in graph["vertices"]}
    tasks: list[dict[str, Any]] = []
    for component in graph["components"]:
        indices = [int(index) for index in component["transaction_indices"]]
        touched_cells: set[str] = set()
        tx_hashes: list[str] = []
        for index in indices:
            vertex = vertices_by_index[index]
            tx_hashes.append(str(vertex["tx_hash"]))
            touched_cells.update(str(cell) for cell in vertex["touched_cells"])
        tasks.append(
            {
                "task_id": len(tasks),
                "component_id": int(component["component_id"]),
                "transaction_indices": indices,
                "transaction_hashes": tx_hashes,
                "transaction_count": len(indices),
                "touched_cells": sorted(touched_cells),
                "touched_cell_count": len(touched_cells),
                "requires_sequential_order": len(indices) > 1,
            }
        )

    width = len(tasks) if max_parallel_components is None else max_parallel_components
    waves: list[dict[str, Any]] = []
    if tasks:
        for start in range(0, len(tasks), width):
            wave_tasks = tasks[start : start + width]
            waves.append(
                {
                    "wave_id": len(waves),
                    "task_ids": [int(task["task_id"]) for task in wave_tasks],
                    "component_ids": [int(task["component_id"]) for task in wave_tasks],
                    "transaction_indices": [
                        int(index)
                        for task in wave_tasks
                        for index in task["transaction_indices"]
                    ],
                    "parallel_task_count": len(wave_tasks),
                }
            )

    schedule_body = {
        "schema": CONFLICT_SCHEDULE_SCHEMA_V0,
        "schedule_mode": "connected_components",
        "conflict_graph_hash": graph["conflict_graph_hash"],
        "transaction_count": graph["transaction_count"],
        "edge_count": graph["edge_count"],
        "component_count": graph["component_count"],
        "task_count": len(tasks),
        "wave_count": len(waves),
        "max_parallel_components": max_parallel_components,
        "tasks": tasks,
        "waves": waves,
    }
    return {**schedule_body, "conflict_schedule_hash": hash_v0("conflict_schedule_v0", schedule_body)}
