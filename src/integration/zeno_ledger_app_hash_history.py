"""Merkle commitments for ZenoLedger app-hash histories."""

from __future__ import annotations

from typing import Any, Mapping, Sequence, TypedDict

from src.integration.zeno_ledger_v0 import ROOT_NBYTES, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

APP_HASH_HISTORY_MERKLE_PROOF_SCHEMA_V0 = (
    "zenodex.zeno_ledger.app_hash_history_merkle_proof.v0"
)


class AppHashHistoryRowV0(TypedDict):
    height: int
    app_hash: str


class CheckedRangeSummaryV0(TypedDict):
    from_height: int
    to_height: int
    height_count: int


def checked_range_summary_v0(checked_heights: Sequence[int]) -> CheckedRangeSummaryV0:
    """Compress a contiguous checked-height list into a canonical range summary."""

    heights = _require_nonempty_int_sequence(checked_heights, name="checked_heights")
    for index, height in enumerate(heights[1:], start=1):
        if height != heights[index - 1] + 1:
            raise ValueError("checked_heights must be contiguous")
    return {
        "from_height": heights[0],
        "to_height": heights[-1],
        "height_count": len(heights),
    }


def validate_checked_range_summary_v0(
    value: Mapping[str, Any],
    *,
    name: str = "checked_range",
) -> CheckedRangeSummaryV0:
    """Validate a compact contiguous checked-height range."""

    obj = _require_mapping(value, name=name)
    if set(obj.keys()) != {"from_height", "to_height", "height_count"}:
        raise ValueError(f"{name} keys mismatch")
    from_height = _require_nonnegative_int(obj.get("from_height"), name=f"{name}.from_height")
    to_height = _require_nonnegative_int(obj.get("to_height"), name=f"{name}.to_height")
    height_count = _require_positive_int(obj.get("height_count"), name=f"{name}.height_count")
    if to_height < from_height:
        raise ValueError(f"{name}.to_height must be >= from_height")
    if height_count != to_height - from_height + 1:
        raise ValueError(f"{name}.height_count must equal to_height - from_height + 1")
    return {
        "from_height": from_height,
        "to_height": to_height,
        "height_count": height_count,
    }


def checked_range_hash_v0(checked_range: Mapping[str, Any]) -> str:
    """Return the canonical commitment to a compact checked-height range."""

    return hash_v0(
        "checked_range_summary_v0",
        validate_checked_range_summary_v0(checked_range),
    )


def app_hash_history_merkle_root_v0(rows: Sequence[Mapping[str, Any]]) -> str:
    """Return the canonical Merkle root for ordered `(height, app_hash)` rows."""

    canonical_rows = _canonical_rows(rows, name="app_hash_history_rows")
    leaves = [_leaf_hash(row) for row in canonical_rows]
    return _root_from_leaves(leaves)


def build_app_hash_history_merkle_proof_v0(
    rows: Sequence[Mapping[str, Any]],
    *,
    snapshot_height: int,
) -> Mapping[str, Any]:
    """Build a deterministic inclusion proof for one app-hash history row."""

    canonical_rows = _canonical_rows(rows, name="app_hash_history_rows")
    selected_height = _require_nonnegative_int(snapshot_height, name="snapshot_height")
    index_by_height = {row["height"]: index for index, row in enumerate(canonical_rows)}
    if selected_height not in index_by_height:
        raise ValueError("snapshot_height must be covered by app_hash history")
    index = index_by_height[selected_height]
    leaves = [_leaf_hash(row) for row in canonical_rows]
    root = _root_from_leaves(leaves)
    siblings: list[dict[str, str]] = []
    level = list(leaves)
    position = index
    while len(level) > 1:
        if position % 2 == 0:
            sibling_index = position + 1
            side = "right"
        else:
            sibling_index = position - 1
            side = "left"
        sibling_hash = level[sibling_index] if sibling_index < len(level) else level[position]
        siblings.append({"side": side, "hash": sibling_hash})
        level = _next_level(level)
        position //= 2
    return {
        "schema": APP_HASH_HISTORY_MERKLE_PROOF_SCHEMA_V0,
        "root": root,
        "index": index,
        "total_rows": len(canonical_rows),
        "leaf": dict(canonical_rows[index]),
        "siblings": siblings,
    }


def verify_app_hash_history_merkle_proof_v0(
    proof: Mapping[str, Any],
    *,
    expected_root: str,
    checked_heights: Sequence[int],
    snapshot_height: int,
    last_app_hash: str,
) -> str:
    """Verify one app-hash history inclusion proof and return its app hash."""

    obj = _require_mapping(proof, name="app_hash_history_merkle_proof")
    if obj.get("schema") != APP_HASH_HISTORY_MERKLE_PROOF_SCHEMA_V0:
        raise ValueError("app_hash_history_merkle_proof schema mismatch")
    normalized_expected_root = _require_root(expected_root, name="expected_root")
    proof_root = _require_root(obj.get("root"), name="app_hash_history_merkle_proof.root")
    if proof_root != normalized_expected_root:
        raise ValueError("app_hash_history_merkle_proof root mismatch")
    heights = _require_nonempty_int_sequence(checked_heights, name="checked_heights")
    selected_height = _require_nonnegative_int(snapshot_height, name="snapshot_height")
    normalized_last_app_hash = _require_root(last_app_hash, name="last_app_hash")
    index = _require_nonnegative_int(obj.get("index"), name="app_hash_history_merkle_proof.index")
    total_rows = _require_positive_int(obj.get("total_rows"), name="app_hash_history_merkle_proof.total_rows")
    if total_rows != len(heights):
        raise ValueError("app_hash_history_merkle_proof total_rows must match checked_heights")
    if index >= total_rows:
        raise ValueError("app_hash_history_merkle_proof index out of bounds")
    if heights[index] != selected_height:
        raise ValueError("app_hash_history_merkle_proof index must match snapshot_height")

    return _verify_app_hash_history_merkle_proof_at_index(
        obj,
        normalized_expected_root=normalized_expected_root,
        selected_height=selected_height,
        expected_index=index,
        total_rows=total_rows,
        last_app_hash=normalized_last_app_hash,
    )


def verify_app_hash_history_merkle_proof_for_range_v0(
    proof: Mapping[str, Any],
    *,
    expected_root: str,
    checked_range: Mapping[str, Any],
    snapshot_height: int,
    last_app_hash: str,
) -> str:
    """Verify an app-hash proof using compact contiguous-range arithmetic."""

    obj = _require_mapping(proof, name="app_hash_history_merkle_proof")
    if obj.get("schema") != APP_HASH_HISTORY_MERKLE_PROOF_SCHEMA_V0:
        raise ValueError("app_hash_history_merkle_proof schema mismatch")
    normalized_expected_root = _require_root(expected_root, name="expected_root")
    proof_root = _require_root(obj.get("root"), name="app_hash_history_merkle_proof.root")
    if proof_root != normalized_expected_root:
        raise ValueError("app_hash_history_merkle_proof root mismatch")
    summary = validate_checked_range_summary_v0(checked_range)
    selected_height = _require_nonnegative_int(snapshot_height, name="snapshot_height")
    if selected_height < summary["from_height"] or selected_height > summary["to_height"]:
        raise ValueError("snapshot_height must be covered by checked_range")
    expected_index = selected_height - summary["from_height"]
    proof_index = _require_nonnegative_int(obj.get("index"), name="app_hash_history_merkle_proof.index")
    if proof_index != expected_index:
        raise ValueError("app_hash_history_merkle_proof index must match compact checked_range")
    total_rows = _require_positive_int(obj.get("total_rows"), name="app_hash_history_merkle_proof.total_rows")
    if total_rows != summary["height_count"]:
        raise ValueError("app_hash_history_merkle_proof total_rows must match checked_range height_count")
    normalized_last_app_hash = _require_root(last_app_hash, name="last_app_hash")
    return _verify_app_hash_history_merkle_proof_at_index(
        obj,
        normalized_expected_root=normalized_expected_root,
        selected_height=selected_height,
        expected_index=expected_index,
        total_rows=total_rows,
        last_app_hash=normalized_last_app_hash,
    )


def _verify_app_hash_history_merkle_proof_at_index(
    obj: Mapping[str, Any],
    *,
    normalized_expected_root: str,
    selected_height: int,
    expected_index: int,
    total_rows: int,
    last_app_hash: str,
) -> str:
    leaf = _canonical_row(
        _require_mapping(obj.get("leaf"), name="app_hash_history_merkle_proof.leaf"),
        name="app_hash_history_merkle_proof.leaf",
    )
    if leaf["height"] != selected_height:
        raise ValueError("app_hash_history_merkle_proof leaf height mismatch")
    if expected_index == total_rows - 1 and leaf["app_hash"] != last_app_hash:
        raise ValueError("app_hash_history_merkle_proof final leaf must match last_app_hash")

    siblings_raw = obj.get("siblings")
    if not isinstance(siblings_raw, list):
        raise ValueError("app_hash_history_merkle_proof.siblings must be a list")
    computed = _leaf_hash(leaf)
    position = expected_index
    width = total_rows
    sibling_index = 0
    while width > 1:
        if sibling_index >= len(siblings_raw):
            raise ValueError("app_hash_history_merkle_proof missing sibling")
        sibling = _require_mapping(
            siblings_raw[sibling_index],
            name=f"app_hash_history_merkle_proof.siblings[{sibling_index}]",
        )
        side = sibling.get("side")
        if side not in {"left", "right"}:
            raise ValueError("app_hash_history_merkle_proof sibling side mismatch")
        sibling_hash = _require_root(
            sibling.get("hash"),
            name=f"app_hash_history_merkle_proof.siblings[{sibling_index}].hash",
        )
        expected_side = "right" if position % 2 == 0 else "left"
        if side != expected_side:
            raise ValueError("app_hash_history_merkle_proof sibling side mismatch")
        computed = (
            _node_hash(sibling_hash, computed)
            if side == "left"
            else _node_hash(computed, sibling_hash)
        )
        position //= 2
        width = (width + 1) // 2
        sibling_index += 1
    if sibling_index != len(siblings_raw):
        raise ValueError("app_hash_history_merkle_proof has extra siblings")
    root = hash_v0(
        "app_hash_history_merkle_root_v0",
        {"leaf_count": total_rows, "root": computed},
    )
    if root != normalized_expected_root:
        raise ValueError("app_hash_history_merkle_proof path root mismatch")
    return leaf["app_hash"]


def _canonical_rows(rows: object, *, name: str) -> list[AppHashHistoryRowV0]:
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes, bytearray)) or not rows:
        raise ValueError(f"{name} must be a non-empty sequence")
    out: list[AppHashHistoryRowV0] = []
    seen: set[int] = set()
    previous_height: int | None = None
    for index, raw in enumerate(rows):
        row = _canonical_row(_require_mapping(raw, name=f"{name}[{index}]"), name=f"{name}[{index}]")
        height = row["height"]
        if height in seen:
            raise ValueError(f"{name} heights must be unique")
        if previous_height is not None and height <= previous_height:
            raise ValueError(f"{name} heights must be strictly increasing")
        seen.add(height)
        previous_height = height
        out.append(row)
    return out


def _canonical_row(row: Mapping[str, Any], *, name: str) -> AppHashHistoryRowV0:
    if set(row.keys()) != {"height", "app_hash"}:
        raise ValueError(f"{name} keys mismatch")
    return {
        "height": _require_nonnegative_int(row.get("height"), name=f"{name}.height"),
        "app_hash": _require_root(row.get("app_hash"), name=f"{name}.app_hash"),
    }


def _root_from_leaves(leaves: Sequence[str]) -> str:
    if not leaves:
        raise ValueError("app_hash_history_merkle_root requires at least one leaf")
    level = list(leaves)
    while len(level) > 1:
        level = _next_level(level)
    return hash_v0(
        "app_hash_history_merkle_root_v0",
        {"leaf_count": len(leaves), "root": level[0]},
    )


def _next_level(level: Sequence[str]) -> list[str]:
    out: list[str] = []
    for index in range(0, len(level), 2):
        left = _require_root(level[index], name=f"merkle_level[{index}]")
        right = (
            _require_root(level[index + 1], name=f"merkle_level[{index + 1}]")
            if index + 1 < len(level)
            else left
        )
        out.append(_node_hash(left, right))
    return out


def _leaf_hash(row: Mapping[str, Any]) -> str:
    return hash_v0("app_hash_history_merkle_leaf_v0", dict(row))


def _node_hash(left: str, right: str) -> str:
    return hash_v0(
        "app_hash_history_merkle_node_v0",
        {"left": _require_root(left, name="merkle_node.left"), "right": _require_root(right, name="merkle_node.right")},
    )


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    return canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_nonnegative_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be a positive int")
    return out


def _require_nonempty_int_sequence(value: object, *, name: str) -> list[int]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)) or not value:
        raise ValueError(f"{name} must be a non-empty int sequence")
    out: list[int] = []
    for index, item in enumerate(value):
        height = _require_nonnegative_int(item, name=f"{name}[{index}]")
        if index > 0 and height <= out[-1]:
            raise ValueError(f"{name} must be strictly increasing")
        out.append(height)
    return out
