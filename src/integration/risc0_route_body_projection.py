"""Deterministic projection from local route-body ops to RISC0 proof-v1 intents."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from copy import deepcopy
from typing import Any

from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.integration.risc0_tx_order_body_summary import tx_order_inputs_from_transactions_v1

PROOF_INTENT_OPERATION_KEY = "2"
ROUTE_BODY_OPERATION_KEY = "5"
ROUTE_BODY_PROJECTION_CONTRACT_SCHEMA = "zenodex.risc0.route_body_projection_contract.v1"
ROUTE_BODY_PROJECTION_CONTRACT_VERSION = 1
ROUTE_BODY_PROJECTION_CONTRACT_SEMANTIC_TAG = (
    "operations[5].route_body -> operations[2].proof_v1; "
    "sender unified; signed route-body pairs require payload preservation; "
    "embedded signatures require payload preservation; "
    "explicit RISC0 route quote-receipt binding hash required; "
    "one-hop legs; canonical leg_indices; totals normalized; "
    "tx_execution_order summary preserved"
)
U32_MAX = (1 << 32) - 1
U128_MAX = (1 << 128) - 1


def route_body_projection_contract_v1() -> dict[str, Any]:
    """Return the host-side projection contract bound into smoke reports."""

    return {
        "schema": ROUTE_BODY_PROJECTION_CONTRACT_SCHEMA,
        "schema_version": ROUTE_BODY_PROJECTION_CONTRACT_VERSION,
        "proof_intent_operation_key": PROOF_INTENT_OPERATION_KEY,
        "route_body_operation_key": ROUTE_BODY_OPERATION_KEY,
        "semantic_tag": ROUTE_BODY_PROJECTION_CONTRACT_SEMANTIC_TAG,
    }


def route_body_projection_contract_hash_v1() -> str:
    """Hash the projection semantics the host checker applies."""

    payload = json.dumps(
        route_body_projection_contract_v1(),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def route_body_projection_signing_dict_v1(intent: Mapping[str, Any]) -> dict[str, Any]:
    """Return the DEX intent signing dict used for projection-authority checks."""

    # Engine signature verification strips transport-only receipt bytes before
    # building the canonical signing payload. Mirror that boundary here so a
    # signed route body can be projected only when it already authorizes the
    # proof-v1 route intent fields.
    signature_view = {
        key: value
        for key, value in dict(intent).items()
        if key not in {"quote_receipt", "signature"}
    }
    return build_dex_intent_signing_dict_v1(signature_view)


def project_route_body_transactions_to_proof_v1(
    transactions: object,
) -> tuple[dict[str, Any], ...]:
    """Project route-body transactions into Rust proof-v1 parseable txs.

    The projection is deliberately fail-closed. It preserves transactions that
    do not carry local route-body operations, and it rejects ambiguous mixed
    proof-intent plus route-body transactions.
    """

    if not isinstance(transactions, list):
        raise TypeError("transactions must be a list")
    return tuple(
        project_route_body_transaction_to_proof_v1(tx, tx_index=tx_index)
        for tx_index, tx in enumerate(transactions)
    )


def project_route_body_transaction_to_proof_v1(
    tx: object,
    *,
    tx_index: int,
) -> dict[str, Any]:
    """Project one transaction's `operations['5']` route body into `operations['2']`."""

    tx_obj = _require_mapping(tx, f"transactions[{tx_index}]")
    operations = _require_mapping(
        tx_obj.get("operations"),
        f"transactions[{tx_index}].operations",
    )
    raw_routes = operations.get(ROUTE_BODY_OPERATION_KEY)
    if raw_routes is None:
        return deepcopy(dict(tx_obj))
    routes = _require_list(
        raw_routes,
        f"transactions[{tx_index}].operations['{ROUTE_BODY_OPERATION_KEY}']",
    )
    if not routes:
        return _copy_without_empty_route_key(tx_obj, operations)

    existing_proof_ops = operations.get(PROOF_INTENT_OPERATION_KEY)
    if existing_proof_ops not in (None, []):
        raise ValueError(
            f"transactions[{tx_index}] cannot mix operations['{PROOF_INTENT_OPERATION_KEY}'] "
            f"with operations['{ROUTE_BODY_OPERATION_KEY}']"
        )

    sender = _tx_sender_identity(tx_obj, tx_index=tx_index)
    projected_ops = dict(operations)
    projected_ops.pop(ROUTE_BODY_OPERATION_KEY, None)
    projected_ops[PROOF_INTENT_OPERATION_KEY] = [
        _project_route_operation(
            op,
            tx_sender=sender,
            op_path=f"transactions[{tx_index}].operations['{ROUTE_BODY_OPERATION_KEY}'][{op_index}]",
        )
        for op_index, op in enumerate(routes)
    ]

    out = deepcopy(dict(tx_obj))
    out["sender_pubkey"] = sender
    out["tx_sender_pubkey"] = sender
    out["operations"] = projected_ops
    _require_tx_order_summary_preserved(tx_obj, out, tx_index=tx_index)
    return out


def _copy_without_empty_route_key(
    tx_obj: Mapping[str, Any],
    operations: Mapping[str, Any],
) -> dict[str, Any]:
    out = deepcopy(dict(tx_obj))
    next_ops = dict(operations)
    next_ops.pop(ROUTE_BODY_OPERATION_KEY, None)
    out["operations"] = next_ops
    return out


def _project_route_operation(
    op: object,
    *,
    tx_sender: str,
    op_path: str,
) -> dict[str, Any]:
    op_obj = _route_op_with_envelope_signature(op, op_path=op_path)
    op_sender = op_obj.get("sender_pubkey")
    if op_sender is not None:
        op_sender_str = _require_non_empty_str(op_sender, f"{op_path}.sender_pubkey")
        if op_sender_str != tx_sender:
            raise ValueError(f"{op_path}.sender_pubkey must match transaction sender")

    receipt = _require_mapping(op_obj.get("quote_receipt"), f"{op_path}.quote_receipt")
    body = _require_mapping(receipt.get("body"), f"{op_path}.quote_receipt.body")
    kind = _proof_route_kind(op_obj.get("kind"), f"{op_path}.kind")
    quote_receipt_hash = _risc0_route_binding_hash(op_obj, receipt, op_path=op_path)
    legs = _route_legs(op_obj, body, op_path=op_path)
    _verify_receipt_pool_map(body, legs, op_path=op_path)
    leg_indices = _leg_indices(op_obj.get("leg_indices"), leg_count=len(legs), op_path=op_path)

    projected: dict[str, Any] = {
        "module": _require_non_empty_str(op_obj.get("module"), f"{op_path}.module"),
        "version": _require_non_empty_str(op_obj.get("version"), f"{op_path}.version"),
        "kind": kind,
        "intent_id": _require_non_empty_str(op_obj.get("intent_id"), f"{op_path}.intent_id"),
        "sender_pubkey": tx_sender,
        "deadline": _require_u64(op_obj.get("deadline"), f"{op_path}.deadline"),
        "quote_receipt_hash": quote_receipt_hash,
        "quote_receipt": deepcopy(dict(receipt)),
        "asset_in": _body_or_op_str(op_obj, body, "asset_in", op_path=op_path),
        "asset_out": _body_or_op_str(op_obj, body, "asset_out", op_path=op_path),
        "leg_indices": leg_indices,
        "legs": legs,
        "recipient": _require_non_empty_str(op_obj.get("recipient"), f"{op_path}.recipient"),
    }
    projected.update(_route_totals(op_obj, body, kind=kind, op_path=op_path))
    if "signature" in op_obj:
        _require_projection_preserves_signature_payload(op_obj, projected, op_path=op_path)
    return projected


def _route_op_with_envelope_signature(op: object, *, op_path: str) -> Mapping[str, Any]:
    if not isinstance(op, list):
        return _require_mapping(op, op_path)
    if len(op) != 2:
        raise ValueError(f"{op_path} signed route-body pair must be [route_body, signature]")
    route = _require_mapping(op[0], f"{op_path}[0]")
    signature = _require_non_empty_str(op[1], f"{op_path}[1]")
    if "signature" in route:
        raise ValueError(f"{op_path}[0].signature must not be duplicated by signed route-body pair")
    route_with_signature = dict(route)
    route_with_signature["signature"] = signature
    return route_with_signature


def _require_projection_preserves_signature_payload(
    op_obj: Mapping[str, Any],
    projected: Mapping[str, Any],
    *,
    op_path: str,
) -> None:
    try:
        local_signing = route_body_projection_signing_dict_v1(op_obj)
        projected_signing = route_body_projection_signing_dict_v1(projected)
    except Exception as exc:
        raise ValueError(f"{op_path} signed route-body payload is not projection-safe") from exc
    if local_signing != projected_signing:
        raise ValueError(
            f"{op_path} embedded signature does not authorize projected proof-v1 route intent; "
            "sign the projected proof-v1 route intent or include projection-equivalent route fields"
        )


def _require_tx_order_summary_preserved(
    original: Mapping[str, Any],
    projected: Mapping[str, Any],
    *,
    tx_index: int,
) -> None:
    original_summary = tx_order_inputs_from_transactions_v1([deepcopy(dict(original))])
    projected_summary = tx_order_inputs_from_transactions_v1([deepcopy(dict(projected))])
    if original_summary != projected_summary:
        raise ValueError(
            f"transactions[{tx_index}] route-body projection must preserve tx_execution_order summary"
        )


def _tx_sender_identity(tx_obj: Mapping[str, Any], *, tx_index: int) -> str:
    tx_sender = tx_obj.get("tx_sender_pubkey")
    legacy_sender = tx_obj.get("sender_pubkey")
    if tx_sender is not None:
        sender = _require_non_empty_str(
            tx_sender,
            f"transactions[{tx_index}].tx_sender_pubkey",
        )
        if legacy_sender is not None:
            legacy = _require_non_empty_str(
                legacy_sender,
                f"transactions[{tx_index}].sender_pubkey",
            )
            if legacy != sender:
                raise ValueError(f"transactions[{tx_index}].sender_pubkey must match tx_sender_pubkey")
        return sender
    if legacy_sender is not None:
        return _require_non_empty_str(legacy_sender, f"transactions[{tx_index}].sender_pubkey")
    raise ValueError(f"transactions[{tx_index}] missing sender_pubkey or tx_sender_pubkey")


def _proof_route_kind(value: object, path: str) -> str:
    kind = _require_non_empty_str(value, path)
    if kind not in {"ROUTE_EXACT_IN", "ROUTE_EXACT_OUT"}:
        raise ValueError(f"{path} must be ROUTE_EXACT_IN or ROUTE_EXACT_OUT")
    return kind


def _risc0_route_binding_hash(
    op: Mapping[str, Any],
    receipt: Mapping[str, Any],
    *,
    op_path: str,
) -> str:
    explicit = op.get("quote_receipt_hash")
    binding = receipt.get("risc0_route_quote_receipt_binding_hash")
    if explicit is not None:
        explicit_hash = _require_non_empty_str(explicit, f"{op_path}.quote_receipt_hash")
        if binding is not None:
            binding_hash = _require_non_empty_str(
                binding,
                f"{op_path}.quote_receipt.risc0_route_quote_receipt_binding_hash",
            )
            if binding_hash != explicit_hash:
                raise ValueError(f"{op_path}.quote_receipt_hash must match receipt RISC0 binding hash")
        return explicit_hash
    if binding is None:
        raise ValueError(
            f"{op_path}.quote_receipt_hash or "
            "quote_receipt.risc0_route_quote_receipt_binding_hash is required"
        )
    return _require_non_empty_str(
        binding,
        f"{op_path}.quote_receipt.risc0_route_quote_receipt_binding_hash",
    )


def _route_legs(
    op: Mapping[str, Any],
    body: Mapping[str, Any],
    *,
    op_path: str,
) -> list[dict[str, Any]]:
    raw_legs = op.get("legs", body.get("legs"))
    legs = _require_list(raw_legs, f"{op_path}.legs")
    if not legs:
        raise ValueError(f"{op_path}.legs must be non-empty")
    projected: list[dict[str, Any]] = []
    for leg_index, leg in enumerate(legs):
        leg_obj = _require_mapping(leg, f"{op_path}.legs[{leg_index}]")
        hops = _require_list(leg_obj.get("hops"), f"{op_path}.legs[{leg_index}].hops")
        if len(hops) != 1:
            raise ValueError(f"{op_path}.legs[{leg_index}].hops must contain exactly one hop")
        hop = _require_mapping(hops[0], f"{op_path}.legs[{leg_index}].hops[0]")
        pool_id = _require_non_empty_str(hop.get("pool_id"), f"{op_path}.legs[{leg_index}].hops[0].pool_id")
        projected.append({"hops": [{"pool_id": pool_id}]})
    return projected


def _verify_receipt_pool_map(
    body: Mapping[str, Any],
    legs: Sequence[Mapping[str, Any]],
    *,
    op_path: str,
) -> None:
    pools = _require_mapping(body.get("pools"), f"{op_path}.quote_receipt.body.pools")
    pool_map_ids = {pool_id for pool_id in pools if isinstance(pool_id, str)}
    leg_ids = {
        str(hop["pool_id"])
        for leg in legs
        for hop in _require_list(leg.get("hops"), f"{op_path}.legs.hops")
    }
    if pool_map_ids != leg_ids:
        raise ValueError(f"{op_path}.quote_receipt body pool map must match route legs")


def _leg_indices(value: object, *, leg_count: int, op_path: str) -> list[int]:
    if value is None:
        return list(range(leg_count))
    entries = _require_list(value, f"{op_path}.leg_indices")
    indices = [_require_u32(entry, f"{op_path}.leg_indices[{index}]") for index, entry in enumerate(entries)]
    expected = list(range(leg_count))
    if indices != expected:
        raise ValueError(f"{op_path}.leg_indices must cover route legs in order")
    return indices


def _route_totals(
    op: Mapping[str, Any],
    body: Mapping[str, Any],
    *,
    kind: str,
    op_path: str,
) -> dict[str, int]:
    if kind == "ROUTE_EXACT_IN":
        return {
            "total_amount_in": _require_positive_u128(
                _field_or_body(op, body, "total_amount_in", "amount_in"),
                f"{op_path}.total_amount_in",
            ),
            "total_min_amount_out": _require_u128(
                op.get("total_min_amount_out", op.get("min_amount_out")),
                f"{op_path}.total_min_amount_out",
            ),
            "total_amount_out": 0,
            "total_max_amount_in": 0,
        }
    return {
        "total_amount_in": 0,
        "total_min_amount_out": 0,
        "total_amount_out": _require_positive_u128(
            _field_or_body(op, body, "total_amount_out", "amount_out"),
            f"{op_path}.total_amount_out",
        ),
        "total_max_amount_in": _require_positive_u128(
            op.get("total_max_amount_in", op.get("max_amount_in")),
            f"{op_path}.total_max_amount_in",
        ),
    }


def _field_or_body(
    op: Mapping[str, Any],
    body: Mapping[str, Any],
    op_name: str,
    body_name: str,
) -> object:
    if op_name in op:
        return op[op_name]
    return body.get(body_name)


def _body_or_op_str(
    op: Mapping[str, Any],
    body: Mapping[str, Any],
    name: str,
    *,
    op_path: str,
) -> str:
    value = op.get(name, body.get(name))
    return _require_non_empty_str(value, f"{op_path}.{name}")


def _require_mapping(value: object, path: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{path} must be an object")
    return value


def _require_list(value: object, path: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{path} must be a list")
    return value


def _require_non_empty_str(value: object, path: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{path} must be a non-empty string")
    return value


def _require_u64(value: object, path: str) -> int:
    parsed = _require_uint(value, path)
    if parsed > (1 << 64) - 1:
        raise ValueError(f"{path} must be a u64")
    return parsed


def _require_u32(value: object, path: str) -> int:
    parsed = _require_uint(value, path)
    if parsed > U32_MAX:
        raise ValueError(f"{path} must be a u32")
    return parsed


def _require_positive_u128(value: object, path: str) -> int:
    parsed = _require_u128(value, path)
    if parsed <= 0:
        raise ValueError(f"{path} must be positive")
    return parsed


def _require_u128(value: object, path: str) -> int:
    parsed = _require_uint(value, path)
    if parsed > U128_MAX:
        raise ValueError(f"{path} must be a u128")
    return parsed


def _require_uint(value: object, path: str) -> int:
    if isinstance(value, bool):
        raise TypeError(f"{path} must be an unsigned integer")
    if isinstance(value, int):
        parsed = value
    elif isinstance(value, str) and value.isdigit():
        parsed = int(value)
    else:
        raise TypeError(f"{path} must be an unsigned integer")
    if parsed < 0:
        raise ValueError(f"{path} must be non-negative")
    return parsed
