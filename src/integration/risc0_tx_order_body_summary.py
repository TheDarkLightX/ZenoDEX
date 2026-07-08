"""Body-derived Risc0 tx-order summaries for route-order receipts."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import Any

from src.core.risc0_tx_execution_order import (
    RISC0_SPOT_PROOF_TYPE_V1,
    TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0,
    TxExecutionOrderInputV1,
    TxExecutionOrderReceiptRequirementV1,
    stale_route_order_receipt_requirement_v1,
    validate_stale_route_order_receipt_policy_v1,
)
from src.state.pools import compute_pool_id, normalize_curve_config

U128_MAX = 2**128 - 1


def tx_order_inputs_from_transactions_v1(
    transactions: object,
) -> tuple[TxExecutionOrderInputV1, ...]:
    """Extract route reads and pool writes from committed transaction bodies."""

    if not isinstance(transactions, list):
        raise TypeError("transactions must be a list")
    out: list[TxExecutionOrderInputV1] = []
    for tx_index, tx in enumerate(transactions):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{tx_index}] must be an object")
        tx_sender = _tx_order_sender_identity_v1(tx, tx_index=tx_index)
        operations = tx.get("operations", {})
        if not isinstance(operations, Mapping):
            raise TypeError(f"transactions[{tx_index}].operations must be an object")

        pool_write_ids: set[str] = set()
        route_read_pool_ids: set[str] = set()
        protected_values_by_asset: dict[str, int] = {}

        raw_spot_ops = operations.get("2", [])
        if raw_spot_ops is not None:
            if not isinstance(raw_spot_ops, list):
                raise TypeError(f"transactions[{tx_index}].operations['2'] must be a list")
            for op_index, raw_op in enumerate(raw_spot_ops):
                op_path = f"transactions[{tx_index}].operations['2'][{op_index}]"
                if not isinstance(raw_op, Mapping):
                    raise TypeError(f"{op_path} must be an object")
                route_pool_ids = _route_pool_ids_from_tau_route_operation(raw_op, op_path=op_path)
                route_read_pool_ids.update(route_pool_ids)
                pool_write_ids.update(route_pool_ids)
                _add_route_protected_value_from_operation(
                    protected_values_by_asset,
                    raw_op,
                    op_path=op_path,
                )
                pool_id = _pool_id_from_tau_swap_operation(raw_op, op_path=op_path)
                if pool_id is not None:
                    pool_write_ids.add(pool_id)

        raw_route_ops = operations.get("5", [])
        if raw_route_ops is not None:
            if not isinstance(raw_route_ops, list):
                raise TypeError(f"transactions[{tx_index}].operations['5'] must be a list")
            for op_index, raw_op in enumerate(raw_route_ops):
                op_path = f"transactions[{tx_index}].operations['5'][{op_index}]"
                raw_op = _route_body_summary_op(raw_op, op_path=op_path)
                route_pool_ids = _route_pool_ids_from_tau_route_operation(
                    raw_op,
                    op_path=op_path,
                    require_quote_receipt=True,
                )
                route_read_pool_ids.update(route_pool_ids)
                pool_write_ids.update(route_pool_ids)
                _add_route_protected_value_from_operation(
                    protected_values_by_asset,
                    raw_op,
                    op_path=op_path,
                )

        out.append(
            TxExecutionOrderInputV1(
                sender_pubkey=tx_sender,
                route_read_pool_ids=tuple(sorted(route_read_pool_ids)),
                pool_write_ids=tuple(sorted(pool_write_ids)),
                protected_values=tuple(sorted(protected_values_by_asset.items())),
            )
        )
    return tuple(out)


def _route_body_summary_op(raw_op: object, *, op_path: str) -> Mapping[str, Any]:
    if isinstance(raw_op, Mapping):
        return raw_op
    if isinstance(raw_op, list):
        if len(raw_op) != 2:
            raise ValueError(f"{op_path} signed route-body pair must be [route_body, signature]")
        if not isinstance(raw_op[0], Mapping):
            raise TypeError(f"{op_path}[0] must be an object")
        signature = raw_op[1]
        if not isinstance(signature, str) or not signature:
            raise TypeError(f"{op_path}[1] must be a non-empty string")
        return raw_op[0]
    raise TypeError(f"{op_path} must be an object")


def tx_order_inputs_from_explicit_summary_v1(
    raw_inputs: object,
) -> tuple[TxExecutionOrderInputV1, ...] | None:
    if raw_inputs is None:
        return None
    if not isinstance(raw_inputs, list):
        raise TypeError("tx_execution_order_inputs must be a list")
    out: list[TxExecutionOrderInputV1] = []
    for index, raw_input in enumerate(raw_inputs):
        if not isinstance(raw_input, Mapping):
            raise TypeError(f"tx_execution_order_inputs[{index}] must be an object")
        sender_pubkey = raw_input.get("sender_pubkey")
        route_read_pool_ids = raw_input.get("route_read_pool_ids", [])
        pool_write_ids = raw_input.get("pool_write_ids", [])
        protected_values = raw_input.get("protected_values", [])
        if not isinstance(sender_pubkey, str):
            raise TypeError(f"tx_execution_order_inputs[{index}].sender_pubkey must be a string")
        if not isinstance(route_read_pool_ids, list) or not all(
            isinstance(pool_id, str) for pool_id in route_read_pool_ids
        ):
            raise TypeError(f"tx_execution_order_inputs[{index}].route_read_pool_ids must be string list")
        if not isinstance(pool_write_ids, list) or not all(isinstance(pool_id, str) for pool_id in pool_write_ids):
            raise TypeError(f"tx_execution_order_inputs[{index}].pool_write_ids must be string list")
        if not isinstance(protected_values, list):
            raise TypeError(f"tx_execution_order_inputs[{index}].protected_values must be a list")
        out.append(
            TxExecutionOrderInputV1(
                sender_pubkey=sender_pubkey,
                route_read_pool_ids=tuple(route_read_pool_ids),
                pool_write_ids=tuple(pool_write_ids),
                protected_values=_explicit_protected_values(
                    protected_values,
                    input_path=f"tx_execution_order_inputs[{index}].protected_values",
                ),
            )
        )
    return tuple(out)


def _tx_order_sender_identity_v1(
    tx: Mapping[str, Any],
    *,
    tx_index: int,
) -> str:
    tx_sender = tx.get("tx_sender_pubkey")
    legacy_sender = tx.get("sender_pubkey")
    if isinstance(tx_sender, str) and tx_sender:
        if legacy_sender is not None:
            if not isinstance(legacy_sender, str) or not legacy_sender:
                raise TypeError(
                    f"transactions[{tx_index}].sender_pubkey must be a non-empty string when present"
                )
            if legacy_sender != tx_sender:
                raise ValueError(
                    f"transactions[{tx_index}].sender_pubkey must match tx_sender_pubkey"
                )
        return tx_sender
    if isinstance(legacy_sender, str) and legacy_sender:
        return legacy_sender
    return f"tx:{tx_index}"


def tx_order_inputs_for_case_v1(case: Mapping[str, Any]) -> tuple[TxExecutionOrderInputV1, ...]:
    derived = tx_order_inputs_from_transactions_v1(case.get("transactions", []))
    explicit = tx_order_inputs_from_explicit_summary_v1(case.get("tx_execution_order_inputs"))
    if explicit is None:
        return derived
    if derived and explicit != derived:
        raise ValueError("tx_execution_order_inputs must match transaction-derived summary")
    return explicit


def route_order_receipt_requirement_for_transactions_v1(
    transactions: object,
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> TxExecutionOrderReceiptRequirementV1 | None:
    tx_order_inputs = tx_order_inputs_from_transactions_v1(transactions)
    if not tx_order_inputs or not _has_route_reads_v1(tx_order_inputs):
        return None
    return stale_route_order_receipt_requirement_v1(tx_order_inputs, proof_type=proof_type)


def route_order_receipt_requirement_for_case_v1(
    case: Mapping[str, Any],
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> TxExecutionOrderReceiptRequirementV1 | None:
    tx_order_inputs = tx_order_inputs_for_case_v1(case)
    if not tx_order_inputs or not _has_route_reads_v1(tx_order_inputs):
        return None
    return stale_route_order_receipt_requirement_v1(tx_order_inputs, proof_type=proof_type)


def apply_route_order_receipt_policy_to_body_v1(
    body: dict[str, Any],
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> bool:
    """Attach the required order receipt, or reject stale/mismatched evidence."""

    requirement = route_order_receipt_requirement_for_transactions_v1(
        body.get("transactions", []),
        proof_type=proof_type,
    )
    if requirement is None:
        return False
    evidence = body.get("evidence")
    if not isinstance(evidence, dict):
        raise TypeError("body.evidence must be an object")
    proof_receipts = evidence.get("proof_receipts")
    if not isinstance(proof_receipts, list):
        raise TypeError("body.evidence.proof_receipts must be a list")

    matching = [
        receipt
        for receipt in proof_receipts
        if isinstance(receipt, Mapping)
        and receipt.get("schema") == TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0
        and receipt.get("proof_type") == proof_type
    ]
    if matching:
        validate_stale_route_order_receipt_policy_v1(
            tx_order_inputs_from_transactions_v1(body.get("transactions", [])),
            proof_receipts,
            proof_type=proof_type,
        )
        return False
    if not requirement.required:
        return False
    proof_receipts.append(requirement.receipt())
    return True


def tx_execution_order_for_body_v1(
    body: Mapping[str, Any],
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> tuple[int, ...]:
    transactions = body.get("transactions", [])
    tx_order_inputs = tx_order_inputs_from_transactions_v1(transactions)
    tx_count = len(tx_order_inputs)
    if not _has_route_reads_v1(tx_order_inputs):
        return tuple(range(tx_count))
    evidence = body.get("evidence")
    if not isinstance(evidence, Mapping):
        raise TypeError("body.evidence must be an object")
    proof_receipts = evidence.get("proof_receipts")
    if not isinstance(proof_receipts, list):
        raise TypeError("body.evidence.proof_receipts must be a list")
    requirement = validate_stale_route_order_receipt_policy_v1(
        tx_order_inputs,
        proof_receipts,
        proof_type=proof_type,
    )
    return requirement.tx_execution_order


def _has_route_reads_v1(txs: Sequence[TxExecutionOrderInputV1]) -> bool:
    return any(tx.route_read_pool_ids for tx in txs)


def _pool_id_from_tau_swap_operation(op: Mapping[str, Any], *, op_path: str) -> str | None:
    kind = op.get("kind")
    if kind == "CREATE_POOL":
        try:
            curve_tag, curve_params = normalize_curve_config(
                curve_tag=op.get("curve_tag", None),
                curve_params=op.get("curve_params", None),
            )
            return compute_pool_id(
                str(op["asset0"]),
                str(op["asset1"]),
                int(op["fee_bps"]),
                curve_tag=curve_tag,
                curve_params=curve_params,
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"{op_path} cannot derive CREATE_POOL pool_id") from exc
    if kind in {"SWAP_EXACT_IN", "SWAP_EXACT_OUT", "ADD_LIQUIDITY", "REMOVE_LIQUIDITY"}:
        pool_id = op.get("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            raise ValueError(f"{op_path}.pool_id must be a non-empty string")
        return pool_id
    return None


def _route_pool_ids_from_legs(legs: object, *, legs_path: str) -> tuple[str, ...]:
    if not isinstance(legs, list) or not legs:
        raise ValueError(f"{legs_path} must be a non-empty list")

    pool_ids: set[str] = set()
    for leg_index, leg in enumerate(legs):
        if not isinstance(leg, Mapping):
            raise TypeError(f"{legs_path}[{leg_index}] must be an object")
        hops = leg.get("hops")
        if not isinstance(hops, list) or not hops:
            raise ValueError(f"{legs_path}[{leg_index}].hops must be a non-empty list")
        for hop_index, hop in enumerate(hops):
            if not isinstance(hop, Mapping):
                raise TypeError(f"{legs_path}[{leg_index}].hops[{hop_index}] must be an object")
            pool_id = hop.get("pool_id")
            if not isinstance(pool_id, str) or not pool_id:
                raise ValueError(
                    f"{legs_path}[{leg_index}].hops[{hop_index}].pool_id must be a non-empty string"
                )
            pool_ids.add(pool_id)
    return tuple(sorted(pool_ids))


def _route_pool_ids_from_quote_receipt(receipt: object, *, op_path: str) -> tuple[str, ...]:
    if not isinstance(receipt, Mapping):
        raise TypeError(f"{op_path}.quote_receipt must be an object")
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        raise TypeError(f"{op_path}.quote_receipt.body must be an object")

    pool_ids = set(
        _route_pool_ids_from_legs(
            body.get("legs"),
            legs_path=f"{op_path}.quote_receipt.body.legs",
        )
    )

    pools = body.get("pools")
    if not isinstance(pools, Mapping):
        raise TypeError(f"{op_path}.quote_receipt.body.pools must be an object")
    pool_map_ids = {pool_id for pool_id in pools if isinstance(pool_id, str)}
    if pool_map_ids != pool_ids:
        raise ValueError(f"{op_path}.quote_receipt body pool map must match leg hop pool ids")
    return tuple(sorted(pool_ids))


def _route_pool_ids_from_tau_route_operation(
    op: Mapping[str, Any],
    *,
    op_path: str,
    require_quote_receipt: bool = False,
) -> tuple[str, ...]:
    kind = op.get("kind")
    if kind not in {"ROUTE_EXACT_IN", "ROUTE_EXACT_OUT"}:
        return ()
    quote_receipt = op.get("quote_receipt")
    receipt_ids = (
        _route_pool_ids_from_quote_receipt(quote_receipt, op_path=op_path)
        if quote_receipt is not None
        else None
    )
    if require_quote_receipt and receipt_ids is None:
        raise TypeError(f"{op_path}.quote_receipt must be an object")
    legs = op.get("legs")
    if legs is None:
        if receipt_ids is None:
            raise TypeError(f"{op_path}.quote_receipt must be an object")
        return receipt_ids
    leg_ids = _route_pool_ids_from_legs(legs, legs_path=f"{op_path}.legs")
    if receipt_ids is not None and receipt_ids != leg_ids:
        raise ValueError(f"{op_path}.quote_receipt body pool ids must match route intent legs")
    return leg_ids


def _add_route_protected_value_from_operation(
    protected_values_by_asset: dict[str, int],
    op: Mapping[str, Any],
    *,
    op_path: str,
) -> None:
    route_value = _route_protected_value_from_tau_route_operation(op, op_path=op_path)
    if route_value is None:
        return
    asset, amount_atoms = route_value
    previous = protected_values_by_asset.get(asset, 0)
    total = previous + amount_atoms
    if total > U128_MAX:
        raise ValueError(f"{op_path}.protected_values amount_atoms overflow")
    protected_values_by_asset[asset] = total


def _route_protected_value_from_tau_route_operation(
    op: Mapping[str, Any],
    *,
    op_path: str,
) -> tuple[str, int] | None:
    kind = op.get("kind")
    if kind == "ROUTE_EXACT_IN":
        amount_value = _first_present(op, ("total_amount_in", "amount_in"))
    elif kind == "ROUTE_EXACT_OUT":
        amount_value = _first_present(op, ("total_max_amount_in", "max_amount_in"))
    else:
        return None
    if amount_value is None:
        return None
    asset_in = op.get("asset_in")
    if not isinstance(asset_in, str) or asset_in == "":
        raise ValueError(f"{op_path}.asset_in must be non-empty when route value is present")
    amount_atoms = _require_u128_atoms(amount_value, f"{op_path}.protected_value_atoms")
    if amount_atoms == 0:
        return None
    return asset_in, amount_atoms


def _first_present(op: Mapping[str, Any], names: tuple[str, ...]) -> object | None:
    for name in names:
        if name in op:
            return op[name]
    return None


def _explicit_protected_values(
    raw_values: list[object],
    *,
    input_path: str,
) -> tuple[tuple[str, int], ...]:
    values_by_asset: dict[str, int] = {}
    for value_index, raw_value in enumerate(raw_values):
        value_path = f"{input_path}[{value_index}]"
        if not isinstance(raw_value, Mapping):
            raise TypeError(f"{value_path} must be an object")
        asset = raw_value.get("asset")
        if not isinstance(asset, str) or asset == "":
            raise TypeError(f"{value_path}.asset must be a non-empty string")
        amount_atoms = _require_u128_atoms(raw_value.get("amount_atoms"), f"{value_path}.amount_atoms")
        if amount_atoms == 0:
            continue
        previous = values_by_asset.get(asset, 0)
        total = previous + amount_atoms
        if total > U128_MAX:
            raise ValueError(f"{value_path}.amount_atoms overflow")
        values_by_asset[asset] = total
    return tuple(sorted(values_by_asset.items()))


def _require_u128_atoms(value: object, field_name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{field_name} must be an integer")
    if value < 0 or value > U128_MAX:
        raise ValueError(f"{field_name} must be a u128")
    return value
