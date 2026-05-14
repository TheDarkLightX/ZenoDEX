"""Canonical ZenoHypergraph root for UPBA v1 evidence.

This module binds the existing UPBA bounded price-grid evidence into a compact
typed hypergraph commitment. The hypergraph uses an implied complete incidence
relation between canonical order vertices and price-row vertices:

    Order vertices x PriceRow vertices -> OrderPrice hyperedges

The root is intentionally a public verifier artifact. It is not an FHE security
claim and does not make private-order guarantees.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from ..state.balances import BalanceTable
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .uniform_batch_clearing import (
    UniformBatchCertificateV1,
    uniform_batch_certificate_hash,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from .uniform_batch_price_grid_table import (
    UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
    UniformBatchPriceGridConfigV1,
    UniformBatchPriceGridRowV1,
    UniformBatchPriceGridWitnessV1,
    verify_uniform_batch_price_grid_table_v1,
)

ZENOHYPERGRAPH_UPBA_ROOT_SCHEMA_V1 = "zenodex/zenohypergraph/upba_price_grid_root/v1"
ZENOHYPERGRAPH_UPBA_RELATION_ID_V1 = "zenodex/zenohypergraph/relation/orders_x_price_rows/v1"


@dataclass(frozen=True)
class ZenoHypergraphVerificationResult:
    ok: bool
    error: str | None
    hypergraph_root: str | None = None


def uniform_batch_hypergraph_root_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    price_grid_config: UniformBatchPriceGridConfigV1 | Mapping[str, Any],
    price_grid_rows: Sequence[UniformBatchPriceGridRowV1 | Mapping[str, Any]],
    price_grid_witness: UniformBatchPriceGridWitnessV1 | Mapping[str, Any],
) -> str:
    """Return the canonical UPBA ZenoHypergraph root.

    The function reuses the functional-core price-grid verifier before hashing.
    This prevents the root from blessing malformed table rows or certificates.
    """

    parsed_cert = (
        uniform_batch_certificate
        if isinstance(uniform_batch_certificate, UniformBatchCertificateV1)
        else UniformBatchCertificateV1.from_obj(_require_mapping(uniform_batch_certificate, name="uniform_batch_certificate"))
    )
    parsed_config = (
        price_grid_config
        if isinstance(price_grid_config, UniformBatchPriceGridConfigV1)
        else UniformBatchPriceGridConfigV1.from_obj(_require_mapping(price_grid_config, name="price_grid.config"))
    )
    parsed_rows = tuple(
        row
        if isinstance(row, UniformBatchPriceGridRowV1)
        else UniformBatchPriceGridRowV1.from_obj(_require_mapping(row, name="price_grid.row"))
        for row in price_grid_rows
    )
    parsed_witness = (
        price_grid_witness
        if isinstance(price_grid_witness, UniformBatchPriceGridWitnessV1)
        else UniformBatchPriceGridWitnessV1.from_obj(_require_mapping(price_grid_witness, name="price_grid.witness"))
    )

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=parsed_cert,
        config=parsed_config,
        rows=parsed_rows,
        witness=parsed_witness,
    )
    if not result.ok:
        raise ValueError(f"price grid evidence invalid: {result.error or 'invalid evidence'}")

    body = {
        "schema": ZENOHYPERGRAPH_UPBA_ROOT_SCHEMA_V1,
        "relation_id": ZENOHYPERGRAPH_UPBA_RELATION_ID_V1,
        "policy_id": parsed_cert.policy_id,
        "score_function_id": UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        "settlement_id": parsed_config.settlement_id,
        "certificate_hash": uniform_batch_certificate_hash(parsed_cert),
        "intent_set_hash": uniform_batch_intent_set_hash(intents),
        "pool": {
            "pool_id": pool.pool_id,
            "base_asset": pool.asset0,
            "quote_asset": pool.asset1,
            "pool_state_hash": uniform_batch_pool_state_hash(pool),
        },
        "price_grid": {
            "max_price_num": parsed_config.max_price_num,
            "max_price_den": parsed_config.max_price_den,
            "row_count": parsed_config.row_count,
            "candidate_table_root": parsed_config.candidate_table_root,
        },
        "vertices": {
            "orders": [_order_vertex(intent) for intent in sorted(intents, key=lambda item: item.intent_id)],
            "price_rows": [
                _price_row_vertex(row)
                for row in sorted(parsed_rows, key=lambda item: (item.price_num, item.price_den))
            ],
        },
        "incidence": {
            "kind": "complete_order_price_incidence",
            "order_count": len(intents),
            "price_row_count": len(parsed_rows),
            "edge_count": len(intents) * len(parsed_rows),
        },
        "winner": {
            "candidate_id": parsed_witness.winner_candidate_id,
            "price_num": parsed_witness.winner_price_num,
            "price_den": parsed_witness.winner_price_den,
            "volume_upper": parsed_witness.volume_upper,
            "surplus_upper_at_winner_volume": parsed_witness.surplus_upper_at_winner_volume,
        },
        "non_claims": [
            "no_fhe_security_claim",
            "no_private_balance_claim",
            "no_unbounded_price_optimality_claim",
        ],
    }
    return sha256_hex(domain_sep_bytes("zenohypergraph_upba_root", version=1) + canonical_json_bytes(body))


def verify_uniform_batch_hypergraph_root_v1(
    *,
    expected_root: str,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    price_grid_config: UniformBatchPriceGridConfigV1 | Mapping[str, Any],
    price_grid_rows: Sequence[UniformBatchPriceGridRowV1 | Mapping[str, Any]],
    price_grid_witness: UniformBatchPriceGridWitnessV1 | Mapping[str, Any],
) -> ZenoHypergraphVerificationResult:
    try:
        expected = canonical_hex_fixed_allow_0x(expected_root, nbytes=32, name="zenohypergraph_root")
        actual = uniform_batch_hypergraph_root_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            uniform_batch_certificate=uniform_batch_certificate,
            price_grid_config=price_grid_config,
            price_grid_rows=price_grid_rows,
            price_grid_witness=price_grid_witness,
        )
        if expected != actual:
            return ZenoHypergraphVerificationResult(
                ok=False,
                error="zenohypergraph root mismatch",
                hypergraph_root=actual,
            )
        return ZenoHypergraphVerificationResult(ok=True, error=None, hypergraph_root=actual)
    except (TypeError, ValueError) as exc:
        return ZenoHypergraphVerificationResult(ok=False, error=str(exc))


def _order_vertex(intent: Intent) -> dict[str, Any]:
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        raise ValueError("ZenoHypergraph UPBA v1 supports SWAP_EXACT_IN order vertices only")
    fields = intent.fields if isinstance(intent.fields, Mapping) else {}
    return {
        "vertex_type": "order",
        "intent_id": _require_str(intent.intent_id, name="intent.intent_id"),
        "sender_pubkey": _require_str(intent.sender_pubkey, name="intent.sender_pubkey"),
        "kind": intent.kind.value,
        "asset_in": _require_str(fields.get("asset_in"), name="intent.asset_in"),
        "asset_out": _require_str(fields.get("asset_out"), name="intent.asset_out"),
        "pool_id": _require_str(fields.get("pool_id"), name="intent.pool_id"),
        "amount_in": _require_nonnegative_int(fields.get("amount_in"), name="intent.amount_in"),
        "min_amount_out": _require_nonnegative_int(fields.get("min_amount_out"), name="intent.min_amount_out"),
    }


def _price_row_vertex(row: UniformBatchPriceGridRowV1) -> dict[str, Any]:
    return {
        "vertex_type": "price_row",
        "candidate_id": row.candidate_id,
        "price_num": row.price_num,
        "price_den": row.price_den,
        "valid_price_ok": row.valid_price_ok,
        "volume": row.volume,
        "surplus": row.surplus,
        "winner_row_ok": row.winner_row_ok,
        "dominated_by_winner_ok": row.dominated_by_winner_ok,
    }


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)
