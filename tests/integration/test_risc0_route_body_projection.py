from __future__ import annotations

import json

import pytest

from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.integration.risc0_route_body_projection import (
    project_route_body_transaction_to_proof_v1,
    project_route_body_transactions_to_proof_v1,
    route_body_projection_signing_dict_v1,
)
from src.integration.risc0_tx_order_body_summary import tx_order_inputs_from_transactions_v1

BINDING_HASH = "0x" + "11" * 32


def _receipt_body() -> dict[str, object]:
    return {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "asset-a",
        "asset_out": "asset-b",
        "amount_in": 100,
        "amount_out": 90,
        "legs": [
            {
                "amount_in": 100,
                "amount_out": 90,
                "hops": [
                    {
                        "pool_id": "pool-a",
                        "asset_in": "asset-a",
                        "asset_out": "asset-b",
                        "amount_in": 100,
                        "amount_out": 90,
                    }
                ],
            }
        ],
        "pools": {"pool-a": "pool-fingerprint-a"},
    }


def _route_receipt(*, binding_hash: str | None = BINDING_HASH) -> dict[str, object]:
    receipt: dict[str, object] = {
        "body": _receipt_body(),
        "receipt_hash": "0x" + "22" * 32,
    }
    if binding_hash is not None:
        receipt["risc0_route_quote_receipt_binding_hash"] = binding_hash
    return receipt


def _route_body_tx(
    *,
    kind: str = "ROUTE_EXACT_IN",
    include_explicit_hash: bool = True,
    receipt_binding_hash: str | None = BINDING_HASH,
    include_projection_fields: bool = True,
) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauSwap",
        "version": "v1",
        "kind": kind,
        "intent_id": "route-local",
        "sender_pubkey": "route-sender",
        "deadline": 100,
        "quote_receipt": _route_receipt(binding_hash=receipt_binding_hash),
        "recipient": "recipient",
        "total_min_amount_out": 80,
    }
    if include_projection_fields:
        op.update(
            {
                "asset_in": "asset-a",
                "asset_out": "asset-b",
                "leg_indices": [0],
                "legs": [{"hops": [{"pool_id": "pool-a"}]}],
                "total_amount_in": 100,
                "total_amount_out": 0,
                "total_max_amount_in": 0,
            }
        )
    if include_explicit_hash:
        op["quote_receipt_hash"] = BINDING_HASH
    if kind == "ROUTE_EXACT_OUT":
        op["total_amount_out"] = 90
        op["total_max_amount_in"] = 120
        op["total_amount_in"] = 0
        op["total_min_amount_out"] = 0
        op.pop("total_min_amount_out")
    return {
        "tx_sender_pubkey": "route-sender",
        "nonce": 7,
        "operations": {"5": [op]},
    }


def _writer_tx() -> dict[str, object]:
    return {
        "tx_sender_pubkey": "writer",
        "nonce": 3,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "pool_id": "pool-a",
                }
            ]
        },
    }


def test_project_route_body_to_proof_v1_preserves_route_order_summary() -> None:
    local_transactions = [_writer_tx(), _route_body_tx()]

    projected = project_route_body_transactions_to_proof_v1(local_transactions)

    assert tx_order_inputs_from_transactions_v1(local_transactions) == (
        tx_order_inputs_from_transactions_v1(list(projected))
    )
    route_intent = projected[1]["operations"]["2"][0]
    assert route_intent["sender_pubkey"] == "route-sender"
    assert route_intent["quote_receipt_hash"] == BINDING_HASH
    assert route_intent["asset_in"] == "asset-a"
    assert route_intent["asset_out"] == "asset-b"
    assert route_intent["leg_indices"] == [0]
    assert route_intent["legs"] == [{"hops": [{"pool_id": "pool-a"}]}]
    assert route_intent["total_amount_in"] == 100
    assert route_intent["total_min_amount_out"] == 80
    assert route_intent["total_amount_out"] == 0
    assert route_intent["total_max_amount_in"] == 0
    json.dumps(projected, sort_keys=True)


def test_project_route_body_rejects_projection_that_changes_route_order_summary() -> None:
    tx = _route_body_tx(include_projection_fields=False)

    with pytest.raises(ValueError, match="projection must preserve tx_execution_order summary"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_to_proof_v1_maps_exact_out_totals() -> None:
    projected = project_route_body_transaction_to_proof_v1(
        _route_body_tx(kind="ROUTE_EXACT_OUT"),
        tx_index=0,
    )

    route_intent = projected["operations"]["2"][0]
    assert route_intent["kind"] == "ROUTE_EXACT_OUT"
    assert route_intent["total_amount_in"] == 0
    assert route_intent["total_min_amount_out"] == 0
    assert route_intent["total_amount_out"] == 90
    assert route_intent["total_max_amount_in"] == 120


def test_project_route_body_rejects_generic_receipt_hash_without_risc0_binding() -> None:
    tx = _route_body_tx(include_explicit_hash=False, receipt_binding_hash=None)

    with pytest.raises(ValueError, match="risc0_route_quote_receipt_binding_hash is required"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_binding_hash_mismatch() -> None:
    tx = _route_body_tx(receipt_binding_hash="0x" + "33" * 32)

    with pytest.raises(ValueError, match="quote_receipt_hash must match receipt RISC0 binding hash"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_mixed_route_body_and_proof_intents() -> None:
    tx = _route_body_tx()
    tx["operations"]["2"] = [{"kind": "SWAP_EXACT_IN"}]

    with pytest.raises(ValueError, match=r"cannot mix operations\['2'\] with operations\['5'\]"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_sender_alias_split() -> None:
    tx = _route_body_tx()
    tx["sender_pubkey"] = "legacy-route-sender"

    with pytest.raises(ValueError, match="sender_pubkey must match tx_sender_pubkey"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_signed_pair_without_projection_equivalent_payload() -> None:
    tx = _route_body_tx(include_projection_fields=False)
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    tx["operations"]["5"] = [[local_route, "0xsig"]]  # type: ignore[index]

    with pytest.raises(ValueError, match="embedded signature does not authorize projected proof-v1 route intent"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_accepts_signed_pair_when_payload_is_projection_equivalent() -> None:
    tx = _route_body_tx()
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    local_route.update(  # type: ignore[union-attr]
        {
            "asset_in": "asset-a",
            "asset_out": "asset-b",
            "leg_indices": [0],
            "legs": [{"hops": [{"pool_id": "pool-a"}]}],
            "total_amount_in": 100,
            "total_amount_out": 0,
            "total_max_amount_in": 0,
        }
    )
    tx["operations"]["5"] = [[local_route, "0xsig"]]  # type: ignore[index]

    projected = project_route_body_transaction_to_proof_v1(tx, tx_index=0)
    proof_route = projected["operations"]["2"][0]
    local_with_sig = dict(local_route)
    local_with_sig["signature"] = "0xsig"

    assert "signature" not in proof_route
    assert route_body_projection_signing_dict_v1(local_with_sig) == route_body_projection_signing_dict_v1(proof_route)


def test_project_route_body_rejects_malformed_signed_pair() -> None:
    tx = _route_body_tx()
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    tx["operations"]["5"] = [[local_route, "0xsig", {}]]  # type: ignore[index]

    with pytest.raises(ValueError, match=r"signed route-body pair must be \[route_body, signature\]"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_signed_pair_duplicate_signature_field() -> None:
    tx = _route_body_tx()
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    local_route["signature"] = "0xembedded"  # type: ignore[index]
    tx["operations"]["5"] = [[local_route, "0xpair"]]  # type: ignore[index]

    with pytest.raises(ValueError, match="signature must not be duplicated"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_signed_pair_non_string_signature() -> None:
    tx = _route_body_tx()
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    tx["operations"]["5"] = [[local_route, 7]]  # type: ignore[index]

    with pytest.raises(TypeError, match=r"\[1\] must be a non-empty string"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_rejects_embedded_signature_without_projection_equivalent_payload() -> None:
    tx = _route_body_tx(include_projection_fields=False)
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    local_route["signature"] = "0xsig"  # type: ignore[index]

    with pytest.raises(ValueError, match="embedded signature does not authorize projected proof-v1 route intent"):
        project_route_body_transaction_to_proof_v1(tx, tx_index=0)


def test_project_route_body_accepts_embedded_signature_when_payload_is_projection_equivalent() -> None:
    tx = _route_body_tx()
    local_route = tx["operations"]["5"][0]  # type: ignore[index]
    local_route.update(  # type: ignore[union-attr]
        {
            "signature": "0xsig",
            "asset_in": "asset-a",
            "asset_out": "asset-b",
            "leg_indices": [0],
            "legs": [{"hops": [{"pool_id": "pool-a"}]}],
            "total_amount_in": 100,
            "total_amount_out": 0,
            "total_max_amount_in": 0,
        }
    )

    projected = project_route_body_transaction_to_proof_v1(tx, tx_index=0)
    proof_route = projected["operations"]["2"][0]

    assert "signature" not in proof_route
    assert route_body_projection_signing_dict_v1(local_route) == route_body_projection_signing_dict_v1(proof_route)


def test_project_route_body_signing_payload_differs_from_projected_proof_intent() -> None:
    local_tx = _route_body_tx(include_projection_fields=False)
    local_route = local_tx["operations"]["5"][0]  # type: ignore[index]
    projected = project_route_body_transaction_to_proof_v1(_route_body_tx(), tx_index=0)
    proof_route = projected["operations"]["2"][0]

    local_signing = build_dex_intent_signing_dict_v1(local_route)
    proof_signing = build_dex_intent_signing_dict_v1(proof_route)

    assert local_signing != proof_signing
    assert set(proof_signing["fields"]) - set(local_signing["fields"]) == {
        "asset_in",
        "asset_out",
        "leg_indices",
        "legs",
        "total_amount_in",
        "total_amount_out",
        "total_max_amount_in",
    }
