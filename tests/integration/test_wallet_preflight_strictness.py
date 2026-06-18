from __future__ import annotations

from src.integration import perps_wallet_api
from src.integration import zusd_monetary_wallet_api


def test_zusd_proof_intent_receipt_requires_literal_true_preflight() -> None:
    receipt = zusd_monetary_wallet_api._zusd_proof_intent_receipt(
        chain_id="chain",
        action="mint_zusd",
        asset_id="asset",
        operation={"kind": "mint_zusd"},
        operations={"11": []},
        app_hash_before="before",
        app_hash_after="after",
        preflight={"ok": "true", "error": None},
        actor_pubkey="0xabc",
        nonce_before=0,
        nonce_after=1,
        tx_sequence_number=7,
        tx_fee_limit=0,
        signing_mode="prepare_only",
        tau_tx_payload=None,
    )

    assert zusd_monetary_wallet_api._preflight_ok({"ok": "true"}) is False
    assert receipt["body"]["preflight_ok"] is False


def test_perps_proof_intent_receipt_requires_literal_true_preflight() -> None:
    receipt = perps_wallet_api._perps_proof_intent_receipt(
        chain_id="chain",
        action="deposit_collateral",
        operation={"kind": "deposit_collateral", "market_id": "perp"},
        operations={"8": []},
        app_hash_before="before",
        app_hash_after="after",
        preflight={"ok": 1, "error": None},
        tx_sender_pubkey="0xabc",
        tx_sequence_number=7,
        tx_fee_limit=0,
        signing_mode="prepare_only",
        tau_tx_payload=None,
    )

    assert perps_wallet_api._preflight_ok({"ok": 1}) is False
    assert receipt["body"]["preflight_ok"] is False
