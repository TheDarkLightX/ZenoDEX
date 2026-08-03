from __future__ import annotations

from src.integration.zeno_ledger_v0 import build_tx_receipt_v0, stable_error_code_v0
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from tools.zeno_ledger_make_testnet_bundle import _body_with_transaction_v0
from tools.zeno_ledger_run_local import _execute_tau_app_body_v0


def test_zeno_ledger_rejects_generic_zusd_mint_without_state_change(monkeypatch) -> None:
    chain_id = "zeno-ledger-managed-zusd"
    operator = "0x" + "ab" * 48
    recipient = "0x" + "cd" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    body = _body_with_transaction_v0(
        chain_id=chain_id,
        height=1,
        time_ms=1_000,
        sequencer_id="sequencer-managed-zusd",
        tx={
            "tx_id": "generic-zusd-mint-must-reject",
            "block_timestamp": 1,
            "tx_sender_pubkey": operator,
            "operations": {
                "9": [
                    {
                        "module": "TauToken",
                        "action": "mint",
                        "asset": zusd_asset,
                        "to_pubkey": recipient,
                        "amount": 1,
                        "nonce": 1,
                    }
                ]
            },
        },
        policy_id="managed_zusd_policy_v1",
    )

    pre_root, post_root, _state, executed_body, receipts = _execute_tau_app_body_v0(
        app_state_json="",
        body=body,
        chain_balances={},
        tau_chain_id=chain_id,
        allow_missing_settlement=True,
        require_intent_signatures=False,
        allow_unsigned_intents_if_tx_sender_matches=False,
        enable_faucet=False,
        default_block_timestamp=1,
    )

    expected_error = stable_error_code_v0(
        "managed asset operation generic_mint requires authority zenodex/zusd-monetary-kernel/v1"
    )
    assert pre_root == post_root
    assert receipts == [
        build_tx_receipt_v0(
            tx_hash=receipts[0]["tx_hash"],
            height=1,
            index=0,
            accepted=False,
            error_code=expected_error,
            state_changed=False,
        )
    ]
    assert executed_body["evidence"]["rejection_receipts"] == receipts
