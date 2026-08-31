from __future__ import annotations

import sys

import pytest

import src.integration.zusd_tau_token as zusd_tau_token
from src.integration.asset_ids import derive_zusd_asset_id
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zusd_tau_token import (
    TokenTauReceipt,
    ZUSDTauTokenConfig,
    create_tau_token_operation,
    derive_zusd_tau_asset_id,
    prepare_zusd_tau_token_operation,
    token_sender_nonce_key,
)


def test_zusd_tau_token_identity_helpers_are_stable() -> None:
    asset_id = derive_zusd_tau_asset_id(chain_id="tau-local")
    assert asset_id == "0xa64d446f162831e37fa13cbc0faf1ebac383955127dccf2f676c063de8d0cc61"
    assert asset_id == derive_zusd_asset_id(chain_id="tau-local")
    assert asset_id.startswith("0x")
    assert len(asset_id) == 66

    sender = "0x" + bls_pubkey_hex_from_privkey(31)
    nonce_key = token_sender_nonce_key(sender)
    assert nonce_key.startswith("0x")
    assert len(nonce_key) == 98
    with pytest.raises(ValueError, match="chain_id must be a non-empty string"):
        derive_zusd_tau_asset_id(chain_id="")
    with pytest.raises(ValueError, match="symbol must be a non-empty string"):
        derive_zusd_tau_asset_id(symbol="")
    with pytest.raises(ValueError, match="chain_id must be a non-empty string"):
        derive_zusd_asset_id(chain_id=object())  # type: ignore[arg-type]
    assert derive_zusd_asset_id(chain_id=" tau-local ", symbol=" zUSD ") == asset_id


def test_create_tau_token_operation_covers_all_actions_and_validation() -> None:
    sender = "0x" + bls_pubkey_hex_from_privkey(32)
    recipient = "0x" + bls_pubkey_hex_from_privkey(33)
    asset_id = derive_zusd_tau_asset_id(chain_id="tau-local")

    transfer = create_tau_token_operation(
        action="transfer",
        asset_id=asset_id,
        nonce=1,
        amount=10,
        deadline=99,
        sender_pubkey=sender,
        to_pubkey=recipient,
    )
    mint = create_tau_token_operation(
        action="mint",
        asset_id=asset_id,
        nonce=2,
        amount=10,
        deadline=99,
        operator_pubkey=sender,
        to_pubkey=recipient,
    )
    burn = create_tau_token_operation(
        action="burn",
        asset_id=asset_id,
        nonce=3,
        amount=10,
        deadline=99,
        sender_pubkey=sender,
    )

    assert transfer["action"] == "transfer"
    assert mint["action"] == "mint"
    assert burn["action"] == "burn"

    with pytest.raises(ValueError, match="transfer requires"):
        create_tau_token_operation(action="transfer", asset_id=asset_id, nonce=1, amount=1, deadline=1)
    with pytest.raises(ValueError, match="mint requires"):
        create_tau_token_operation(action="mint", asset_id=asset_id, nonce=1, amount=1, deadline=1)
    with pytest.raises(ValueError, match="burn requires"):
        create_tau_token_operation(action="burn", asset_id=asset_id, nonce=1, amount=1, deadline=1)
    with pytest.raises(TypeError, match="nonce must be an int"):
        create_tau_token_operation(
            action="burn",
            asset_id=asset_id,
            nonce="bad",  # type: ignore[arg-type]
            amount=1,
            deadline=1,
            sender_pubkey=sender,
        )
    with pytest.raises(ValueError, match="amount out of u32 range"):
        create_tau_token_operation(
            action="burn",
            asset_id=asset_id,
            nonce=1,
            amount=-1,
            deadline=1,
            sender_pubkey=sender,
        )


def test_prepare_zusd_tau_transfer_success_builds_receipts_and_tx_payload() -> None:
    privkey = 34
    sender = "0x" + bls_pubkey_hex_from_privkey(privkey)
    recipient = "0x" + bls_pubkey_hex_from_privkey(35)

    report = prepare_zusd_tau_token_operation(
        action="transfer",
        amount=100,
        deadline=99,
        last_used_nonce=0,
        total_supply_before=1_000,
        sender_balance_before=400,
        recipient_balance_before=50,
        sender_pubkey=sender,
        recipient_pubkey=recipient,
        chain_id="tau-local",
        signer_privkey=privkey,
        tx_sequence_number=7,
        tx_expiration_time=999,
    )

    assert report.action == "transfer"
    assert report.nonce_after == 1
    assert report.sender_balance_after == 300
    assert report.recipient_balance_after == 150
    assert report.supply_after == 1_000
    assert report.operations["9"][0]["sender_pubkey"] == sender
    assert len(report.tau_receipts) == 2
    assert report.tau_tx_payload is not None
    assert report.tau_tx_payload["sequence_number"] == 7


def test_prepare_zusd_tau_token_covers_mint_and_burn() -> None:
    operator = "0x" + bls_pubkey_hex_from_privkey(36)
    recipient = "0x" + bls_pubkey_hex_from_privkey(37)
    burner = "0x" + bls_pubkey_hex_from_privkey(38)

    mint = prepare_zusd_tau_token_operation(
        action="mint",
        amount=50,
        deadline=99,
        last_used_nonce=4,
        total_supply_before=1_000,
        recipient_balance_before=10,
        operator_pubkey=operator,
        recipient_pubkey=recipient,
        signer_privkey=36,
    )
    burn = prepare_zusd_tau_token_operation(
        action="burn",
        amount=40,
        deadline=99,
        last_used_nonce=8,
        total_supply_before=1_000,
        sender_balance_before=100,
        sender_pubkey=burner,
        signer_privkey=38,
    )

    assert mint.supply_after == 1_050
    assert mint.recipient_balance_after == 60
    assert len(mint.tau_receipts) == 1
    assert burn.supply_after == 960
    assert burn.sender_balance_after == 60
    assert len(burn.tau_receipts) == 1


def test_prepare_zusd_tau_token_rejects_invalid_budget_and_signer_inputs() -> None:
    sender = "0x" + bls_pubkey_hex_from_privkey(39)
    recipient = "0x" + bls_pubkey_hex_from_privkey(40)

    with pytest.raises(ValueError, match="insufficient"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=101,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=1_000,
            sender_balance_before=100,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
        )
    with pytest.raises(ValueError, match="overflow"):
        prepare_zusd_tau_token_operation(
            action="mint",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=0xFFFFFFFF,
            recipient_balance_before=0,
            operator_pubkey=sender,
            recipient_pubkey=recipient,
        )
    with pytest.raises(ValueError, match="recipient balance overflow"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=100,
            sender_balance_before=10,
            recipient_balance_before=0xFFFFFFFF,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
        )
    with pytest.raises(ValueError, match="signer_privkey does not match"):
        prepare_zusd_tau_token_operation(
            action="burn",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
            sender_balance_before=10,
            sender_pubkey=sender,
            signer_privkey=41,
        )
    with pytest.raises(ValueError, match="provided together"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
            sender_balance_before=10,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
            tx_sequence_number=1,
        )
    with pytest.raises(ValueError, match="next token nonce exceeds u32"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=1,
            deadline=99,
            last_used_nonce=0xFFFFFFFF,
            total_supply_before=10,
            sender_balance_before=10,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
        )
    with pytest.raises(ValueError, match="burn requires sender_pubkey"):
        prepare_zusd_tau_token_operation(
            action="burn",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
        )
    with pytest.raises(ValueError, match="mint requires operator_pubkey and recipient_pubkey"):
        prepare_zusd_tau_token_operation(
            action="mint",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
        )
    with pytest.raises(ValueError, match="transfer requires sender_pubkey and recipient_pubkey"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
        )
    with pytest.raises(ValueError, match="burn amount exceeds balance or supply"):
        prepare_zusd_tau_token_operation(
            action="burn",
            amount=11,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
            sender_balance_before=10,
            sender_pubkey=sender,
        )
    with pytest.raises(ValueError, match="signer_privkey is required"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=1,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=10,
            sender_balance_before=10,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
            tx_sequence_number=1,
            tx_expiration_time=1,
        )


def test_prepare_zusd_tau_token_tau_verification_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    sender = "0x" + bls_pubkey_hex_from_privkey(42)
    recipient = "0x" + bls_pubkey_hex_from_privkey(43)

    monkeypatch.setattr(zusd_tau_token, "_resolve_tau_bin", lambda config: (True, sys.executable, None))
    monkeypatch.setattr(zusd_tau_token, "_verify_tau_receipt", lambda **kwargs: None)
    report = prepare_zusd_tau_token_operation(
        action="transfer",
        amount=10,
        deadline=99,
        last_used_nonce=0,
        total_supply_before=100,
        sender_balance_before=50,
        recipient_balance_before=0,
        sender_pubkey=sender,
        recipient_pubkey=recipient,
        tau_config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert len(report.tau_receipts) == 2

    monkeypatch.setattr(zusd_tau_token, "_resolve_tau_bin", lambda config: (False, None, "missing tau"))
    with pytest.raises(ValueError, match="tau_tool_unavailable:missing tau"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=10,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=100,
            sender_balance_before=50,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
            tau_config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
        )

    monkeypatch.setattr(zusd_tau_token, "_resolve_tau_bin", lambda config: (True, sys.executable, None))
    monkeypatch.setattr(zusd_tau_token, "_verify_tau_receipt", lambda **kwargs: "tau_token_mismatch:protocol_token_v1:local=1,tau=0")
    with pytest.raises(ValueError, match="tau_token_mismatch"):
        prepare_zusd_tau_token_operation(
            action="transfer",
            amount=10,
            deadline=99,
            last_used_nonce=0,
            total_supply_before=100,
            sender_balance_before=50,
            recipient_balance_before=0,
            sender_pubkey=sender,
            recipient_pubkey=recipient,
            tau_config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
        )


def test_zusd_tau_token_internal_helper_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    receipt = TokenTauReceipt(
        spec_id="protocol_token_v1",
        gate_output="o1",
        steps=({"i1": 0},),
        expected_ok=True,
    )

    monkeypatch.setattr(
        zusd_tau_token,
        "run_tau_spec_steps",
        lambda **kwargs: (_ for _ in ()).throw(RuntimeError("tau boom")),
    )
    assert (
        zusd_tau_token._verify_tau_receipt(
            tau_bin=sys.executable,
            config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "tau_token_runner_error:RuntimeError:tau boom"
    )

    monkeypatch.setattr(zusd_tau_token, "run_tau_spec_steps", lambda **kwargs: {0: {}})
    assert (
        zusd_tau_token._verify_tau_receipt(
            tau_bin=sys.executable,
            config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "tau_token_missing_output:o1"
    )

    monkeypatch.setattr(zusd_tau_token, "run_tau_spec_steps", lambda **kwargs: {0: {"o1": 0}})
    assert (
        zusd_tau_token._verify_tau_receipt(
            tau_bin=sys.executable,
            config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "tau_token_mismatch:protocol_token_v1:local=1,tau=0"
    )

    monkeypatch.setattr(zusd_tau_token, "run_tau_spec_steps", lambda **kwargs: {0: {"o1": 1}})
    assert (
        zusd_tau_token._verify_tau_receipt(
            tau_bin=sys.executable,
            config=ZUSDTauTokenConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        is None
    )

    assert zusd_tau_token._resolve_tau_bin(ZUSDTauTokenConfig(enabled=True, tau_bin="rel", allow_path_lookup=False)) == (
        False,
        None,
        "tau_bin must be an absolute path when allow_path_lookup=False",
    )
    assert zusd_tau_token._resolve_tau_bin(ZUSDTauTokenConfig(enabled=True)) == (
        False,
        None,
        "tau_bin not configured (set ZUSDTauTokenConfig.tau_bin)",
    )
    monkeypatch.setattr(zusd_tau_token.os.path, "isfile", lambda path: False)
    monkeypatch.setattr(zusd_tau_token.os, "access", lambda path, mode: False)
    assert zusd_tau_token._resolve_tau_bin(
        ZUSDTauTokenConfig(enabled=True, tau_bin="/not/executable", allow_path_lookup=False)
    ) == (False, None, "tau_bin is not an executable file: /not/executable")
    monkeypatch.setattr(zusd_tau_token.os.path, "isfile", lambda path: True)
    monkeypatch.setattr(zusd_tau_token.os, "access", lambda path, mode: True)
    assert zusd_tau_token._resolve_tau_bin(
        ZUSDTauTokenConfig(enabled=True, tau_bin="/ok/tau", allow_path_lookup=False)
    ) == (True, "/ok/tau", None)
    assert zusd_tau_token._resolve_tau_bin(
        ZUSDTauTokenConfig(enabled=True, tau_bin="tau", allow_path_lookup=True)
    ) == (True, "tau", None)
    monkeypatch.setattr(zusd_tau_token, "find_tau_bin", lambda: "/ok/from/path")
    assert zusd_tau_token._resolve_tau_bin(
        ZUSDTauTokenConfig(enabled=True, allow_path_lookup=True)
    ) == (True, "/ok/from/path", None)
    monkeypatch.setattr(zusd_tau_token, "find_tau_bin", lambda: None)
    assert zusd_tau_token._resolve_tau_bin(
        ZUSDTauTokenConfig(enabled=True, allow_path_lookup=True)
    ) == (False, None, "tau binary not found (fail-closed)")
