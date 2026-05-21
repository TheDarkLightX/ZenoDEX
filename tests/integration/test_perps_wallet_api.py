from __future__ import annotations

import json
import sys

import pytest

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
    build_perps_wallet_authority_profile_v1,
    evaluate_perps_wallet_authority_profile_v1,
    evaluate_perps_wallet_recovery_exercise_v1,
    evaluate_perps_wallet_rotation_exercise_v1,
    perps_wallet_recovery_exercise_hash_v1,
    perps_wallet_rotation_exercise_hash_v1,
)
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_profile_v1,
)
from src.integration.perp_engine import PerpEngineConfig, _kernel_initial_global_state, apply_perp_ops
from src.integration.tau_net_client import (
    TauNetRpcError,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    sign_perp_op_for_engine,
)
from src.integration.zeno_key_manager import KeyRef, RecoveryGuardian, SocialRecoveryPolicy, ZenoKeyManager
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0, infer_artifact_hash_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
import src.integration.perps_wallet_api as perps_wallet_api


CHAIN_ID = "tau-test-perps-wallet"
ALICE_PRIVKEY = 83
BOB_PRIVKEY = 84
ORACLE_PRIVKEY = 85
OPERATOR_PRIVKEY = 86
CAROL_PRIVKEY = 87
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)
CAROL = "0x" + bls_pubkey_hex_from_privkey(CAROL_PRIVKEY)
MARKET_ID = "perp:ch2p:test"
ISOLATED_MARKET_ID = "perp:isolated:test"


def _privkey_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, byteorder="big", signed=False).hex()


def _perps_wallet_key_manager(*, second_pubkey: str = BOB) -> dict[str, object]:
    return ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=ALICE, recovery_policy_id="recovery-perps-wallet-a"),
            KeyRef(key_id="perps-wallet-b", public_key=second_pubkey, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-a",
                subject_key_id="perps-wallet-a",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
        ),
    ).public_dict()


def _perps_wallet_signer_registry(*, second_pubkey: str = BOB, threshold: int = 1) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="perps-wallet-authority-v1",
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
        threshold=threshold,
        signers=(
            {
                "signer_id": "wallet-a",
                "key_id": "perps-wallet-a",
                "public_key": ALICE,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "wallet-b",
                "key_id": "perps-wallet-b",
                "public_key": second_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )


def _perps_wallet_authority_profile(**overrides: object) -> dict[str, object]:
    base = {
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "chain_id": CHAIN_ID,
        "stage": "production",
        "enabled": True,
        "key_manager": _perps_wallet_key_manager(),
        "signer_registry": _perps_wallet_signer_registry(),
        "wallet_ux": {
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
            "replay_protection_required": True,
            "recovery_policy_required": True,
        },
        "proof_profile": {
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": True,
            "zk_or_proof_required": True,
            "runtime_proof_profile": "perps-stream8-risc0-or-equivalent-v1",
        },
        "transaction_scope": {
            "stream_key": "8",
            "allowed_actions": [
                "init_market_2p",
                "deposit_collateral",
                "withdraw_collateral",
                "set_position_pair",
                "advance_epoch",
                "publish_clearing_price",
                "settle_epoch",
                "partial_liquidate",
            ],
        },
    }
    base.update(overrides)
    return build_perps_wallet_authority_profile_v1(**base)


def _perps_wallet_recovery_exercise(**overrides: object) -> dict[str, object]:
    base = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
        "chain_id": CHAIN_ID,
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "subject_key_id": "perps-wallet-a",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "current_epoch": 13,
        "approvals": ["guardian-oracle", "guardian-operator"],
    }
    base.update(overrides)
    exercise = dict(base)
    exercise_hash = perps_wallet_recovery_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-oracle",
            key_id="guardian-oracle",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-operator",
            key_id="guardian-operator",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return exercise


def _perps_wallet_rotated_profile() -> dict[str, object]:
    return build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        stage="production",
        enabled=True,
        key_manager=ZenoKeyManager(
            key_refs=(
                KeyRef(key_id="perps-wallet-c", public_key=CAROL, recovery_policy_id="recovery-perps-wallet-c"),
                KeyRef(key_id="perps-wallet-b", public_key=BOB, recovery_policy_id="recovery-perps-wallet-b"),
            ),
            recovery_policies=(
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-c",
                    subject_key_id="perps-wallet-c",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                        RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                    ),
                ),
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-b",
                    subject_key_id="perps-wallet-b",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                        RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                    ),
                ),
            ),
        ).public_dict(),
        signer_registry=build_signer_registry_v0(
            registry_id="perps-wallet-authority-v1",
            payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
            threshold=1,
            signers=(
                {
                    "signer_id": "wallet-c",
                    "key_id": "perps-wallet-c",
                    "public_key": CAROL,
                    "weight": 1,
                    "status": "active",
                },
                {
                    "signer_id": "wallet-b",
                    "key_id": "perps-wallet-b",
                    "public_key": BOB,
                    "weight": 1,
                    "status": "active",
                },
            ),
        ),
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
            "replay_protection_required": True,
            "recovery_policy_required": True,
        },
        proof_profile={
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": True,
            "zk_or_proof_required": True,
            "runtime_proof_profile": "perps-stream8-risc0-or-equivalent-v1",
        },
        transaction_scope={
            "stream_key": "8",
            "allowed_actions": [
                "init_market_2p",
                "deposit_collateral",
                "withdraw_collateral",
                "set_position_pair",
                "advance_epoch",
                "publish_clearing_price",
                "settle_epoch",
                "partial_liquidate",
            ],
        },
    )


def _perps_wallet_rotation_exercise(**overrides: object) -> dict[str, object]:
    base = {
        "schema": PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
        "chain_id": CHAIN_ID,
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "rotated_key_id": "perps-wallet-a",
        "replacement_key_id": "perps-wallet-c",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "broadcast_at_epoch": 13,
        "broadcast_reference": "tau-tx:perps-wallet-rotation-1",
        "approvals": ["guardian-oracle", "guardian-operator"],
        "next_wallet_authority_profile": _perps_wallet_rotated_profile(),
    }
    base.update(overrides)
    exercise = dict(base)
    exercise_hash = perps_wallet_rotation_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-oracle",
            key_id="guardian-oracle",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-operator",
            key_id="guardian-operator",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return exercise


def _oracle_authority_key_manager(*, second_pubkey: str = OPERATOR) -> dict[str, object]:
    return ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=ORACLE),
            KeyRef(key_id="oracle-authority-b", public_key=second_pubkey),
        )
    ).public_dict()


def _oracle_authority_signer_registry(*, second_pubkey: str = OPERATOR, threshold: int = 2) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="oracle-production-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=threshold,
        signers=(
            {
                "signer_id": "oracle-a",
                "key_id": "oracle-authority-a",
                "public_key": ORACLE,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "oracle-b",
                "key_id": "oracle-authority-b",
                "public_key": second_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )


def _oracle_authority_profile(**overrides: object) -> dict[str, object]:
    base = {
        "authority_id": "oracle-production-authority-v1",
        "chain_id": CHAIN_ID,
        "stage": "production",
        "enabled": True,
        "key_manager": _oracle_authority_key_manager(),
        "signer_registry": _oracle_authority_signer_registry(),
        "wallet_ux": {
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
        },
        "proof_profile": {
            "zk_or_proof_required": True,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "zenooracle-o3-replay-zk-profile-v1",
        },
    }
    base.update(overrides)
    profile = build_oracle_authority_profile_v1(**base)
    profile["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-a",
            key_id="oracle-authority-a",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-b",
            key_id="oracle-authority-b",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return profile


def _wrapped_app_state(state: DexState) -> dict[str, object]:
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }


def _signed_init_op(*, quote_asset: str, nonce_a: int = 1, nonce_b: int = 1) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": 123456789,
        "nonce_a": nonce_a,
        "nonce_b": nonce_b,
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _state_with_market_and_balance(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID),
        state=state,
        operations={"5": [_signed_init_op(quote_asset=quote_asset)]},
        tx_sender_pubkey=ALICE,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    res.state.balances.set(ALICE, quote_asset, 5_000)
    return res.state


def _apply_perps(state: DexState, ops: list[dict[str, object]], *, sender: str = OPERATOR) -> DexState:
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID, oracle_pubkey=ORACLE),
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _state_with_advanced_market(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply_perps(state, [_signed_init_op(quote_asset=quote_asset)])
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )


def _state_ready_to_settle(*, quote_asset: str) -> DexState:
    state = _state_with_advanced_market(quote_asset=quote_asset)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": 100_000_000,
        "deadline": 123456789,
        "oracle_nonce": 1,
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=1,
    )
    return _apply_perps(state, [op], sender=ORACLE)


def _signed_set_position_pair(*, new_a: int, new_b: int, nonce_a: int, nonce_b: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "set_position_pair",
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": 123456789,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _signed_publish_price(*, price_e8: int, oracle_nonce: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": 123456789,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=oracle_nonce,
    )
    return op


def _state_after_pair_liquidation(*, quote_asset: str) -> DexState:
    state = _state_ready_to_settle(quote_asset=quote_asset)
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
    )
    state.balances.set(ALICE, quote_asset, 1000)
    state.balances.set(BOB, quote_asset, 1000)
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 100,
            }
        ],
        sender=ALICE,
    )
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": BOB,
                "amount": 100,
            }
        ],
        sender=BOB,
    )
    state = _apply_perps(state, [_signed_set_position_pair(new_a=1000, new_b=-1000, nonce_a=2, nonce_b=2)])
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )
    state = _apply_perps(state, [_signed_publish_price(price_e8=105_000_000, oracle_nonce=2)], sender=ORACLE)
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
    )


def _state_with_posted_collateral(*, quote_asset: str) -> DexState:
    state = _state_with_market_and_balance(quote_asset=quote_asset)
    return _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 1_000,
            }
        ],
        sender=ALICE,
    )


def _state_with_isolated_liquidatable_account(*, quote_asset: str) -> DexState:
    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 5,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 10_000_000_000,
            "max_oracle_staleness_epochs": 100,
            "max_oracle_move_bps": 500,
            "initial_margin_bps": 1000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_position_abs": 1_000_000,
            "fee_pool_quote": 0,
            "fee_income": 0,
            "initial_insurance": 100_000,
            "insurance_balance": 100_000,
            "claims_paid": 0,
            "min_notional_for_bounty": 100_000_000,
        }
    )
    market = PerpMarketState(
        quote_asset=quote_asset,
        global_state=global_state,
        accounts={
            ALICE: PerpAccountState(
                position_base=100,
                entry_price_e8=10_000_000_000,
                collateral_quote=300,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            )
        },
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={ISOLATED_MARKET_ID: market}),
    )


class _FakeClient:
    app_state: dict[str, object] = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    sent: list[dict[str, object]] = []
    native_balances: dict[str, int] = {}

    def __init__(self, _cfg=None) -> None:
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps({"app_hash": "sha256:" + "cd" * 32, "app_state": self.app_state}, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == ALICE[2:]:
            return 9
        if sender_pubkey_hex == BOB[2:]:
            return 11
        if sender_pubkey_hex == ORACLE[2:]:
            return 13
        if sender_pubkey_hex == OPERATOR[2:]:
            return 15
        return 0

    def get_balance(self, address_hex: str) -> int:
        return int(self.native_balances.get(address_hex, 0))

    def sendtx(self, payload):
        self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


def _fake_client_apply_stream8_payload(client: _FakeClient, payload: object) -> None:
    client.sent.append(dict(payload))
    assert isinstance(payload, dict)
    wire_ops = payload.get("operations")
    assert isinstance(wire_ops, dict)
    stream_ops = json.loads(wire_ops["8"])
    state = perps_wallet_api._state_from_app_state(client.app_state)
    result = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID, oracle_pubkey=ORACLE, operator_pubkey=OPERATOR),
        state=state,
        operations={"5": stream_ops},
        tx_sender_pubkey="0x" + str(payload["sender_pubkey"]),
        block_timestamp=1,
    )
    assert result.ok, result.error
    assert result.state is not None
    client.app_state = _wrapped_app_state(result.state)


@pytest.fixture(autouse=True)
def _reset_fake_client_balances() -> None:
    _FakeClient.native_balances = {}
    yield
    _FakeClient.native_balances = {}


def test_perps_wallet_authority_missing_profile_is_blocked() -> None:
    status = evaluate_perps_wallet_authority_profile_v1(None, expected_chain_id=CHAIN_ID)

    assert status["ok"] is False
    assert status["production_wallet_authority"] is False
    assert status["status"] == "blocked"
    assert status["readiness_gaps"] == ["perps wallet authority profile is missing"]


def test_perps_wallet_authority_complete_profile_is_ready() -> None:
    profile = _perps_wallet_authority_profile()
    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["production_wallet_authority"] is True
    assert status["status"] == "ready"
    assert status["readiness_gaps"] == []
    assert status["threshold"] == 1
    assert status["active_signer_count"] == 2
    assert status["key_ref_count"] == 2
    assert status["recovery_policy_count"] == 2
    assert status["recoverable_active_key_count"] == 2
    assert status["wallet_ux"]["device_approval_required"] is True
    assert status["wallet_ux"]["replay_protection_required"] is True
    assert status["wallet_ux"]["recovery_policy_required"] is True
    assert status["proof_profile"]["state_delta_witness_required"] is True
    assert status["proof_profile"]["runtime_proof_profile"] == "perps-stream8-risc0-or-equivalent-v1"
    assert status["transaction_scope"]["stream_key"] == "8"
    assert "deposit_collateral" in status["transaction_scope"]["allowed_actions"]
    assert {policy["subject_key_id"] for policy in status["recovery_policies"]} == {
        "perps-wallet-a",
        "perps-wallet-b",
    }
    assert infer_artifact_hash_v0(
        artifact=profile,
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    ) == profile["wallet_authority_hash"]


def test_perps_wallet_authority_blocks_bad_controls_and_chain_mismatch() -> None:
    profile = _perps_wallet_authority_profile(
        chain_id="wrong-chain",
        stage="devnet",
        enabled=False,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": False,
            "device_approval_required": True,
            "replay_protection_required": False,
            "recovery_policy_required": False,
        },
        proof_profile={
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": False,
            "zk_or_proof_required": False,
            "runtime_proof_profile": "",
        },
        transaction_scope={"stream_key": "9", "allowed_actions": []},
    )

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)
    gaps = set(status["readiness_gaps"])

    assert status["production_wallet_authority"] is False
    assert "perps wallet authority profile is not enabled" in gaps
    assert "perps wallet authority profile stage must be production" in gaps
    assert "perps wallet authority profile chain_id mismatch" in gaps
    assert "wallet_ux.key_manager_required must be true" in gaps
    assert "wallet_ux.replay_protection_required must be true" in gaps
    assert "wallet_ux.recovery_policy_required must be true" in gaps
    assert "proof_profile.state_delta_witness_required must be true" in gaps
    assert "proof_profile.zk_or_proof_required must be true" in gaps
    assert "proof_profile.runtime_proof_profile must be a non-empty string" in gaps
    assert "transaction_scope.stream_key must be 8" in gaps
    assert "transaction_scope.allowed_actions must be a non-empty string list" in gaps


def test_perps_wallet_authority_blocks_signer_key_manager_public_key_mismatch() -> None:
    profile = _perps_wallet_authority_profile(
        key_manager=_perps_wallet_key_manager(second_pubkey=ORACLE),
        signer_registry=_perps_wallet_signer_registry(second_pubkey=BOB),
    )

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["production_wallet_authority"] is False
    assert "active signer key_id perps-wallet-b public key mismatch" in status["readiness_gaps"]


def test_perps_wallet_authority_blocks_active_signer_without_recovery_policy() -> None:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=ALICE),
            KeyRef(key_id="perps-wallet-b", public_key=BOB, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
        ),
    ).public_dict()
    profile = _perps_wallet_authority_profile(key_manager=key_manager)

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["production_wallet_authority"] is False
    assert status["recovery_policy_count"] == 1
    assert status["recoverable_active_key_count"] == 1
    assert "active signer key_id perps-wallet-a has no recovery_policy_id" in status["readiness_gaps"]


def test_perps_wallet_recovery_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_recovery_exercise()

    status = evaluate_perps_wallet_recovery_exercise_v1(profile, exercise, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["recovery_exercise_ready"] is True
    assert status["status"] == "ready"
    assert status["errors"] == []
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_recovery_exercise_hash_v1(exercise)
    assert status["subject_key_id"] == "perps-wallet-a"
    assert status["evaluation"]["ok"] is True
    assert status["evaluation"]["delay_ok"] is True
    assert status["evaluation"]["threshold_ok"] is True
    assert status["evaluation"]["accepted_weight"] == 2
    assert status["evaluation_hash"] == status["evaluation"]["evaluation_hash"]
    assert status["guardian_signature_quorum"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["threshold"] == 2
    assert status["guardian_signature_quorum_hash"] == status["guardian_signature_quorum"]["quorum_report_hash"]
    encoded = json.dumps(status, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_perps_wallet_recovery_exercise_blocks_early_request() -> None:
    status = evaluate_perps_wallet_recovery_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_recovery_exercise(current_epoch=12),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["recovery_exercise_ready"] is False
    assert status["status"] == "blocked"
    assert "recovery_policy_not_satisfied" in status["errors"]
    assert status["evaluation"]["delay_ok"] is False
    assert status["evaluation"]["threshold_ok"] is True


def test_perps_wallet_recovery_exercise_blocks_bad_guardian_signature_quorum() -> None:
    exercise = _perps_wallet_recovery_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status = evaluate_perps_wallet_recovery_exercise_v1(
        _perps_wallet_authority_profile(),
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["recovery_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in status["errors"])


def test_perps_wallet_rotation_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_rotation_exercise()

    status = evaluate_perps_wallet_rotation_exercise_v1(profile, exercise, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["rotation_exercise_ready"] is True
    assert status["status"] == "ready"
    assert status["errors"] == []
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_rotation_exercise_hash_v1(exercise)
    assert status["rotated_key_id"] == "perps-wallet-a"
    assert status["replacement_key_id"] == "perps-wallet-c"
    assert status["next_wallet_authority_hash"] == exercise["next_wallet_authority_profile"]["wallet_authority_hash"]
    assert status["evaluation"]["ok"] is True
    assert status["evaluation"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["threshold"] == 2
    assert status["guardian_signature_quorum_hash"] == status["guardian_signature_quorum"]["quorum_report_hash"]


def test_perps_wallet_rotation_exercise_blocks_missing_rotation_transition() -> None:
    status = evaluate_perps_wallet_rotation_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_rotation_exercise(replacement_key_id="perps-wallet-b"),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["rotation_exercise_ready"] is False
    assert status["status"] == "blocked"
    assert "replacement key is already active in current wallet authority" in status["errors"]


def test_perps_wallet_rotation_exercise_blocks_bad_guardian_signature_quorum() -> None:
    exercise = _perps_wallet_rotation_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status = evaluate_perps_wallet_rotation_exercise_v1(
        _perps_wallet_authority_profile(),
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["rotation_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in status["errors"])


def test_prepare_init_market_2p_builds_signed_stream_8_and_preflights(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 0}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["transport"]["tx_sequence_number"] == 9
    assert payload["transport"]["tx_fee_limit"] == "0"
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["report"]["operations"]["8"][0]["action"] == "init_market_2p"
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["proof"]["profile"]["profile_id"] == "perps_stream8_live_wallet_v0"
    assert payload["proof"]["profile"]["zk_proof_verified"] is False
    assert "risc0_zkvm_wrapper" in payload["proof"]["profile"]["not_covered"]
    receipt = payload["proof"]["intent_receipt"]
    assert receipt["profile_id"] == "perps_stream8_live_wallet_v0"
    assert receipt["receipt_hash"].startswith("0x")
    assert receipt["body"]["stream_key"] == "8"
    assert receipt["body"]["engine_stream_key"] == "5"
    assert receipt["body"]["app_hash_before"] == "sha256:" + "cd" * 32
    assert receipt["body"]["app_hash_after"] is None
    assert receipt["body"]["action"] == "init_market_2p"
    assert receipt["body"]["preflight_ok"] is True
    assert receipt["body"]["tau_tx_payload_hash"] is None
    assert receipt["body"]["zk_proof_verified"] is False
    assert payload["proof"]["zk_wrapper"]["required"] is False
    assert payload["proof"]["zk_wrapper"]["proof_provided"] is False
    assert payload["proof"]["zk_wrapper"]["zk_proof_verified"] is False


def test_prepare_init_market_requires_zk_proof_when_enabled(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps([sys.executable, "-c", "import json,sys; json.load(sys.stdin); print('{\"ok\": true}')"]),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"] == "zk_proof_required: zk_proof missing"


def test_prepare_init_market_accepts_verified_zk_wrapper(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps([sys.executable, "-c", "import json,sys; obj=json.load(sys.stdin); assert obj['surface']=='perps_stream8'; print('{\"ok\": true}')"]),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["surface"] == "perps_stream8"
    assert wrapper["required"] is True
    assert wrapper["proof_provided"] is True
    assert wrapper["verifier_configured"] is True
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["proof_intent_receipt_hash"] == payload["proof"]["intent_receipt"]["receipt_hash"]
    assert payload["proof"]["profile"]["zk_proof_verified"] is True
    assert payload["proof"]["profile"]["promotion_ready"] is True


def test_submit_deposit_collateral_rejected_zk_proof_blocks_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                "import json,sys; json.load(sys.stdin); print('{\"ok\": false, \"error\": \"fixture proof rejected\"}')",
            ]
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def fail_sendtx(self, payload):  # pragma: no cover - this is a disaster-state sentinel.
        raise AssertionError("zk_reject_broadcasts_tx")

    monkeypatch.setattr(_FakeClient, "sendtx", fail_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "bad-fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"] == "zk_proof_required: fixture proof rejected"
    assert _FakeClient.sent == []


def test_prepare_reports_tau_fee_limit_native_balance_posture(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 1}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_fee_limit"] == "2"
    assert payload["transport"]["native_balance_e8"] == 1
    assert payload["transport"]["fee_limit_native_balance_ok"] is False
    assert payload["transport"]["fee_limit_warning"] == "native balance is below requested Tau fee limit"
    assert payload["report"]["fee_limit"]["native_balance_covers_fee_limit"] is False


def test_prepare_rejects_bad_tx_fee_limit(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "1.5",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_tx_fee_limit"}


def test_prepare_rejects_bad_counterparty_signature_in_preflight(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    good = _signed_init_op(quote_asset=quote_asset)
    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": good["sig_a"],
        "sig_b": "0x" + "00" * 96,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert "account_b signature invalid" in payload["report"]["preflight"]["error"]


def test_submit_deposit_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["account_pubkey"] == ALICE
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["transport"]["quote_balance"] == 5_000
    assert payload["report"]["tau_tx_payload"]["fee_limit"] == "2"
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"


def test_submit_accepts_external_signed_tau_payload_without_local_signing(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def sendtx_and_apply(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_and_apply)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    assert prepared["ok"] is True
    assert prepared["report"]["tau_tx_payload"] is None

    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["allow_local_signing"] is False
    assert payload["transport"]["signing_mode"] == "external_signed_payload"
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["tau_tx_payload"] == external_payload
    assert _FakeClient.sent == [external_payload]
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    assert json.loads(payload["report"]["tau_tx_payload"]["operations"]["8"])[0]["action"] == "deposit_collateral"
    proof_body = payload["proof"]["intent_receipt"]["body"]
    assert proof_body["app_hash_before"] == "sha256:" + "cd" * 32
    assert proof_body["app_hash_after"] == "sha256:" + "cd" * 32
    assert proof_body["signing_mode"] == "external_signed_payload"
    assert proof_body["tau_tx_payload_hash"].startswith("0x")
    assert proof_body["state_delta_witness_hash"].startswith("0x")
    witness = payload["proof"]["intent_receipt"]["state_delta_witness"]
    assert witness["schema"] == "zenodex/perps_wallet/state_delta_witness/v1"
    assert witness["stream_key"] == "8"
    assert witness["action"] == "deposit_collateral"
    assert witness["app_hash_before"] == "sha256:" + "cd" * 32
    assert witness["app_hash_after"] == "sha256:" + "cd" * 32
    assert len(witness["changed_markets"]) == 1
    assert witness["changed_markets"][0]["market_id"] == MARKET_ID
    assert witness["changed_markets"][0]["deltas"]["collateral_e8_a"] == 1000 * 100_000_000


def test_submit_external_signed_payload_can_retry_after_tau_send_failure_without_state_drift(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    initial_app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.app_state = json.loads(json.dumps(initial_app_state))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    _FakeClient.send_attempts = 0
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def flaky_sendtx(self, payload):
        type(self).send_attempts += 1
        if type(self).send_attempts == 1:
            raise TauNetRpcError("temporary tau node send failure")
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted after retry"

    monkeypatch.setattr(_FakeClient, "sendtx", flaky_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}

    status_code, failed = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 502
    assert failed["ok"] is False
    assert failed["error"] == "tau_rpc_error"
    assert "temporary tau node send failure" in failed["detail"]
    assert _FakeClient.sent == []
    assert _FakeClient.app_state == initial_app_state

    status_code, accepted = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 200
    assert accepted["ok"] is True
    assert accepted["submission"]["sendtx_response"] == "SUCCESS tx accepted after retry"
    assert accepted["transport"]["signing_mode"] == "external_signed_payload"
    assert _FakeClient.sent == [external_payload]
    witness = accepted["proof"]["intent_receipt"]["state_delta_witness"]
    assert witness["changed_markets"][0]["deltas"]["collateral_e8_a"] == 1000 * 100_000_000


def test_submit_external_signed_payload_replay_after_node_restart_rejected_before_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    _FakeClient.sequence_by_sender = {ALICE[2:]: 9}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def sequence_from_persisted_node(self, sender_pubkey_hex: str) -> int:
        return int(type(self).sequence_by_sender.get(sender_pubkey_hex, 0))

    def sendtx_apply_and_advance(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        sender = str(payload["sender_pubkey"])
        type(self).sequence_by_sender[sender] = int(type(self).sequence_by_sender.get(sender, 0)) + 1
        type(self).app_state = json.loads(json.dumps(self.app_state))
        return "SUCCESS tx accepted before restart"

    monkeypatch.setattr(_FakeClient, "get_sequence", sequence_from_persisted_node)
    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_apply_and_advance)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    assert prepared["transport"]["tx_sequence_number"] == 9
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}

    status_code, accepted = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 200
    assert accepted["ok"] is True
    assert accepted["submission"]["sendtx_response"] == "SUCCESS tx accepted before restart"
    assert len(_FakeClient.sent) == 1
    assert _FakeClient.sequence_by_sender[ALICE[2:]] == 10
    persisted_after_submit = json.loads(json.dumps(_FakeClient.app_state))

    class _RestartedFakeClient(_FakeClient):
        app_state = persisted_after_submit
        sent = _FakeClient.sent
        native_balances = _FakeClient.native_balances
        sequence_by_sender = dict(_FakeClient.sequence_by_sender)

    def restarted_sequence(self, sender_pubkey_hex: str) -> int:
        return int(type(self).sequence_by_sender.get(sender_pubkey_hex, 0))

    def restarted_sendtx(self, payload):
        raise AssertionError("replay should be rejected before sendtx after restart")

    monkeypatch.setattr(_RestartedFakeClient, "get_sequence", restarted_sequence)
    monkeypatch.setattr(_RestartedFakeClient, "sendtx", restarted_sendtx)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _RestartedFakeClient)

    status_code, replay = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )

    assert status_code == 400
    assert replay == {"ok": False, "error": "signed_tau_tx_payload sequence mismatch"}
    assert _RestartedFakeClient.sent == [external_payload]
    assert _RestartedFakeClient.app_state == persisted_after_submit


def test_submit_rejects_external_signed_tau_payload_operation_mismatch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    wrong_operations = json.loads(json.dumps(prepared["report"]["operations"]))
    wrong_operations["8"][0]["amount"] = 999
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=wrong_operations,
        fee_limit=2,
    )

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps({**body, "signed_tau_tx_payload": external_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload operations mismatch"}
    assert _FakeClient.sent == []


def test_submit_withdraw_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_posted_collateral(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "withdraw_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 100,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["action"] == "withdraw_collateral"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]


def test_prepare_publish_price_signs_oracle_op(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "publish_clearing_price",
        "market_id": MARKET_ID,
        "oracle_privkey": str(ORACLE_PRIVKEY),
        "price_e8": 100_000_000,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_sender_pubkey"] == ORACLE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_nonce"] == 1
    assert payload["report"]["operation"]["oracle_sig"].startswith("0x")


def test_submit_advance_epoch_uses_operator_signer(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "advance_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "delta": 1,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["action"] == "advance_epoch"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == OPERATOR[2:]


def test_prepare_settle_epoch_can_fail_closed_on_missing_oracle_bridge(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert payload["report"]["preflight"]["error"] == "settle_epoch requires oracle_adapter_bridge"


def test_oracle_bridge_template_preflights_required_settle_epoch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )

    assert status_code == 200
    assert bridge_payload["ok"] is True
    assert bridge_payload["fixture_kind"] == "local_o3_aggregate_adapter"
    assert bridge_payload["production_authority"] is False
    assert bridge_payload["verify_result"]["status"] == "accepted"
    assert bridge_payload["target"]["consumer_module"] == "zenodex.perps"
    assert bridge_payload["target"]["action_kind"] == "settle_epoch"

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_submit_settle_epoch_binds_ready_oracle_authority_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(), sort_keys=True),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )
    assert status_code == 200

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    exercise = payload["proof"]["oracle_authority_exercise"]
    assert exercise["schema"] == "zenodex/perps_wallet/oracle_authority_exercise/v1"
    assert exercise["authority_exercised"] is True
    assert exercise["production_authority"] is True
    assert exercise["status"] == "exercised"
    assert exercise["readiness_gaps"] == []
    assert exercise["authority_hash"] == _oracle_authority_profile()["authority_hash"]
    assert exercise["signature_quorum_accepted_weight"] == 2
    assert exercise["signature_quorum_threshold"] == 2
    assert exercise["oracle_adapter_bridge_id"] == bridge_payload["bridge"]["bridge_id"]
    assert str(exercise["oracle_adapter_bridge_hash"]).startswith("0x")
    receipt = payload["proof"]["intent_receipt"]
    assert receipt["body"]["oracle_authority_exercised"] is True
    assert receipt["body"]["oracle_authority_exercise_hash"] == exercise["exercise_hash"]
    assert receipt["oracle_authority_exercise"]["exercise_hash"] == exercise["exercise_hash"]


def test_submit_settle_epoch_requires_ready_oracle_authority_when_enabled(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY", "1")
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_JSON", raising=False)
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )
    assert status_code == 200

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert "production_oracle_authority_required" in payload["error"]
    assert "oracle production authority profile is missing" in payload["error"]
    assert _FakeClient.sent == []


def test_oracle_bridge_inspector_summarizes_verified_settle_bridge(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )
    assert status_code == 200

    status_code, inspection = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge/inspect",
        json.dumps({"oracle_adapter_bridge": bridge_payload["bridge"]}).encode("utf-8"),
    )

    assert status_code == 200
    assert inspection["ok"] is True
    assert inspection["status"] == "accepted"
    assert inspection["production_authority"] is False
    summary = inspection["summary"]
    assert summary["bridge_id"] == bridge_payload["bridge"]["bridge_id"]
    assert summary["consumer_module"] == "zenodex.perps"
    assert summary["action_kind"] == "settle_epoch"
    assert summary["query_id"] == bridge_payload["target"]["query_id"]
    assert summary["profile_id"] == bridge_payload["target"]["profile_id"]
    assert summary["required_evidence_floor"] == "O3"
    assert summary["value_e8"] == 100_000_000
    assert summary["report_count"] == 3


def test_oracle_bridge_inspector_rejects_tampered_action_id(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )
    assert status_code == 200
    tampered = json.loads(json.dumps(bridge_payload["bridge"]))
    tampered["action"]["action_id"] = "sha256:" + "0" * 64

    status_code, inspection = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge/inspect",
        json.dumps({"oracle_adapter_bridge": tampered}).encode("utf-8"),
    )

    assert status_code == 200
    assert inspection["ok"] is False
    assert inspection["status"] == "rejected"
    assert "adapter:adapter_action_id_mismatch" in inspection["verify_result"]["errors"]


def test_status_exposes_clearinghouse_liquidation_summary_fields(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_JSON", raising=False)
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    for name in (
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    proof_profile = payload["status"]["proof_profile"]
    assert proof_profile["profile_id"] == "perps_stream8_live_wallet_v0"
    assert proof_profile["zk_wrapper_required_for_production_claim"] is True
    assert proof_profile["promotion_ready"] is False
    assert "does_not_claim_perps_zk_execution" in proof_profile["non_claims"]
    wallet_authority = payload["status"]["wallet_authority"]
    assert payload["status"]["production_wallet_authority"] is False
    assert wallet_authority["status"] == "blocked"
    assert wallet_authority["readiness_gaps"] == ["perps wallet authority profile is missing"]
    oracle_authority = payload["status"]["oracle_authority"]
    assert payload["status"]["production_oracle_authority"] is False
    assert oracle_authority["status"] == "blocked"
    assert oracle_authority["readiness_gaps"] == ["oracle production authority profile is missing"]
    markets = payload["status"]["markets"]
    assert len(markets) == 1
    market = markets[0]
    assert market["market_id"] == MARKET_ID
    assert market["liquidated_this_step"] is True
    assert market["account_a_quote_balance"] == 900
    assert market["account_b_quote_balance"] == 900
    assert market["fee_pool_e8"] == 525_000_000
    assert market["position_base_a"] == 0
    assert market["position_base_b"] == 0
    assert market["net_deposited_e8"] == 20_000_000_000


def test_status_loads_ready_perps_wallet_authority_profile(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_wallet_authority"] is True
    wallet_authority = payload["status"]["wallet_authority"]
    assert wallet_authority["status"] == "ready"
    assert wallet_authority["readiness_gaps"] == []
    assert wallet_authority["key_ref_count"] == 2
    assert wallet_authority["recovery_policy_count"] == 2
    assert wallet_authority["recoverable_active_key_count"] == 2
    assert wallet_authority["active_signer_count"] == 2
    assert wallet_authority["transaction_scope"]["stream_key"] == "8"
    encoded = json.dumps(wallet_authority, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_status_loads_ready_perps_wallet_recovery_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_RECOVERY_EXERCISE_JSON",
        json.dumps(_perps_wallet_recovery_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_RECOVERY_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    recovery = payload["status"]["wallet_authority"]["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is True
    assert recovery["status"] == "ready"
    assert recovery["evaluation"]["accepted_weight"] == 2
    assert recovery["evaluation"]["delay_ok"] is True
    assert recovery["evaluation"]["threshold_ok"] is True
    assert recovery["guardian_signature_quorum"]["accepted_weight"] == 2
    assert recovery["guardian_signature_quorum"]["threshold"] == 2


def test_status_loads_ready_perps_wallet_rotation_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_ROTATION_EXERCISE_JSON",
        json.dumps(_perps_wallet_rotation_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_ROTATION_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    rotation = payload["status"]["wallet_authority"]["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is True
    assert rotation["status"] == "ready"
    assert rotation["rotated_key_id"] == "perps-wallet-a"
    assert rotation["replacement_key_id"] == "perps-wallet-c"
    assert rotation["broadcast_reference"] == "tau-tx:perps-wallet-rotation-1"
    assert rotation["guardian_signature_quorum"]["accepted_weight"] == 2
    assert rotation["guardian_signature_quorum"]["threshold"] == 2


def test_recovery_evaluate_endpoint_blocks_threshold_gap(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/recovery/evaluate",
        json.dumps(_perps_wallet_recovery_exercise(approvals=["guardian-oracle"])).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    recovery = payload["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is False
    assert "recovery_policy_not_satisfied" in recovery["errors"]


def test_recovery_evaluate_endpoint_blocks_bad_guardian_signature_quorum(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    exercise = _perps_wallet_recovery_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/recovery/evaluate",
        json.dumps(exercise).encode("utf-8"),
    )

    assert status_code == 200
    recovery = payload["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in recovery["errors"])


def test_rotation_evaluate_endpoint_blocks_bad_broadcast_epoch(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/rotation/evaluate",
        json.dumps(_perps_wallet_rotation_exercise(broadcast_at_epoch=9)).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    rotation = payload["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is False
    assert "perps wallet rotation exercise broadcast_at_epoch precedes request" in rotation["errors"]


def test_rotation_evaluate_endpoint_blocks_bad_guardian_signature_quorum(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    exercise = _perps_wallet_rotation_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/rotation/evaluate",
        json.dumps(exercise).encode("utf-8"),
    )

    assert status_code == 200
    rotation = payload["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in rotation["errors"])


def test_status_loads_ready_oracle_authority_profile(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(), sort_keys=True),
    )
    for name in (
        "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_oracle_authority"] is True
    oracle_authority = payload["status"]["oracle_authority"]
    assert oracle_authority["status"] == "ready"
    assert oracle_authority["readiness_gaps"] == []
    assert oracle_authority["active_signer_count"] == 2
    assert oracle_authority["threshold"] == 2
    assert oracle_authority["signature_count"] == 2
    assert oracle_authority["signature_quorum"]["accepted_weight"] == 2
    assert oracle_authority["proof_profile"]["runtime_proof_profile"] == "zenooracle-o3-replay-zk-profile-v1"
    encoded = json.dumps(oracle_authority, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_status_blocks_oracle_authority_profile_chain_mismatch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(chain_id="wrong-chain"), sort_keys=True),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_oracle_authority"] is False
    assert "oracle production authority profile chain_id mismatch" in payload["status"]["oracle_authority"]["readiness_gaps"]


def test_prepare_partial_liquidate_is_opt_in_for_isolated_markets(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("TAU_DEX_ALLOW_ISOLATED_PERPS", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 2500,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["preflight"]["ok"] is False
    assert "isolated perps disabled" in payload["report"]["preflight"]["error"]


def test_prepare_partial_liquidate_accepts_auto_fraction_zero(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 0


def test_oracle_bridge_template_preflights_required_partial_liquidate(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps(
            {
                "action": "partial_liquidate",
                "market_id": ISOLATED_MARKET_ID,
                "account_pubkey": ALICE,
                "fraction_bps": 0,
            }
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert bridge_payload["ok"] is True
    assert bridge_payload["action"] == "partial_liquidate"
    assert bridge_payload["target"]["action_kind"] == "liquidate_account"
    assert bridge_payload["target"]["wallet_action"] == "partial_liquidate"
    assert bridge_payload["verify_result"]["status"] == "accepted"

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_submit_partial_liquidate_builds_account_bound_stream_8_tx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "fraction_bps": 5000,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 5000
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    wire_ops = json.loads(payload["report"]["tau_tx_payload"]["operations"]["8"])
    assert wire_ops[0]["action"] == "partial_liquidate"
    assert wire_ops[0]["account_pubkey"] == ALICE
    assert wire_ops[0]["fraction_bps"] == 5000
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"


def test_submit_rejects_preflight_failure_before_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": "0x" + "00" * 96,
        "sig_b": "0x" + "00" * 96,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"].startswith("preflight_failed:")
    assert _FakeClient.sent == []
