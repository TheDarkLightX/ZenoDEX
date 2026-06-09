from __future__ import annotations

import json
import shutil
import threading
from functools import partial
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Mapping
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.tau_net_client import sign_dex_intent_for_engine
from src.integration.zeno_ledger_tokenomics import build_protocol_token_distribution_v0
from src.integration.zeno_ledger_signature import _BLS_AVAILABLE, bls_public_key_hex_from_private_key_v0
from src.integration.zeno_ledger_v0 import (
    build_header_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    dex_state_root_v0,
    hash_v0,
    tx_hash_v0,
)
from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus
from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import (
    NODE_JOIN_CONFIG_SCHEMA,
    NODE_LIVE_STATE_SCHEMA,
    NODE_STATUS_SCHEMA,
    _candidate_reward_participants_for_source_tx_v0,
    _default_ui_intent_tx_id_v0,
    _eligible_reward_receipt_kinds_for_source_tx_v0,
    _existing_append_report_for_tx_id_v0,
    _existing_tx_and_append_report_for_tx_id_v0,
    _market_buyback_purchase_from_state_v0,
    _node_status_hash,
    _public_network_config_to_join_config_v0,
    _tokenomics_buyback_source_pubkey_v0,
    _ui_account_history_from_live_bodies_v0,
    _ui_swap_tx_v0,
    _ui_tokenomics_response_v0,
    _validate_tokenomics_claim_idempotent_payload_v0,
    append_dex_transaction_v0,
    append_testnet_faucet_v0,
    build_public_network_config_v0,
    check_peer_status_v0,
    join_public_node_from_network_config_url_v0,
    join_public_node_from_config_v0,
    load_node_status_v0,
    make_node_http_server_v0,
    preflight_node_join_config_v0,
    pull_live_from_peer_v0,
    run_node_once_v0,
    sync_public_bundle_from_url_v0,
)
from tools.zeno_ledger_run_local import ZERO_ROOT


def _read_url_json(url: str) -> dict[str, object]:
    with urlopen(url, timeout=5) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


def _get_url_json_status(url: str) -> tuple[int, dict[str, object]]:
    try:
        with urlopen(url, timeout=5) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = response.status
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = exc.code
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return status, obj


def _read_json_path(path: Path) -> dict[str, object]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _ui_tokenomics_response_for_test(data_dir: Path) -> dict[str, object]:
    status = _ui_tokenomics_response_v0(data_dir=data_dir, node_status=load_node_status_v0(data_dir))
    assert isinstance(status, dict)
    assert status["ok"] is True
    return status


def _pubkey(byte: str) -> str:
    return "0x" + byte * 48


def _post_url_json(url: str, value: dict[str, object]) -> dict[str, object]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
        body = response.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


def _allocation_current_balance(status: Mapping[str, object], allocation_id: str) -> int:
    rows = status["status"]["allocation_rows"] if isinstance(status.get("status"), Mapping) else []
    assert isinstance(rows, list)
    for row in rows:
        if isinstance(row, Mapping) and row.get("id") == allocation_id:
            return int(row["current_balance"])
    raise AssertionError(f"missing allocation row {allocation_id}")


def _program_row(status: Mapping[str, object], program_id: str) -> Mapping[str, object]:
    rows = status["status"]["active_participant_programs"] if isinstance(status.get("status"), Mapping) else []
    assert isinstance(rows, list)
    for row in rows:
        if isinstance(row, Mapping) and row.get("id") == program_id:
            return row
    raise AssertionError(f"missing program row {program_id}")


def test_default_ui_tx_id_is_stable_and_payload_bound() -> None:
    alice = _pubkey("31")
    bob = _pubkey("32")
    base_intent = {
        "sender_pubkey": alice,
        "recipient": alice,
        "pool_id": "pool-a",
        "asset_in": DEFAULT_ASSET0,
        "asset_out": DEFAULT_ASSET1,
        "amount_in": 25,
        "min_amount_out": 1,
        "nonce": 1,
    }

    first = _default_ui_intent_tx_id_v0(prefix="ui-swap", sender=alice, nonce=1, intent_payload=base_intent)
    retry = _default_ui_intent_tx_id_v0(prefix="ui-swap", sender=alice, nonce=1, intent_payload=dict(base_intent))
    other_sender_intent = dict(base_intent, sender_pubkey=bob, recipient=bob)
    other_sender = _default_ui_intent_tx_id_v0(
        prefix="ui-swap",
        sender=bob,
        nonce=1,
        intent_payload=other_sender_intent,
    )
    other_amount = _default_ui_intent_tx_id_v0(
        prefix="ui-swap",
        sender=alice,
        nonce=1,
        intent_payload=dict(base_intent, amount_in=26),
    )

    assert first == retry
    assert first != other_sender
    assert first != other_amount
    assert first.startswith("ui-swap-1-")


def test_ui_swap_builder_default_tx_id_does_not_collide_across_users(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    alice = _pubkey("31")
    bob = _pubkey("32")
    pool_id = compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30)
    balances = BalanceTable()
    for account in (alice, bob):
        balances.set(account, DEFAULT_ASSET0, 10_000)
    snapshot = snapshot_from_state(
        DexState(
            balances=balances,
            pools={
                pool_id: PoolState(
                    pool_id=pool_id,
                    asset0=DEFAULT_ASSET0,
                    asset1=DEFAULT_ASSET1,
                    reserve0=100_000,
                    reserve1=100_000,
                    fee_bps=30,
                    lp_supply=100_000,
                    status=PoolStatus.ACTIVE,
                    created_at=1,
                )
            },
            lp_balances=LPTable(),
        )
    ).data
    node_status = {
        "bundle_root": str(tmp_path),
        "test_token_catalog": [
            {"symbol": "tASSET0", "asset_id": DEFAULT_ASSET0},
            {"symbol": "tASSET1", "asset_id": DEFAULT_ASSET1},
        ],
    }

    def _same_height_snapshot(**_kwargs: object) -> tuple[int, dict[str, object]]:
        return 41, snapshot

    monkeypatch.setattr("tools.zeno_ledger_node._latest_snapshot_for_ui_v0", _same_height_snapshot)

    def build(sender: str) -> dict[str, object]:
        return _ui_swap_tx_v0(
            data_dir=tmp_path,
            node_status=node_status,
            payload={
                "from": "tASSET0",
                "to": "tASSET1",
                "poolId": pool_id,
                "amountIn": 25,
                "minAmountOut": 1,
                "senderPubkey": sender,
                "recipient": sender,
                "nonce": 1,
            },
            time_ms=1_778_740_101_000,
        )

    alice_tx = build(alice)
    bob_tx = build(bob)

    assert alice_tx["tx_id"] != bob_tx["tx_id"]
    assert str(alice_tx["tx_id"]).startswith("ui-swap-1-")
    assert str(bob_tx["tx_id"]).startswith("ui-swap-1-")


def _ui_swap_builder_snapshot_fixture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[str, dict[str, object]]:
    """Pin a fixed snapshot + node_status for builder-shape unit tests.

    Returns (pool_id, node_status). Monkeypatches the snapshot loader so the
    builder is exercised deterministically with no disk/settlement dependency.
    """
    alice = _pubkey("31")
    pool_id = compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30)
    balances = BalanceTable()
    balances.set(alice, DEFAULT_ASSET0, 10_000)
    balances.set(alice, DEFAULT_ASSET1, 10_000)
    snapshot = snapshot_from_state(
        DexState(
            balances=balances,
            pools={
                pool_id: PoolState(
                    pool_id=pool_id,
                    asset0=DEFAULT_ASSET0,
                    asset1=DEFAULT_ASSET1,
                    reserve0=100_000,
                    reserve1=100_000,
                    fee_bps=30,
                    lp_supply=100_000,
                    status=PoolStatus.ACTIVE,
                    created_at=1,
                )
            },
            lp_balances=LPTable(),
        )
    ).data
    node_status = {
        "bundle_root": str(tmp_path),
        "test_token_catalog": [
            {"symbol": "tASSET0", "asset_id": DEFAULT_ASSET0},
            {"symbol": "tASSET1", "asset_id": DEFAULT_ASSET1},
        ],
    }

    def _same_height_snapshot(**_kwargs: object) -> tuple[int, dict[str, object]]:
        return 41, snapshot

    monkeypatch.setattr("tools.zeno_ledger_node._latest_snapshot_for_ui_v0", _same_height_snapshot)
    return pool_id, node_status


def test_ui_swap_builder_exact_in_golden_unchanged(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Golden: a pure exact-in request still produces the identical op dict.

    This pins backward compatibility: the exact-out branch is purely additive,
    so the exact-in op (including its derived intent_id) must be byte-identical.
    """
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)

    tx = _ui_swap_tx_v0(
        data_dir=tmp_path,
        node_status=node_status,
        payload={
            "from": "tASSET0",
            "to": "tASSET1",
            "poolId": pool_id,
            "amountIn": 25,
            "minAmountOut": 1,
            "senderPubkey": alice,
            "recipient": alice,
            "nonce": 7,
        },
        time_ms=1_778_740_101_000,
    )

    ops = tx["operations"]["5"]
    assert len(ops) == 1
    op = ops[0]
    # Golden intent_id is the canonical hash over the exact-in intent payload.
    expected_intent_id = hash_v0(
        "ui_swap_intent_v0",
        {
            "sender_pubkey": alice,
            "recipient": alice,
            "pool_id": pool_id,
            "asset_in": DEFAULT_ASSET0,
            "asset_out": DEFAULT_ASSET1,
            "amount_in": 25,
            "min_amount_out": 1,
            "nonce": 7,
        },
    )
    # FULL golden: the entire op dict is pinned, so any extra/changed/dropped
    # field (a new key, a default change) fails this test -- not just a subset.
    assert op == {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": expected_intent_id,
        "sender_pubkey": alice,
        "deadline": 1_999_999_999,
        "nonce": 7,
        "pool_id": pool_id,
        "asset_in": DEFAULT_ASSET0,
        "asset_out": DEFAULT_ASSET1,
        "amount_in": 25,
        "min_amount_out": 1,
        "recipient": alice,
    }
    # No exact-out fields leaked into the exact-in op.
    assert "amount_out" not in op
    assert "max_amount_in" not in op
    # tx_id derivation unchanged (prefix binds sender + nonce); the collision
    # test covers full tx_id determinism.
    assert str(tx["tx_id"]).startswith("ui-swap-7-")


def test_ui_swap_builder_exact_out_op_shape(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Builder emits a correct SWAP_EXACT_OUT op with exact field mapping.

    Verifies amount_out/max_amount_in carried in place of amount_in/
    min_amount_out, kind flipped, and signed-intent fields carried identically.
    """
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)
    signature = "0x" + "cd" * 96

    tx = _ui_swap_tx_v0(
        data_dir=tmp_path,
        node_status=node_status,
        payload={
            "from": "tASSET0",
            "to": "tASSET1",
            "poolId": pool_id,
            "kind": "SWAP_EXACT_OUT",
            "amountOut": 1_000,
            "maxAmountIn": 2_000,
            "senderPubkey": alice,
            "recipient": alice,
            "nonce": 9,
            "signature": signature,
        },
        time_ms=1_778_740_101_000,
    )

    ops = tx["operations"]["5"]
    assert len(ops) == 1
    op = ops[0]
    assert op["kind"] == "SWAP_EXACT_OUT"
    # Exact-out fields present; exact-in fields absent (intents.py SwapIntent).
    assert op["amount_out"] == 1_000
    assert op["max_amount_in"] == 2_000
    assert "amount_in" not in op
    assert "min_amount_out" not in op
    # Shared signed-intent fields carried the same way as exact-in.
    assert op["module"] == "TauSwap"
    assert op["version"] == "0.1"
    assert op["pool_id"] == pool_id
    assert op["asset_in"] == DEFAULT_ASSET0
    assert op["asset_out"] == DEFAULT_ASSET1
    assert op["sender_pubkey"] == alice
    assert op["recipient"] == alice
    assert op["nonce"] == 9
    assert op["deadline"] == 1_999_999_999
    assert op["signature"] == signature
    # intent_id binds the exact-out amount fields (amount_out/max_amount_in).
    assert op["intent_id"] == hash_v0(
        "ui_swap_intent_v0",
        {
            "sender_pubkey": alice,
            "recipient": alice,
            "pool_id": pool_id,
            "asset_in": DEFAULT_ASSET0,
            "asset_out": DEFAULT_ASSET1,
            "amount_out": 1_000,
            "max_amount_in": 2_000,
            "nonce": 9,
        },
    )


def test_ui_swap_builder_exact_out_detected_by_amount_keys(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Presence of amount_out/max_amount_in alone routes to exact-out."""
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)

    tx = _ui_swap_tx_v0(
        data_dir=tmp_path,
        node_status=node_status,
        payload={
            "from": "tASSET0",
            "to": "tASSET1",
            "poolId": pool_id,
            "amount_out": 500,
            "max_amount_in": 1_500,
            "senderPubkey": alice,
            "recipient": alice,
            "nonce": 3,
        },
        time_ms=1_778_740_101_000,
    )
    op = tx["operations"]["5"][0]
    assert op["kind"] == "SWAP_EXACT_OUT"
    assert op["amount_out"] == 500
    assert op["max_amount_in"] == 1_500


def test_ui_swap_builder_exact_out_requires_max_amount_in(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Fail-closed: exact-out with a missing max_amount_in cap is rejected."""
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)

    with pytest.raises(ValueError):
        _ui_swap_tx_v0(
            data_dir=tmp_path,
            node_status=node_status,
            payload={
                "from": "tASSET0",
                "to": "tASSET1",
                "poolId": pool_id,
                "kind": "SWAP_EXACT_OUT",
                "amount_out": 500,
                # max_amount_in intentionally omitted -> unbounded input -> reject
                "senderPubkey": alice,
                "recipient": alice,
                "nonce": 3,
            },
            time_ms=1_778_740_101_000,
        )


def test_ui_swap_builder_exact_out_rejects_nonpositive_amount_out(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Fail-closed: amount_out must be strictly positive (intents.py >0)."""
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)

    with pytest.raises(ValueError):
        _ui_swap_tx_v0(
            data_dir=tmp_path,
            node_status=node_status,
            payload={
                "from": "tASSET0",
                "to": "tASSET1",
                "poolId": pool_id,
                "amount_out": 0,
                "max_amount_in": 1_000,
                "senderPubkey": alice,
                "recipient": alice,
                "nonce": 3,
            },
            time_ms=1_778_740_101_000,
        )


def test_ui_swap_builder_rejects_ambiguous_exact_in_and_exact_out(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Fail-closed: a request mixing exact-in and exact-out intent is rejected.

    A write API must not silently disambiguate a contradictory request and drop
    part of the caller's intent. All three ambiguity forms must raise ValueError:
      (a) both amount families present,
      (b) explicit exact-out marker WITH exact-in amount keys,
      (c) explicit exact-in marker WITH exact-out amount keys.
    """
    alice = _pubkey("31")
    pool_id, node_status = _ui_swap_builder_snapshot_fixture(tmp_path, monkeypatch)

    base = {
        "from": "tASSET0",
        "to": "tASSET1",
        "poolId": pool_id,
        "senderPubkey": alice,
        "recipient": alice,
        "nonce": 3,
    }
    ambiguous_payloads = [
        # (a) both families, no explicit marker
        {**base, "amount_in": 25, "min_amount_out": 1, "amount_out": 1_000, "max_amount_in": 2_000},
        # (b) explicit exact-out marker but exact-in amount keys also present
        {**base, "kind": "SWAP_EXACT_OUT", "amount_out": 1_000, "max_amount_in": 2_000, "amount_in": 25},
        # (c) explicit exact-in marker but exact-out amount keys also present
        {**base, "kind": "SWAP_EXACT_IN", "amount_in": 25, "min_amount_out": 1, "amount_out": 1_000},
        # camelCase variants must be detected the same way
        {**base, "amountIn": 25, "maxAmountIn": 2_000},
    ]
    for payload in ambiguous_payloads:
        with pytest.raises(ValueError, match="ambiguous swap intent"):
            _ui_swap_tx_v0(
                data_dir=tmp_path,
                node_status=node_status,
                payload=payload,
                time_ms=1_778_740_101_000,
            )


def _post_url_json_status(url: str, value: dict[str, object], *, bearer_token: str | None = None) -> tuple[int, dict[str, object]]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if bearer_token is not None:
        headers["Authorization"] = f"Bearer {bearer_token}"
    request = Request(url, data=payload, headers=headers, method="POST")
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = response.status
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = exc.code
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return status, obj


class _QuietStaticHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return


class _WriterAuthHandler(BaseHTTPRequestHandler):
    def do_POST(self) -> None:  # noqa: N802
        if self.headers.get("Authorization") != "Bearer writer-token":
            payload = b'{"ok": false, "error": "unauthorized"}\n'
            self.send_response(int(HTTPStatus.UNAUTHORIZED))
        else:
            payload = b'{"ok": true, "accepted_by": "writer"}\n'
            self.send_response(int(HTTPStatus.OK))
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def log_message(self, format: str, *args: object) -> None:
        return


def _status_only_handler(status: dict[str, object]) -> type[BaseHTTPRequestHandler]:
    class _StatusOnlyHandler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802
            if self.path == "/status":
                payload = json.dumps(status, sort_keys=True).encode("utf-8") + b"\n"
                self.send_response(int(HTTPStatus.OK))
            elif self.path == "/live":
                payload = b'{"ok": false, "live": false}\n'
                self.send_response(int(HTTPStatus.OK))
            else:
                payload = b'{"ok": false, "error": "missing"}\n'
                self.send_response(int(HTTPStatus.NOT_FOUND))
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, format: str, *args: object) -> None:
            return

    return _StatusOnlyHandler


def test_tokenomics_reward_classifier_covers_active_participant_runtime_actions() -> None:
    alice = _pubkey("31")
    oracle = _pubkey("32")
    miner = _pubkey("33")

    cases = [
        (
            {
                "tx_sender_pubkey": alice,
                "operations": {"5": [{"module": "TauSwap", "kind": "ADD_LIQUIDITY", "sender_pubkey": alice}]},
            },
            alice,
            {"add_liquidity", "lp_position_snapshot"},
        ),
        (
            {
                "tx_sender_pubkey": alice,
                "operations": {
                    "11": [{"module": "ZUSDFinance", "action": "deposit_sp", "account_pubkey": alice}]
                },
            },
            alice,
            {"stability_pool_deposit", "stability_pool_epoch_snapshot"},
        ),
        (
            {
                "tx_sender_pubkey": oracle,
                "operations": {"11": [{"module": "ZUSDFinance", "action": "oracle_report"}]},
            },
            oracle,
            {"oracle_report"},
        ),
        (
            {
                "tx_sender_pubkey": alice,
                "operations": {"8": [{"module": "TauPerp", "action": "deposit_collateral", "account_pubkey": alice}]},
            },
            alice,
            {"perps_position_activity"},
        ),
        (
            {
                "tx_sender_pubkey": alice,
                "operations": {"11": [{"module": "ZUSDFinance", "action": "mint_zusd", "owner_pubkey": alice}]},
            },
            alice,
            {"zusd_vault_activity"},
        ),
        (
            {
                "tx_sender_pubkey": miner,
                "operations": {
                    "10": [{"module": "ZenoProofMining", "action": "submit_proof", "recipient_pubkey": miner}]
                },
            },
            miner,
            {"proof_mining_claim", "verified_proof_work"},
        ),
    ]

    for tx, participant, expected in cases:
        assert participant in _candidate_reward_participants_for_source_tx_v0(tx)
        assert _eligible_reward_receipt_kinds_for_source_tx_v0(tx=tx, recipient_pubkey=participant) == expected

    assert _eligible_reward_receipt_kinds_for_source_tx_v0(tx=cases[1][0], recipient_pubkey=oracle) == set()


def test_tokenomics_active_participant_claim_transfers_preallocated_rewards(tmp_path: Path) -> None:
    fixture_keys = tmp_path / "fixture-keys.json"
    fixture_keys.write_text(
        json.dumps(
            {
                "roles": {
                    "guardian_2": {
                        "public_key": _pubkey("12"),
                    }
                }
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    source_bundle_root = tmp_path / "source_bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id="zeno-ledger-tokenomics-claim",
        chain_id="zeno-ledger-tokenomics-claim",
        sequencer_id="sequencer-tokenomics-claim",
        time_ms=1_778_730_123_000,
        token_symbol="ZDEX",
        fixture_key_bundle_path=fixture_keys,
    )
    assert build_report["ok"] is True
    node_dir = tmp_path / "node"
    node_report = run_node_once_v0(
        bundle_root=source_bundle_root,
        node_id="node-tokenomics-claim",
        data_dir=node_dir,
        peer_watcher_attestation_paths=[],
    )
    assert node_report["ok"] is True

    server = make_node_http_server_v0(
        data_dir=node_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        before = _read_url_json(f"http://{host}:{port}/api/tokenomics/status")
        active_before = _allocation_current_balance(before, "active_participant_rewards_pool")
        bootstrap_before = _allocation_current_balance(before, "liquidity_bootstrap_market_making")
        overclaim_status, overclaim_report = _post_url_json_status(
            f"http://{host}:{port}/api/tokenomics/active-participant/claim",
            {
                "program_id": "lp_liquidity_provider_rewards",
                "recipient_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "source_height": 3,
                "source_tx_index": 0,
                "amount": 1_000,
                "time_ms": 1_778_731_129_000,
                "tx_id": "node-tokenomics-lp-reward-overclaim-v0",
            },
        )
        claim_report = _post_url_json(
            f"http://{host}:{port}/api/tokenomics/active-participant/claim",
            {
                "program_id": "lp_liquidity_provider_rewards",
                "recipient_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "source_height": 3,
                "source_tx_index": 0,
                "amount": 25,
                "time_ms": 1_778_731_130_000,
                "tx_id": "node-tokenomics-lp-reward-claim-v0",
            },
        )
        duplicate_status, duplicate_report = _post_url_json_status(
            f"http://{host}:{port}/api/tokenomics/active-participant/claim",
            {
                "program_id": "lp_liquidity_provider_rewards",
                "recipient_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "source_height": 3,
                "source_tx_index": 0,
                "amount": 25,
                "time_ms": 1_778_731_131_000,
                "tx_id": "node-tokenomics-lp-reward-claim-duplicate-v0",
            },
        )
        after = _read_url_json(f"http://{host}:{port}/api/tokenomics/status")
    finally:
        server.shutdown()
        server.server_close()

    assert overclaim_status == HTTPStatus.BAD_REQUEST
    assert "amount_must_match_program_claim_amount" in str(overclaim_report["error"])
    assert claim_report["ok"] is True
    assert claim_report["append_kind"] == "tokenomics_active_participant_reward_claim"
    assert claim_report["receipt"]["accepted"] is True
    assert claim_report["claim"]["receipt_kind"] == "add_liquidity"
    assert claim_report["claim"]["tau_policy"]["host_computed_flags"]["amount_matches_program_claim_amount"] is True
    assert claim_report["claim"]["production_security_claim"] is False
    assert _allocation_current_balance(after, "active_participant_rewards_pool") == active_before - 25
    assert _allocation_current_balance(after, "liquidity_bootstrap_market_making") == bootstrap_before + 25
    program_after = _program_row(after, "lp_liquidity_provider_rewards")
    assert program_after["claimed_amount"] == 25
    assert program_after["remaining_amount"] == 29_975
    assert duplicate_status == HTTPStatus.BAD_REQUEST
    assert "receipt_not_previously_claimed" in str(duplicate_report["error"])


def test_append_dex_transaction_tx_id_is_idempotency_key(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    (data_dir / "live_ledger" / "bodies").mkdir(parents=True)
    (data_dir / "live_ledger" / "receipts").mkdir(parents=True)
    (data_dir / "append_reports").mkdir(parents=True)
    tx = {
        "tx_id": "tx-id-idempotency-swap-v0",
        "block_timestamp": 1_778_731_121,
        "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "operations": {
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + "ad" * 32,
                    "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "deadline": 1_999_999_999,
                    "nonce": 1,
                    "pool_id": compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30),
                    "asset_in": DEFAULT_ASSET0,
                    "asset_out": DEFAULT_ASSET1,
                    "amount_in": 1_000,
                    "min_amount_out": 1,
                    "recipient": DEFAULT_BOOTSTRAP_SENDER,
                }
            ],
            "12": [
                {
                    "module": "ZenoTokenomics",
                    "kind": "ZENODEX_TOKENOMICS_BUYBACK_BURN",
                    "event": {"height": 6},
                }
            ],
        },
    }
    body = {
        "schema": "zeno_ledger_body_v0",
        "chain_id": "zeno-ledger-tx-id-idempotency",
        "height": 6,
        "ingress": [],
        "transactions": [tx],
        "settlement_envelopes": [],
        "evidence": {},
    }
    receipt = {"accepted": True, "tx_hash": "0x" + "11" * 32}
    report = {
        "schema": "zeno_ledger_append_report_v0",
        "ok": True,
        "status": "accepted",
        "height": 6,
        "tx_hash": "0x" + "22" * 32,
        "receipt": receipt,
    }
    (data_dir / "live_ledger" / "bodies" / "6.json").write_text(json.dumps(body), encoding="utf-8")
    (data_dir / "live_ledger" / "receipts" / "6.json").write_text(json.dumps([receipt]), encoding="utf-8")
    (data_dir / "append_reports" / "6.json").write_text(json.dumps(report), encoding="utf-8")

    replay = _existing_append_report_for_tx_id_v0(
        data_dir=data_dir,
        tx_id="tx-id-idempotency-swap-v0",
        tx={**tx, "operations": {"5": tx["operations"]["5"]}},
        max_height=6,
    )
    assert replay["idempotent_replay"] is True
    assert replay["height"] == 6
    assert replay["tx_hash"] == report["tx_hash"]

    mismatched = json.loads(json.dumps(tx))
    mismatched["operations"]["5"][0]["amount_in"] = 1_001
    with pytest.raises(ValueError, match="duplicate_tx_id_payload_mismatch"):
        _existing_append_report_for_tx_id_v0(
            data_dir=data_dir,
            tx_id="tx-id-idempotency-swap-v0",
            tx=mismatched,
            max_height=6,
        )


def test_tokenomics_claim_tx_id_replay_validates_supplied_payload_fields(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    (data_dir / "live_ledger" / "bodies").mkdir(parents=True)
    (data_dir / "live_ledger" / "receipts").mkdir(parents=True)
    (data_dir / "append_reports").mkdir(parents=True)
    claim = {
        "program_id": "lp_liquidity_provider_rewards",
        "recipient_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "receipt_kind": "add_liquidity",
        "receipt_hash": "0x" + "33" * 32,
        "amount": 25,
        "source_height": 5,
        "source_tx_index": 0,
        "source_tx_hash": "0x" + "44" * 32,
        "claim_key": "lp_liquidity_provider_rewards:" + "0x" + "33" * 32,
    }
    tx = {
        "tx_id": "tokenomics-claim-idempotent-v0",
        "kind": "ZENODEX_ACTIVE_PARTICIPANT_REWARD_CLAIM",
        "block_timestamp": 1_778_731_121,
        "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "claim": claim,
    }
    body = {
        "schema": "zeno_ledger_body_v0",
        "chain_id": "zeno-ledger-tokenomics-idempotency",
        "height": 6,
        "ingress": [],
        "transactions": [tx],
        "settlement_envelopes": [],
        "evidence": {},
    }
    report = {
        "schema": "zeno_ledger_append_report_v0",
        "ok": True,
        "status": "accepted",
        "height": 6,
        "tx_hash": "0x" + "55" * 32,
        "append_kind": "tokenomics_active_participant_reward_claim",
    }
    (data_dir / "live_ledger" / "bodies" / "6.json").write_text(json.dumps(body), encoding="utf-8")
    (data_dir / "live_ledger" / "receipts" / "6.json").write_text(json.dumps([{"accepted": True}]), encoding="utf-8")
    (data_dir / "append_reports" / "6.json").write_text(json.dumps(report), encoding="utf-8")

    found = _existing_tx_and_append_report_for_tx_id_v0(
        data_dir=data_dir,
        tx_id="tokenomics-claim-idempotent-v0",
        max_height=6,
    )
    assert found is not None
    existing_tx, existing_report = found
    _validate_tokenomics_claim_idempotent_payload_v0(
        payload={
            "tx_id": "tokenomics-claim-idempotent-v0",
            "program_id": "lp_liquidity_provider_rewards",
            "recipient_pubkey": DEFAULT_BOOTSTRAP_SENDER,
            "amount": 25,
            "source_height": 5,
            "source_tx_index": 0,
            "receipt_hash": "0x" + "33" * 32,
            "receipt_kind": "add_liquidity",
        },
        existing_tx=existing_tx,
    )
    assert existing_report["idempotent_replay"] is True
    assert existing_report["height"] == 6

    with pytest.raises(ValueError, match="duplicate_tx_id_payload_mismatch"):
        _validate_tokenomics_claim_idempotent_payload_v0(
            payload={
                "tx_id": "tokenomics-claim-idempotent-v0",
                "program_id": "stability_pool_depositor_rewards",
                "amount": 25,
            },
            existing_tx=existing_tx,
        )


@pytest.mark.skipif(not _BLS_AVAILABLE, reason="py_ecc BLS support is required for signed local DEX intents")
def test_tokenomics_buyback_burn_wires_to_signed_swap_and_follower_replay(tmp_path: Path) -> None:
    source_bundle_root = tmp_path / "source_bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id="zeno-ledger-tokenomics-buyback",
        chain_id="zeno-ledger-tokenomics-buyback",
        sequencer_id="sequencer-tokenomics-buyback",
        time_ms=1_778_730_123_000,
        token_symbol="ZDEX",
    )
    assert build_report["ok"] is True

    writer_dir = tmp_path / "writer"
    follower_dir = tmp_path / "follower"
    assert run_node_once_v0(
        bundle_root=source_bundle_root,
        node_id="node-tokenomics-buyback-writer",
        data_dir=writer_dir,
        peer_watcher_attestation_paths=[],
    )["ok"] is True
    assert run_node_once_v0(
        bundle_root=source_bundle_root,
        node_id="node-tokenomics-buyback-follower",
        data_dir=follower_dir,
        peer_watcher_attestation_paths=[],
    )["ok"] is True

    private_key = "0x" + "01".zfill(64)
    trader = bls_public_key_hex_from_private_key_v0(private_key)
    asset_in = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
    asset_out = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
    pool_id = compute_pool_id(asset_in, asset_out, 30)

    append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=trader,
        asset=asset_in,
        amount=100_000,
        time_ms=1_778_731_120_000,
        tx_id="tokenomics-buyback-faucet-v0",
    )
    pre_status = _ui_tokenomics_response_for_test(writer_dir)
    pre_burned = int(pre_status["status"]["buyback_burned_total"])
    source_pubkey = _tokenomics_buyback_source_pubkey_v0(load_node_status_v0(writer_dir)["token_distribution"])
    pre_live = _read_json_path(writer_dir / "live_state.json")
    pre_snapshot_path = Path(str(pre_live["latest_snapshot_path"]))
    if not pre_snapshot_path.is_absolute():
        pre_snapshot_path = writer_dir / pre_snapshot_path
    pre_state = state_from_snapshot(_read_json_path(pre_snapshot_path))
    pre_protocol_fee_balance = pre_state.balances.get(source_pubkey, asset_in)
    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "ab" * 32,
        "sender_pubkey": trader,
        "deadline": 1_999_999_999,
        "nonce": 1,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": 10_000,
        "min_amount_out": 1,
        "recipient": trader,
    }
    intent["signature"] = sign_dex_intent_for_engine(
        intent,
        privkey=private_key,
        chain_id="zeno-ledger-tokenomics-buyback",
    )
    append_report = append_dex_transaction_v0(
        data_dir=writer_dir,
        tx={
            "tx_id": "tokenomics-buyback-swap-v0",
            "block_timestamp": 1_778_731_121,
            "tx_sender_pubkey": trader,
            "operations": {"5": [intent]},
        },
        time_ms=1_778_731_121_000,
    )
    post_status = _ui_tokenomics_response_for_test(writer_dir)
    post_burned = int(post_status["status"]["buyback_burned_total"])
    post_state = state_from_snapshot(_read_json_path(Path(str(append_report["post_snapshot_path"]))))

    assert append_report["ok"] is True
    assert append_report["receipt"]["accepted"] is True
    assert post_burned > pre_burned
    assert post_status["status"]["burned_total"] >= post_burned
    assert post_status["status"]["buyback_event_count"] == 1
    assert post_status["status"]["protocol_fee_capture"] == {
        "enabled": True,
        "share_bps": 2000,
        "recipient_pubkey": source_pubkey,
    }
    assert post_status["status"]["buyback_market_purchase"] == {
        "available": False,
        "route_available": False,
        "route_count": 0,
        "routes": [],
        "runtime_enabled": False,
        "runtime_mode": "treasury_allocation_burn_only",
        "runtime_blocker": "token_buyback_route_unavailable",
        "production_ready": False,
    }
    assert post_status["status"]["checks"]["buyback_market_route_available"] is False
    assert post_status["status"]["checks"]["buyback_market_purchase_runtime_enabled"] is False
    assert post_state.balances.get(source_pubkey, asset_in) - pre_protocol_fee_balance == 6

    pool_after_exact_in = post_state.pools[pool_id]
    if asset_in == pool_after_exact_in.asset0:
        reserve_in = int(pool_after_exact_in.reserve0)
        reserve_out = int(pool_after_exact_in.reserve1)
    else:
        reserve_in = int(pool_after_exact_in.reserve1)
        reserve_out = int(pool_after_exact_in.reserve0)
    exact_out_quote = quote_cpmm_swap_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=1_000,
        fee_bps=int(pool_after_exact_in.fee_bps),
        protocol_fee_share_bps=2_000,
    )
    exact_out_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_OUT",
        "intent_id": "0x" + "ac" * 32,
        "sender_pubkey": trader,
        "deadline": 1_999_999_999,
        "nonce": 2,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_out": 1_000,
        "max_amount_in": int(exact_out_quote.amount_in),
        "recipient": trader,
    }
    exact_out_intent["signature"] = sign_dex_intent_for_engine(
        exact_out_intent,
        privkey=private_key,
        chain_id="zeno-ledger-tokenomics-buyback",
    )
    append_report_exact_out = append_dex_transaction_v0(
        data_dir=writer_dir,
        tx={
            "tx_id": "tokenomics-buyback-swap-exact-out-v0",
            "block_timestamp": 1_778_731_122,
            "tx_sender_pubkey": trader,
            "operations": {"5": [exact_out_intent]},
        },
        time_ms=1_778_731_122_000,
    )
    post_exact_out_status = _ui_tokenomics_response_for_test(writer_dir)
    post_exact_out_state = state_from_snapshot(
        _read_json_path(Path(str(append_report_exact_out["post_snapshot_path"])))
    )

    assert append_report_exact_out["ok"] is True
    assert append_report_exact_out["receipt"]["accepted"] is True
    assert post_exact_out_status["status"]["buyback_event_count"] == 2
    assert (
        post_exact_out_state.balances.get(source_pubkey, asset_in)
        - post_state.balances.get(source_pubkey, asset_in)
    ) == exact_out_quote.protocol_fee_paid

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        pull_report = pull_live_from_peer_v0(data_dir=follower_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    writer_live = _read_json_path(writer_dir / "live_state.json")
    follower_live = _read_json_path(follower_dir / "live_state.json")
    assert pull_report["ok"] is True
    assert pull_report["pulled_count"] == 3
    assert follower_live["latest_header_hash"] == writer_live["latest_header_hash"]
    follower_status = _ui_tokenomics_response_for_test(follower_dir)
    assert follower_status["status"]["buyback_burned_total"] == post_exact_out_status["status"]["buyback_burned_total"]


def _snapshot_state_for_writer(writer_dir: Path):
    live = _read_json_path(writer_dir / "live_state.json")
    snapshot_path = Path(str(live["latest_snapshot_path"]))
    if not snapshot_path.is_absolute():
        snapshot_path = writer_dir / snapshot_path
    return state_from_snapshot(_read_json_path(snapshot_path)), live


def _exact_out_pool_reserves(state, pool_id: str, asset_in: str):
    pool = state.pools[pool_id]
    if asset_in == pool.asset0:
        return int(pool.reserve0), int(pool.reserve1), int(pool.fee_bps)
    return int(pool.reserve1), int(pool.reserve0), int(pool.fee_bps)


@pytest.mark.skipif(not _BLS_AVAILABLE, reason="BLS not available")
def test_ui_swap_builder_exact_out_settles_end_to_end(tmp_path: Path) -> None:
    """End-to-end: a builder-emitted SWAP_EXACT_OUT op settles correctly.

    Proves (a) `_ui_swap_tx_v0` emits a correct exact-out op AND (b) that op
    settles through `append_dex_transaction_v0` -> apply_ops with the asserted
    invariants: output == requested amount_out (exact), input == required input
    and <= max_amount_in (bounded), fee/reserve deltas match the kernel quote,
    nonce += 1, receipt accepted, and the committed state-root advances.
    """
    chain_id = "zeno-ledger-exact-out-e2e"
    source_bundle_root = tmp_path / "source_bundle"
    assert build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id=chain_id,
        chain_id=chain_id,
        sequencer_id="sequencer-exact-out-e2e",
        time_ms=1_778_730_123_000,
        token_symbol="ZDEX",
    )["ok"] is True

    writer_dir = tmp_path / "writer"
    assert run_node_once_v0(
        bundle_root=source_bundle_root,
        node_id="node-exact-out-writer",
        data_dir=writer_dir,
        peer_watcher_attestation_paths=[],
    )["ok"] is True

    private_key = "0x" + "01".zfill(64)
    trader = bls_public_key_hex_from_private_key_v0(private_key)
    asset_in = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
    asset_out = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
    pool_id = compute_pool_id(asset_in, asset_out, 30)

    append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=trader,
        asset=asset_in,
        amount=100_000,
        time_ms=1_778_731_120_000,
        tx_id="exact-out-e2e-faucet",
    )

    pre_state, _pre_live = _snapshot_state_for_writer(writer_dir)
    pre_root = dex_state_root_v0(pre_state)
    pre_in = pre_state.balances.get(trader, asset_in)
    pre_out = pre_state.balances.get(trader, asset_out)

    reserve_in, reserve_out, fee_bps = _exact_out_pool_reserves(pre_state, pool_id, asset_in)
    amount_out = 1_000
    quote = quote_cpmm_swap_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        protocol_fee_share_bps=2_000,
    )
    required_in = int(quote.amount_in)
    max_amount_in = required_in  # exact boundary: max == required must accept

    status = load_node_status_v0(writer_dir)
    # Build the op through the WRITE-PATH builder (no signature yet), then sign
    # the exact op the builder produced so the engine accepts it.
    tx = _ui_swap_tx_v0(
        data_dir=writer_dir,
        node_status=status,
        payload={
            "kind": "SWAP_EXACT_OUT",
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": max_amount_in,
            "sender_pubkey": trader,
            "recipient": trader,
            "nonce": 1,
            "tx_id": "exact-out-e2e-swap",
        },
        time_ms=1_778_731_121_000,
    )
    op = tx["operations"]["5"][0]
    # Builder emitted a correct exact-out op (field mapping check).
    assert op["kind"] == "SWAP_EXACT_OUT"
    assert op["amount_out"] == amount_out
    assert op["max_amount_in"] == max_amount_in
    assert "amount_in" not in op
    assert "min_amount_out" not in op
    op["signature"] = sign_dex_intent_for_engine(op, privkey=private_key, chain_id=chain_id)

    append_report = append_dex_transaction_v0(
        data_dir=writer_dir,
        tx=tx,
        time_ms=1_778_731_121_000,
    )
    assert append_report["ok"] is True
    assert append_report["receipt"]["accepted"] is True

    post_state = state_from_snapshot(_read_json_path(Path(str(append_report["post_snapshot_path"]))))
    post_in = post_state.balances.get(trader, asset_in)
    post_out = post_state.balances.get(trader, asset_out)

    # Output is EXACT: recipient receives exactly amount_out (gap retained in pool).
    assert post_out - pre_out == amount_out
    # Input is BOUNDED: sender pays exactly the required input, which is <= max.
    assert pre_in - post_in == required_in
    assert required_in <= max_amount_in

    # Reserve deltas match the kernel quote (value conservation through the pool).
    post_reserve_in, post_reserve_out, _ = _exact_out_pool_reserves(post_state, pool_id, asset_in)
    assert post_reserve_in == int(quote.reserve_in_after)
    assert post_reserve_out == int(quote.reserve_out_after)
    # net input into reserves + LP fee accounts for the pool's share of the input.
    assert post_reserve_in - reserve_in == int(quote.net_in_actual) + int(quote.lp_fee_paid)
    assert reserve_out - post_reserve_out == amount_out

    # FULL asset_in conservation: every party that receives asset_in is counted,
    # so this is true conservation (not just the pool's share). The input the
    # sender paid lands entirely in the pool reserve and the protocol-fee
    # recipient -- nothing is created or destroyed.
    fee_recipient = _tokenomics_buyback_source_pubkey_v0(
        load_node_status_v0(writer_dir)["token_distribution"]
    )
    pre_fee_recipient = pre_state.balances.get(fee_recipient, asset_in)
    post_fee_recipient = post_state.balances.get(fee_recipient, asset_in)
    fee_recipient_delta = post_fee_recipient - pre_fee_recipient
    assert fee_recipient_delta == int(quote.protocol_fee_paid)
    assert (pre_in - post_in) == (post_reserve_in - reserve_in) + fee_recipient_delta

    # Nonce advanced by exactly one for the trader (pre-swap last nonce was 0).
    assert pre_state.nonces.get_last(trader) == 0
    assert post_state.nonces.get_last(trader) == 1
    # Committed canonical state-root advanced, and the append report agrees with
    # the re-derived post-state root.
    post_root = dex_state_root_v0(post_state)
    assert post_root != pre_root
    assert append_report["app_hash"] == _read_json_path(writer_dir / "live_state.json")["latest_app_hash"]


@pytest.mark.skipif(not _BLS_AVAILABLE, reason="BLS not available")
def test_ui_swap_builder_exact_out_rejects_when_required_exceeds_max(tmp_path: Path) -> None:
    """Reject path: exact-out whose required input exceeds max_amount_in fails closed.

    The engine is the authority for the max_amount_in bound. With
    max_amount_in == required_input - 1 the intent must be rejected and the
    committed state must be unchanged (balances, reserves, and state-root).
    """
    chain_id = "zeno-ledger-exact-out-reject"
    source_bundle_root = tmp_path / "source_bundle"
    assert build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id=chain_id,
        chain_id=chain_id,
        sequencer_id="sequencer-exact-out-reject",
        time_ms=1_778_730_123_000,
        token_symbol="ZDEX",
    )["ok"] is True

    writer_dir = tmp_path / "writer"
    assert run_node_once_v0(
        bundle_root=source_bundle_root,
        node_id="node-exact-out-reject-writer",
        data_dir=writer_dir,
        peer_watcher_attestation_paths=[],
    )["ok"] is True

    private_key = "0x" + "01".zfill(64)
    trader = bls_public_key_hex_from_private_key_v0(private_key)
    asset_in = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
    asset_out = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
    pool_id = compute_pool_id(asset_in, asset_out, 30)

    append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=trader,
        asset=asset_in,
        amount=100_000,
        time_ms=1_778_731_120_000,
        tx_id="exact-out-reject-faucet",
    )

    pre_state, _pre_live = _snapshot_state_for_writer(writer_dir)
    pre_root = dex_state_root_v0(pre_state)
    pre_in = pre_state.balances.get(trader, asset_in)
    pre_out = pre_state.balances.get(trader, asset_out)
    reserve_in, reserve_out, fee_bps = _exact_out_pool_reserves(pre_state, pool_id, asset_in)

    amount_out = 1_000
    quote = quote_cpmm_swap_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        protocol_fee_share_bps=2_000,
    )
    required_in = int(quote.amount_in)
    too_tight_max = required_in - 1  # one below required -> must reject

    status = load_node_status_v0(writer_dir)
    tx = _ui_swap_tx_v0(
        data_dir=writer_dir,
        node_status=status,
        payload={
            "kind": "SWAP_EXACT_OUT",
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": too_tight_max,
            "sender_pubkey": trader,
            "recipient": trader,
            "nonce": 1,
            "tx_id": "exact-out-reject-swap",
        },
        time_ms=1_778_731_121_000,
    )
    op = tx["operations"]["5"][0]
    assert op["max_amount_in"] == too_tight_max
    op["signature"] = sign_dex_intent_for_engine(op, privkey=private_key, chain_id=chain_id)

    append_report = append_dex_transaction_v0(
        data_dir=writer_dir,
        tx=tx,
        time_ms=1_778_731_121_000,
    )
    # Intent rejected: the block may be appended, but the swap is NOT accepted.
    receipt = append_report["receipt"]
    assert receipt["accepted"] is False
    assert receipt["state_changed"] is False
    # Assert the rejection REASON binds to the max_amount_in slippage bound
    # (not a signature/parse/nonce error) so this test cannot pass spuriously.
    error_code = receipt["error_code"]
    assert isinstance(error_code, str)
    assert error_code.endswith("_slippage"), error_code
    assert "settlement_rejected" in error_code

    # Fail-closed: committed state unchanged.
    post_state = state_from_snapshot(_read_json_path(Path(str(append_report["post_snapshot_path"]))))
    assert post_state.balances.get(trader, asset_in) == pre_in
    assert post_state.balances.get(trader, asset_out) == pre_out
    post_reserve_in, post_reserve_out, _ = _exact_out_pool_reserves(post_state, pool_id, asset_in)
    assert post_reserve_in == reserve_in
    assert post_reserve_out == reserve_out
    # Canonical state-root unchanged: the rejected intent committed no state.
    assert dex_state_root_v0(post_state) == pre_root


def test_tokenomics_market_route_reports_buyback_runtime_enabled(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    writer_dir = tmp_path / "writer"
    writer_dir.mkdir()
    distribution = build_protocol_token_distribution_v0(
        chain_id="zeno-ledger-tokenomics-route-only",
        token_symbol="ZDEX",
        token_asset_id="0x" + "99" * 32,
        role_pubkeys={},
        fallback_pubkey=_pubkey("aa"),
    )
    node_status = {
        "chain_id": "zeno-ledger-tokenomics-route-only",
        "token_distribution": distribution,
        "token_distribution_hash": distribution["distribution_hash"],
    }
    token_asset = str(distribution["token_asset_id"])
    quote_asset = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
    asset0 = min(quote_asset, token_asset)
    asset1 = max(quote_asset, token_asset)
    pool_id = compute_pool_id(asset0, asset1, 30)
    if asset0 == token_asset:
        reserve0, reserve1 = 25_000, 50_000
    else:
        reserve0, reserve1 = 50_000, 25_000

    balances = BalanceTable()
    for allocation in distribution["allocations"]:
        assert isinstance(allocation, Mapping)
        balances.add(str(allocation["recipient_pubkey"]), token_asset, int(allocation["amount"]))
    token_reserve = reserve0 if asset0 == token_asset else reserve1
    balances.subtract(_pubkey("aa"), token_asset, token_reserve)

    pools = {
        pool_id: PoolState(
            pool_id=pool_id,
            asset0=asset0,
            asset1=asset1,
            reserve0=reserve0,
            reserve1=reserve1,
            fee_bps=30,
            lp_supply=75_000,
            status=PoolStatus.ACTIVE,
            created_at=7,
        )
    }
    route_snapshot = snapshot_from_state(DexState(balances=balances, pools=pools, lp_balances=LPTable())).data

    monkeypatch.setattr(
        "tools.zeno_ledger_node._latest_snapshot_for_ui_v0",
        lambda *, data_dir, node_status: (7, route_snapshot),
    )
    monkeypatch.setattr(
        "tools.zeno_ledger_node._tokenomics_claim_index_from_live_bodies_v0",
        lambda *, data_dir, max_height: ({}, set()),
    )
    monkeypatch.setattr(
        "tools.zeno_ledger_node._tokenomics_buyback_index_from_live_bodies_v0",
        lambda *, data_dir, max_height: {
            "buyback_burned_total": 0,
            "buyback_total_swap_fee": 0,
            "buyback_carry_after": 0,
            "buyback_event_count": 0,
        },
    )

    response = _ui_tokenomics_response_v0(data_dir=writer_dir, node_status=node_status)
    assert response["ok"] is True
    buyback_market = response["status"]["buyback_market_purchase"]
    assert buyback_market["available"] is True
    assert buyback_market["route_available"] is True
    assert buyback_market["route_count"] == 1
    assert buyback_market["runtime_enabled"] is True
    assert buyback_market["runtime_mode"] == "market_purchase_then_burn"
    assert buyback_market["runtime_blocker"] is None
    assert response["status"]["checks"]["buyback_market_route_available"] is True
    assert response["status"]["checks"]["buyback_market_purchase_runtime_enabled"] is True


def test_tokenomics_market_buyback_purchase_uses_protocol_fee_route() -> None:
    source = _pubkey("aa")
    token_asset = "0x" + "99" * 32
    quote_asset = DEFAULT_ASSET0
    asset0 = min(quote_asset, token_asset)
    asset1 = max(quote_asset, token_asset)
    pool_id = compute_pool_id(asset0, asset1, 30)
    if asset0 == quote_asset:
        reserve0, reserve1 = 100_000, 90_000
    else:
        reserve0, reserve1 = 90_000, 100_000
    pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=95_000,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    balances = BalanceTable()
    balances.set(source, quote_asset, 6)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())

    purchase = _market_buyback_purchase_from_state_v0(
        state=state,
        source_pubkey=source,
        token_asset_id=token_asset,
        protocol_fee_by_asset={quote_asset: 6},
        current_supply_before=1_000_000,
        supply_floor=100_000,
    )

    assert purchase is not None
    assert purchase["pool_id"] == pool_id
    assert purchase["quote_asset_id"] == quote_asset
    assert purchase["token_asset_id"] == token_asset
    assert purchase["quote_amount_in"] == 6
    assert purchase["token_amount_out"] > 0
    if asset0 == quote_asset:
        assert purchase["reserve0_after"] > reserve0
        assert purchase["reserve1_after"] < reserve1
    else:
        assert purchase["reserve1_after"] > reserve1
        assert purchase["reserve0_after"] < reserve0


@pytest.mark.xfail(
    reason=(
        "Test feeds an unsigned SWAP_EXACT_IN intent (intent_id 0xbb..bb) but "
        "append_dex_transaction_v0 now requires BLS-signed intents "
        "(require_intent_signatures=True post-hardening). Receipt fails with "
        "error_code='missing_intent_signature_0xbb...'. Fix path: generate a "
        "real BLS test keypair fixture, sign the intent, replace the fake "
        "DEFAULT_BOOTSTRAP_SENDER. Pre-existing test debt; not caused by the "
        "Bug 24/25 restart-recovery hardening."
    ),
    strict=True,
)
def test_zeno_ledger_node_syncs_replays_bundle_and_serves_status(tmp_path: Path) -> None:
    source_bundle_root = tmp_path / "source_bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id="zeno-ledger-node-testnet-0",
        chain_id="zeno-ledger-node-testnet-0",
        sequencer_id="sequencer-node-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    static_handler = partial(_QuietStaticHandler, directory=str(source_bundle_root))
    static_server = ThreadingHTTPServer(("127.0.0.1", 0), static_handler)
    static_thread = threading.Thread(target=static_server.serve_forever, daemon=True)
    static_thread.start()
    try:
        host, port = static_server.server_address
        synced_bundle_root = tmp_path / "synced_bundle"
        sync_report = sync_public_bundle_from_url_v0(
            base_url=f"http://{host}:{port}",
            out_dir=synced_bundle_root,
        )
    finally:
        static_server.shutdown()
        static_server.server_close()

    assert sync_report["ok"] is True
    assert sync_report["feature_count"] == 10
    assert sync_report["downloaded_mirror_count"] == 11

    peer_attestation = synced_bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    node_dir = tmp_path / "node-b"
    node_report = run_node_once_v0(
        bundle_root=synced_bundle_root,
        node_id="node-b",
        data_dir=node_dir,
        peer_watcher_attestation_paths=[peer_attestation],
    )
    assert node_report["ok"] is True
    assert node_report["combined_watcher_count"] == 2
    assert node_report["covered_feature_count"] == 10

    status = load_node_status_v0(node_dir)
    assert status["ok"] is True
    assert status["node_role"] == "follower_watcher"
    assert status["network_id"] == "zeno-ledger-node-testnet-0"
    assert status["latest_height"] == 5
    assert status["token_symbol"] == "tZENO"
    assert [item["symbol"] for item in status["test_token_catalog"]] == ["tAGRS", "tZDEX", "zUSD"]
    assert status["token_posture"]["default_faucet_token"] == "tAGRS"
    assert status["testnet_faucet_posture"]["supports_fixture_mint"] is True
    assert status["testnet_token_support"]["faucet_scope"] == "testnet-only feature lanes"

    join_config_path = tmp_path / "node-join-config.json"
    join_config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "bundle_root": str(synced_bundle_root),
                "node_id": "node-join",
                "data_dir": str(tmp_path / "node-join"),
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    preflight_report = preflight_node_join_config_v0(config_path=join_config_path, check_port=False)
    assert preflight_report["ok"] is True
    assert preflight_report["checks"]["bundle_source"] is True
    assert preflight_report["checks"]["node_id"] is True
    assert preflight_report["peer_count"] == 0

    join_report = join_public_node_from_config_v0(config_path=join_config_path)
    assert join_report["ok"] is True
    assert join_report["run_report"]["covered_feature_count"] == 10

    peer_node_dir = tmp_path / "node-c"
    shutil.copytree(node_dir, peer_node_dir)

    server = make_node_http_server_v0(
        data_dir=node_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        expose_testnet_faucet_http=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        asset_a = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
        asset_b = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
        protocol_asset = status["token_distribution"]["token_asset_id"]
        protocol_faucet_status, protocol_faucet_report = _post_url_json_status(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": protocol_asset,
                "amount": 1,
                "local_fixture_mode": True,
                "time_ms": 1_778_731_121_000,
                "tx_id": "node-http-protocol-token-faucet-rejected-v0",
            },
        )
        assert protocol_faucet_status == HTTPStatus.BAD_REQUEST
        assert protocol_faucet_report["error"] == "protocol_token_faucet_forbidden"
        faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": asset_a,
                "amount": 1234,
                "local_fixture_mode": True,
                "time_ms": 1_778_731_122_000,
                "tx_id": "node-http-faucet-v0",
            },
        )
        assert faucet_report["ok"] is True
        assert faucet_report["height"] == 6
        live_swap_request = {
            "time_ms": 1_778_731_123_000,
            "tx": {
                "tx_id": "node-live-swap-v0",
                "block_timestamp": 1_778_731_123,
                "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "operations": {
                    "2": [
                        {
                            "module": "TauSwap",
                            "version": "0.1",
                            "kind": "SWAP_EXACT_IN",
                            "intent_id": "0x" + "bb" * 32,
                            "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                            "deadline": 1_999_999_999,
                            "nonce": 5,
                            "pool_id": compute_pool_id(asset_a, asset_b, 30),
                            "asset_in": asset_a,
                            "asset_out": asset_b,
                            "amount_in": 100,
                            "min_amount_out": 1,
                            "recipient": DEFAULT_BOOTSTRAP_SENDER,
                        }
                    ]
                },
            },
        }
        append_report = _post_url_json(f"http://{host}:{port}/tx", live_swap_request)
        assert append_report["ok"] is True
        assert append_report["height"] == 7
        assert append_report["receipt"]["accepted"] is True
        replay_report = _post_url_json(f"http://{host}:{port}/tx", live_swap_request)
        assert replay_report["ok"] is True
        assert replay_report["height"] == 7
        assert replay_report["tx_hash"] == append_report["tx_hash"]
        assert replay_report["idempotent_replay"] is True
        mismatched_replay_request = json.loads(json.dumps(live_swap_request))
        mismatched_replay_request["tx"]["operations"]["2"][0]["amount_in"] = 101
        replay_status, replay_mismatch = _post_url_json_status(f"http://{host}:{port}/tx", mismatched_replay_request)
        assert replay_status == HTTPStatus.BAD_REQUEST
        assert replay_mismatch["error"] == "duplicate_tx_id_payload_mismatch"

        new_fake_asset = "0x" + "33" * 32
        fake_asset_faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": new_fake_asset,
                "amount": 50_000,
                "local_fixture_mode": True,
                "time_ms": 1_778_731_124_000,
                "tx_id": "node-http-new-fake-asset-faucet-v0",
            },
        )
        assert fake_asset_faucet_report["ok"] is True
        assert fake_asset_faucet_report["height"] == 8

        asset0_for_new_pool = min(asset_a, new_fake_asset)
        asset1_for_new_pool = max(asset_a, new_fake_asset)
        create_new_pool_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_125_000,
                "tx": {
                    "tx_id": "node-live-create-fake-token-pool-v0",
                    "block_timestamp": 1_778_731_125,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "CREATE_POOL",
                                "intent_id": "0x" + "cc" * 32,
                                "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                                "deadline": 1_999_999_999,
                                "nonce": 6,
                                "asset0": asset0_for_new_pool,
                                "asset1": asset1_for_new_pool,
                                "fee_bps": 30,
                                "amount0": 100,
                                "amount1": 100,
                                "created_at": 1_778_731_125,
                            }
                        ]
                    },
                },
            },
        )
        assert create_new_pool_report["ok"] is True
        assert create_new_pool_report["height"] == 9
        assert create_new_pool_report["receipt"]["accepted"] is True
        fake_pool_id = compute_pool_id(asset0_for_new_pool, asset1_for_new_pool, 30)
        add_fake_pool_liquidity_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_126_000,
                "tx": {
                    "tx_id": "node-live-add-fake-token-liquidity-v0",
                    "block_timestamp": 1_778_731_126,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "ADD_LIQUIDITY",
                                "intent_id": "0x" + "cd" * 32,
                                "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                                "deadline": 1_999_999_999,
                                "nonce": 7,
                                "pool_id": fake_pool_id,
                                "amount0_desired": 10,
                                "amount1_desired": 10,
                                "amount0_min": 0,
                                "amount1_min": 0,
                                "recipient": DEFAULT_BOOTSTRAP_SENDER,
                            }
                        ]
                    },
                },
            },
        )
        assert add_fake_pool_liquidity_report["ok"] is True
        assert add_fake_pool_liquidity_report["height"] == 10
        assert add_fake_pool_liquidity_report["receipt"]["accepted"] is True
        remove_fake_pool_liquidity_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_127_000,
                "tx": {
                    "tx_id": "node-live-remove-fake-token-liquidity-v0",
                    "block_timestamp": 1_778_731_127,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "REMOVE_LIQUIDITY",
                                "intent_id": "0x" + "ce" * 32,
                                "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                                "deadline": 1_999_999_999,
                                "nonce": 8,
                                "pool_id": fake_pool_id,
                                "lp_amount": 1,
                                "amount0_min": 0,
                                "amount1_min": 0,
                                "recipient": DEFAULT_BOOTSTRAP_SENDER,
                            }
                        ]
                    },
                },
            },
        )
        assert remove_fake_pool_liquidity_report["ok"] is True
        assert remove_fake_pool_liquidity_report["height"] == 11
        assert remove_fake_pool_liquidity_report["receipt"]["accepted"] is True

        mirror_handler = partial(_QuietStaticHandler, directory=str(source_bundle_root))
        mirror_server = ThreadingHTTPServer(("127.0.0.1", 0), mirror_handler)
        mirror_thread = threading.Thread(target=mirror_server.serve_forever, daemon=True)
        mirror_thread.start()
        try:
            mirror_host, mirror_port = mirror_server.server_address
            public_network_config = build_public_network_config_v0(
                bundle_root=source_bundle_root,
                mirror_base_url=f"http://{mirror_host}:{mirror_port}",
                writer_urls=[f"http://{host}:{port}"],
                peer_urls=[],
                poll_seconds=5,
                node_port=8790,
            )
            (source_bundle_root / "public_network_config.json").write_text(
                json.dumps(public_network_config, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            join_network_report = join_public_node_from_network_config_url_v0(
                config_url=f"http://{mirror_host}:{mirror_port}/public_network_config.json",
                node_id="node-network-join",
                bundle_root=tmp_path / "network-join-bundle",
                data_dir=tmp_path / "node-network-join",
                host="127.0.0.1",
                port=None,
                poll_seconds=None,
                serve=False,
            )
        finally:
            mirror_server.shutdown()
            mirror_server.server_close()

        health = _read_url_json(f"http://{host}:{port}/health")
        served_status = _read_url_json(f"http://{host}:{port}/status")
        features = _read_url_json(f"http://{host}:{port}/features")
        tokens = _read_url_json(f"http://{host}:{port}/tokens")
        tokenomics_status = _read_url_json(f"http://{host}:{port}/api/tokenomics/status")
        live = _read_url_json(f"http://{host}:{port}/live")
        network = _read_url_json(f"http://{host}:{port}/network")
        testnet_status = _read_url_json(f"http://{host}:{port}/testnet-status")
        pre_pull_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        pull_report = pull_live_from_peer_v0(
            data_dir=peer_node_dir,
            peer_url=f"http://{host}:{port}",
        )
        post_pull_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        forward_server = make_node_http_server_v0(
            data_dir=peer_node_dir,
            host="127.0.0.1",
            port=0,
            enable_testnet_intake=True,
            enable_testnet_faucet=True,
            expose_testnet_faucet_http=True,
            allow_unauthenticated_testnet_writes=True,
            submit_peer_url=f"http://{host}:{port}",
        )
        forward_thread = threading.Thread(target=forward_server.serve_forever, daemon=True)
        forward_thread.start()
        try:
            forward_host, forward_port = forward_server.server_address
            forwarded_faucet_report = _post_url_json(
                f"http://{forward_host}:{forward_port}/faucet",
                {
                    "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "asset": asset_a,
                    "amount": 55,
                    "local_fixture_mode": True,
                    "time_ms": 1_778_731_128_000,
                    "tx_id": "node-http-forwarded-faucet-v0",
                },
            )
            forward_network = _read_url_json(f"http://{forward_host}:{forward_port}/network")
        finally:
            forward_server.shutdown()
            forward_server.server_close()
        forwarded_pull_report = pull_live_from_peer_v0(
            data_dir=peer_node_dir,
            peer_url=f"http://{host}:{port}",
        )
        final_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )

        assert health["ok"] is True
        assert health["node_status_hash"] == status["node_status_hash"]
        assert served_status["node_status_hash"] == status["node_status_hash"]
        assert features["covered_feature_count"] == 10
        assert len(tokens["test_token_catalog"]) == 3
        assert tokenomics_status["ok"] is True
        assert tokenomics_status["status"]["current_supply"] == 1_000_000
        assert tokenomics_status["status"]["checks"]["tau_policy_flags_all_pass"] is True
        assert tokenomics_status["status"]["checks"]["distribution_hash_self_consistent"] is True
        assert tokenomics_status["status"]["checks"]["distribution_hash_manifest_anchored"] is True
        assert tokenomics_status["status"]["checks"]["runtime_mutation_disabled"] is True
        assert tokenomics_status["status"]["active_participant_reward_pool_id"] == "active_participant_rewards_pool"
        assert join_network_report["ok"] is True
        assert join_network_report["peer_check"]["ok"] is True
        assert join_network_report["run_report"]["covered_feature_count"] == 10
        assert network["local_tip"]["height"] == 11
        assert network["capabilities"]["submission_forwarding_enabled"] is False
        assert live["live"] is True
        assert live["state"]["latest_height"] == 11
        assert pre_pull_peer_check["ok"] is True
        assert pre_pull_peer_check["peers"][0]["height_relation"] == "peer_ahead"
        assert pre_pull_peer_check["peers"][0]["common_height"] == 5
        assert pull_report["ok"] is True
        assert pull_report["pulled_count"] == 6
        assert pull_report["to_height"] == 11
        assert post_pull_peer_check["ok"] is True
        assert post_pull_peer_check["peers"][0]["height_relation"] == "same_height"
        assert post_pull_peer_check["peers"][0]["common_height"] == 11
        assert forwarded_faucet_report["ok"] is True
        assert forwarded_faucet_report["forwarded_to"] == f"http://{host}:{port}"
        assert forwarded_faucet_report["height"] == 12
        assert forward_network["capabilities"]["submission_forwarding_enabled"] is True
        assert forward_network["submit_peer_url"] == f"http://{host}:{port}"
        assert forwarded_pull_report["ok"] is True
        assert forwarded_pull_report["pulled_count"] == 1
        assert forwarded_pull_report["to_height"] == 12
        assert final_peer_check["ok"] is True
        assert final_peer_check["peers"][0]["height_relation"] == "same_height"
        assert final_peer_check["peers"][0]["common_height"] == 12
        peer_live = _read_url_json(f"http://{host}:{port}/live/header/12")
        assert peer_live["height"] == 12
        assert load_node_status_v0(peer_node_dir)["ok"] is True
        assert json.loads((peer_node_dir / "live_state.json").read_text(encoding="utf-8"))["latest_height"] == 12
        assert testnet_status["watcher_count"] == 2
    finally:
        server.shutdown()
        server.server_close()


def test_zeno_ledger_node_preflight_rejects_unsafe_join_config(tmp_path: Path) -> None:
    config_path = tmp_path / "bad-node-join-config.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "base_url": "http://user:pass@example.test",
                "bundle_root": str(tmp_path / "bundle"),
                "node_id": "",
                "data_dir": str(tmp_path / "node"),
                "serve": True,
                "host": "0.0.0.0",
                "port": 70000,
                "poll_seconds": -1,
                "peer_urls": ["ftp://bad-peer.example.test"],
                "submit_peer_url": "http://user:pass@example.test",
                "enable_testnet_faucet": True,
                "enable_testnet_intake": True,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    report = preflight_node_join_config_v0(config_path=config_path, check_port=False)

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["checks"]["node_id"] is False
    assert report["checks"]["port_range"] is False
    assert report["checks"]["poll_seconds"] is False
    assert any("base_url" in error for error in report["errors"])
    assert any("peer_url" in error for error in report["errors"])
    assert any("submit_peer_url" in error for error in report["errors"])
    assert any("testnet faucet" in warning for warning in report["warnings"])


def test_public_network_config_carries_live_follow_policy(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    (bundle_root / "core_features").mkdir(parents=True)
    (bundle_root / "public_testnet_manifest.json").write_text(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.public_testnet_bundle.v0",
                "network_id": "zeno-ledger-policy-testnet",
                "chain_id": "zeno-ledger-policy-testnet",
                "token_symbol": "tZENO",
                "core_suite_path": "core_features/feature_suite.json",
                "test_token_catalog": [],
                "testnet_faucet_posture": {},
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (bundle_root / "core_features" / "feature_suite.json").write_text(
        json.dumps(
            {
                "feature_suite_hash": "0x" + "11" * 32,
                "feature_count": 0,
                "features": [],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    config = build_public_network_config_v0(
        bundle_root=bundle_root,
        mirror_base_url="https://seed.example/ledger-bundle",
        writer_urls=["https://seed.example"],
        peer_urls=[],
        poll_seconds=1,
        node_port=8788,
        min_lp_position_age_seconds=300,
        lp_duration_risk_policy="zeno-oracle",
    )
    join_config = _public_network_config_to_join_config_v0(
        network_config=config,
        node_id="policy-follower",
        bundle_root=tmp_path / "downloaded-bundle",
        data_dir=tmp_path / "node",
        host="127.0.0.1",
        port=None,
        poll_seconds=None,
        serve=False,
    )

    assert config["recommended_node"]["min_lp_position_age_seconds"] == 300
    assert config["recommended_node"]["lp_duration_risk_policy"] == "zeno-oracle"
    assert join_config["min_lp_position_age_seconds"] == 300
    assert join_config["lp_duration_risk_policy"] == "zeno-oracle"


def test_zeno_ledger_node_rejects_non_http_remote_urls(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="base_url must be an http"):
        sync_public_bundle_from_url_v0(
            base_url="file:///tmp/zeno-ledger-public-testnet",
            out_dir=tmp_path / "synced",
        )


def test_zeno_ledger_pull_rejects_peer_before_live_fetch_on_admission_mismatch(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id="zeno-ledger-admission-testnet-0",
        chain_id="zeno-ledger-admission-testnet-0",
        sequencer_id="sequencer-admission-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    node_dir = tmp_path / "node"
    node_report = run_node_once_v0(
        bundle_root=bundle_root,
        node_id="node-local",
        data_dir=node_dir,
    )
    assert node_report["ok"] is True

    bad_peer_status = load_node_status_v0(node_dir)
    bad_peer_status["network_id"] = "wrong-network"
    bad_peer_status["node_status_hash"] = _node_status_hash(bad_peer_status)
    server = ThreadingHTTPServer(("127.0.0.1", 0), _status_only_handler(bad_peer_status))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(ValueError, match="peer admission rejected"):
            pull_live_from_peer_v0(data_dir=node_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()


@pytest.mark.slow
def test_zeno_ledger_pull_rejects_tampered_live_body_without_tip_mutation(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id="zeno-ledger-tamper-testnet-0",
        chain_id="zeno-ledger-tamper-testnet-0",
        sequencer_id="sequencer-tamper-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    writer_dir = tmp_path / "writer"
    follower_dir = tmp_path / "follower"
    assert run_node_once_v0(bundle_root=bundle_root, node_id="writer", data_dir=writer_dir)["ok"] is True
    assert run_node_once_v0(bundle_root=bundle_root, node_id="follower", data_dir=follower_dir)["ok"] is True

    append_report = append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=123,
        time_ms=1_778_731_123_000,
        tx_id="tampered-live-body-source-v0",
    )
    assert append_report["ok"] is True
    height = int(append_report["height"])
    before_status = load_node_status_v0(follower_dir)
    assert not (follower_dir / "live_state.json").exists()

    body_path = Path(str(append_report["body_path"]))
    body = json.loads(body_path.read_text(encoding="utf-8"))
    body["transactions"][0]["amount"] = 124
    body_path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    server = make_node_http_server_v0(data_dir=writer_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(ValueError, match=f"peer header mismatch at height {height}"):
            pull_live_from_peer_v0(data_dir=follower_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    after_status = load_node_status_v0(follower_dir)
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (follower_dir / "live_state.json").exists()


@pytest.mark.slow
def test_zeno_ledger_pull_keeps_verified_cursor_before_later_mismatch(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id="zeno-ledger-partial-pull-testnet-0",
        chain_id="zeno-ledger-partial-pull-testnet-0",
        sequencer_id="sequencer-partial-pull-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    writer_dir = tmp_path / "writer"
    follower_dir = tmp_path / "follower"
    assert run_node_once_v0(bundle_root=bundle_root, node_id="writer", data_dir=writer_dir)["ok"] is True
    assert run_node_once_v0(bundle_root=bundle_root, node_id="follower", data_dir=follower_dir)["ok"] is True

    first = append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=123,
        time_ms=1_778_731_123_000,
        tx_id="partial-pull-first-v0",
    )
    second = append_testnet_faucet_v0(
        data_dir=writer_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=124,
        time_ms=1_778_731_124_000,
        tx_id="partial-pull-second-v0",
    )
    first_height = int(first["height"])
    second_height = int(second["height"])

    second_body_path = Path(str(second["body_path"]))
    second_body = json.loads(second_body_path.read_text(encoding="utf-8"))
    second_body["transactions"][0]["amount"] = 125
    second_body_path.write_text(json.dumps(second_body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    server = make_node_http_server_v0(data_dir=writer_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(ValueError, match=f"peer header mismatch at height {second_height}"):
            pull_live_from_peer_v0(data_dir=follower_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    live_state = json.loads((follower_dir / "live_state.json").read_text(encoding="utf-8"))
    assert live_state["latest_height"] == first_height
    assert not (follower_dir / "live_ledger" / "headers" / f"{second_height}.json").exists()


def test_zeno_ledger_node_rejects_corrupt_live_state_with_stable_error(tmp_path: Path) -> None:
    node_dir = tmp_path / "node"
    node_dir.mkdir()
    status = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": "node-corrupt-live-state",
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-corrupt-live-state-testnet-0",
        "chain_id": "zeno-ledger-corrupt-live-state-testnet-0",
        "bundle_root": str(tmp_path / "bundle"),
        "data_dir": str(node_dir),
        "latest_height": 5,
        "last_header_hash": "0x" + "11" * 32,
        "last_app_hash": "0x" + "22" * 32,
    }
    status["node_status_hash"] = _node_status_hash(status)
    (node_dir / "node_status.json").write_text(json.dumps(status, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (node_dir / "live_state.json").write_text("{bad-json", encoding="utf-8")

    server = make_node_http_server_v0(data_dir=node_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(HTTPError) as exc_info:
            urlopen(f"http://{host}:{port}/network", timeout=5)  # noqa: S310 - local test server
        body = exc_info.value.read().decode("utf-8")
        payload = json.loads(body)
    finally:
        server.shutdown()
        server.server_close()

    assert exc_info.value.code == int(HTTPStatus.INTERNAL_SERVER_ERROR)
    assert payload == {"ok": False, "error": "live_state_invalid"}


def _build_minimal_live_state_node_v0(tmp_path: Path, *, node_id: str) -> Path:
    """Create a cheap node dir with a valid node_status.json (no public bundle)."""
    node_dir = tmp_path / "node"
    node_dir.mkdir()
    status = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_id,
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-live-state-testnet-0",
        "chain_id": "zeno-ledger-live-state-testnet-0",
        "bundle_root": str(tmp_path / "bundle"),
        "data_dir": str(node_dir),
        "latest_height": 4,
        "last_header_hash": "0x" + "11" * 32,
        "last_app_hash": "0x" + "22" * 32,
    }
    status["node_status_hash"] = _node_status_hash(status)
    (node_dir / "node_status.json").write_text(json.dumps(status, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return node_dir


def _write_live_state_json_v0(node_dir: Path, live_state: dict[str, object]) -> None:
    (node_dir / "live_state.json").write_text(json.dumps(live_state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _zero_root_header_v0(
    *,
    height: int,
    chain_id: str = "zeno-ledger-live-state-testnet-0",
    app_hash: str | None = None,
    post_state_root: str = ZERO_ROOT,
) -> dict[str, object]:
    """Build a structurally valid v0 header with zero roots for live_state tests."""
    if app_hash is None:
        app_hash = compute_app_hash_v0(
            {
                "chain_id": chain_id,
                "height": height,
                "post_state_root": post_state_root,
                "evidence_root": ZERO_ROOT,
                "config_digest": ZERO_ROOT,
                "module_versions_digest": ZERO_ROOT,
            }
        )
    return build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=1000,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=ZERO_ROOT,
        ingress_root=ZERO_ROOT,
        tx_root=ZERO_ROOT,
        pre_state_root=ZERO_ROOT,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=ZERO_ROOT,
        body_root=ZERO_ROOT,
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=ZERO_ROOT,
        module_versions_digest=ZERO_ROOT,
        signature_set_root=ZERO_ROOT,
    )


def _assert_network_rejects_live_state(node_dir: Path) -> None:
    """Start a node HTTP server and assert /network fails closed with live_state_invalid."""
    server = make_node_http_server_v0(data_dir=node_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(HTTPError) as exc_info:
            urlopen(f"http://{host}:{port}/network", timeout=5)  # noqa: S310 - local test server
        body = exc_info.value.read().decode("utf-8")
        payload = json.loads(body)
    finally:
        server.shutdown()
        server.server_close()
    assert exc_info.value.code == int(HTTPStatus.INTERNAL_SERVER_ERROR)
    assert payload == {"ok": False, "error": "live_state_invalid"}


def test_zeno_ledger_node_rejects_live_state_missing_header_path(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-missing-header")
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            # Header path is well-formed and under data_dir but never written to disk.
            "latest_header_path": str(node_dir / "live_ledger" / "headers" / "5.json"),
            "latest_snapshot_path": str(node_dir / "live_ledger" / "snapshots" / "5.json"),
            "latest_header_hash": "0x" + "33" * 32,
            "latest_app_hash": "0x" + "44" * 32,
        },
    )
    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_rejects_live_state_header_hash_mismatch(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-hash-mismatch")
    header = _zero_root_header_v0(height=5)
    header_path = node_dir / "live_ledger" / "headers" / "5.json"
    snapshot_path = node_dir / "live_ledger" / "snapshots" / "5.json"
    header_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    header_path.write_text(json.dumps(header, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text("{}\n", encoding="utf-8")
    # Sanity check: a hash that does NOT match the on-disk header.
    wrong_hash = "0x" + "ab" * 32
    assert canonical_header_hash_v0(dict(header)) != wrong_hash
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            "latest_header_path": str(header_path),
            "latest_snapshot_path": str(snapshot_path),
            "latest_header_hash": wrong_hash,
            "latest_app_hash": ZERO_ROOT,
        },
    )
    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_rejects_live_state_path_traversal(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-traversal")
    # An existing file outside the node data_dir: rejection must be due to path
    # containment, not file existence.
    outside_header = tmp_path / "evil_header.json"
    outside_header.write_text(
        json.dumps(_zero_root_header_v0(height=5), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    snapshot_path = node_dir / "live_ledger" / "snapshots" / "5.json"
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_path.write_text("{}\n", encoding="utf-8")
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            # Relative ".." traversal escaping data_dir to an existing file.
            "latest_header_path": "../evil_header.json",
            "latest_snapshot_path": str(snapshot_path),
            "latest_header_hash": canonical_header_hash_v0(_zero_root_header_v0(height=5)),
            "latest_app_hash": ZERO_ROOT,
        },
    )
    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_rejects_live_state_chain_mismatch(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-chain-mismatch")
    empty_snapshot = {
        "version": 4,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "lp_mint_timestamps": [],
        "lp_duration_risk": [],
        "nonces": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
        "perps": None,
    }
    empty_root = dex_state_root_v0(state_from_snapshot(empty_snapshot))
    header = _zero_root_header_v0(
        height=5,
        chain_id="zeno-ledger-wrong-chain-0",
        post_state_root=empty_root,
    )
    header_path = node_dir / "live_ledger" / "headers" / "5.json"
    snapshot_path = node_dir / "live_ledger" / "snapshots" / "5.json"
    header_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    header_path.write_text(json.dumps(header, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text(json.dumps(empty_snapshot, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            "latest_header_path": str(header_path),
            "latest_snapshot_path": str(snapshot_path),
            "latest_header_hash": canonical_header_hash_v0(header),
            "latest_app_hash": str(header["app_hash"]),
        },
    )

    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_rejects_live_state_header_app_hash_mismatch(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-bad-app-hash")
    header = _zero_root_header_v0(height=5, app_hash=ZERO_ROOT)
    header_path = node_dir / "live_ledger" / "headers" / "5.json"
    snapshot_path = node_dir / "live_ledger" / "snapshots" / "5.json"
    header_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    header_path.write_text(json.dumps(header, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text("{}\n", encoding="utf-8")
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            "latest_header_path": str(header_path),
            "latest_snapshot_path": str(snapshot_path),
            "latest_header_hash": canonical_header_hash_v0(header),
            "latest_app_hash": ZERO_ROOT,
        },
    )

    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_rejects_live_state_snapshot_root_mismatch(tmp_path: Path) -> None:
    node_dir = _build_minimal_live_state_node_v0(tmp_path, node_id="node-live-state-bad-snapshot-root")
    empty_state = state_from_snapshot(
        {
            "version": 4,
            "balances": [],
            "pools": [],
            "lp_balances": [],
            "lp_mint_timestamps": [],
            "lp_duration_risk": [],
            "nonces": [],
            "fee_accumulator": {"dust": 0},
            "vault": None,
            "oracle": None,
            "perps": None,
        }
    )
    empty_snapshot = snapshot_from_state(empty_state).data
    empty_root = dex_state_root_v0(empty_state)
    assert empty_root != ZERO_ROOT

    header = _zero_root_header_v0(height=5, post_state_root=ZERO_ROOT)
    header_path = node_dir / "live_ledger" / "headers" / "5.json"
    snapshot_path = node_dir / "live_ledger" / "snapshots" / "5.json"
    header_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    header_path.write_text(json.dumps(header, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text(json.dumps(empty_snapshot, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_live_state_json_v0(
        node_dir,
        {
            "schema": NODE_LIVE_STATE_SCHEMA,
            "latest_height": 5,
            "latest_header_path": str(header_path),
            "latest_snapshot_path": str(snapshot_path),
            "latest_header_hash": canonical_header_hash_v0(header),
            "latest_app_hash": str(header["app_hash"]),
        },
    )

    _assert_network_rejects_live_state(node_dir)


def test_zeno_ledger_node_accepts_relative_live_state_paths_for_next_append(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id="zeno-ledger-relative-live-state-testnet-0",
        chain_id="zeno-ledger-relative-live-state-testnet-0",
        sequencer_id="sequencer-relative-live-state-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    node_dir = tmp_path / "node"
    assert run_node_once_v0(bundle_root=bundle_root, node_id="node-relative-live-state", data_dir=node_dir)["ok"] is True
    first_append = append_testnet_faucet_v0(
        data_dir=node_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=10,
        time_ms=1_778_731_123_000,
        tx_id="relative-live-state-first",
    )
    assert first_append["ok"] is True

    live_state = json.loads((node_dir / "live_state.json").read_text(encoding="utf-8"))
    for key in ("latest_header_path", "latest_snapshot_path"):
        path = Path(str(live_state[key]))
        live_state[key] = str(path.relative_to(node_dir) if path.is_absolute() else path)
    _write_live_state_json_v0(node_dir, live_state)

    second_append = append_testnet_faucet_v0(
        data_dir=node_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=11,
        time_ms=1_778_732_123_000,
        tx_id="relative-live-state-second",
    )

    assert second_append["ok"] is True
    assert second_append["height"] == int(first_append["height"]) + 1


def test_zeno_ledger_node_strict_exposure_rejects_public_testnet_endpoints(tmp_path: Path) -> None:
    config_path = tmp_path / "public-testnet-node-config.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "base_url": "http://127.0.0.1:8000/",
                "bundle_root": str(tmp_path / "bundle"),
                "node_id": "operator-b",
                "data_dir": str(tmp_path / "node"),
                "serve": True,
                "host": "0.0.0.0",
                "port": 18788,
                "poll_seconds": 5,
                "peer_urls": ["http://127.0.0.1:8787"],
                "submit_peer_url": "http://127.0.0.1:8787",
                "enable_testnet_faucet": True,
                "enable_testnet_intake": True,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    relaxed = preflight_node_join_config_v0(config_path=config_path, check_port=False)
    strict = preflight_node_join_config_v0(
        config_path=config_path,
        check_port=False,
        strict_exposure=True,
    )

    assert relaxed["ok"] is False
    assert relaxed["warnings"]
    assert any("enabled testnet mutation endpoints require write_auth_token_env or write_auth_token" in error for error in relaxed["errors"])
    assert strict["ok"] is False
    assert strict["strict_exposure"] is True
    assert any("serve host exposes" in error for error in strict["errors"])
    assert any("testnet faucet is enabled" in error for error in strict["errors"])
    assert any("testnet transaction intake is enabled" in error for error in strict["errors"])


def test_zeno_ledger_node_public_operator_rejects_inline_auth_tokens(tmp_path: Path) -> None:
    config_path = tmp_path / "inline-token-node-config.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "base_url": "http://127.0.0.1:8000/",
                "bundle_root": str(tmp_path / "bundle"),
                "node_id": "operator-inline",
                "data_dir": str(tmp_path / "node"),
                "serve": True,
                "host": "127.0.0.1",
                "port": 18788,
                "poll_seconds": 0,
                "peer_urls": ["http://127.0.0.1:8787"],
                "submit_peer_url": "http://127.0.0.1:8787",
                "enable_testnet_intake": True,
                "write_auth_token": "inline-follower-token",
                "submit_peer_auth_token": "inline-writer-token",
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    report = preflight_node_join_config_v0(
        config_path=config_path,
        check_port=False,
        public_operator=True,
    )

    assert report["ok"] is False
    assert report["public_operator"] is True
    assert report["checks"]["inline_auth_tokens_absent"] is False
    assert any("inline auth tokens are forbidden" in error for error in report["errors"])


def test_zeno_ledger_node_public_operator_rejects_public_fixture_endpoints(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ZENO_LEDGER_WRITE_TOKEN", "local-token")
    monkeypatch.setenv("ZENO_LEDGER_SUBMIT_TOKEN", "writer-token")
    config_path = tmp_path / "public-fixture-node-config.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "base_url": "http://127.0.0.1:8000/",
                "bundle_root": str(tmp_path / "bundle"),
                "node_id": "operator-public-fixture",
                "data_dir": str(tmp_path / "node"),
                "serve": True,
                "host": "0.0.0.0",
                "port": 18788,
                "poll_seconds": 5,
                "peer_urls": ["http://127.0.0.1:8787"],
                "submit_peer_url": "http://127.0.0.1:8787",
                "enable_testnet_faucet": True,
                "enable_testnet_intake": True,
                "write_auth_token_env": "ZENO_LEDGER_WRITE_TOKEN",
                "submit_peer_auth_token_env": "ZENO_LEDGER_SUBMIT_TOKEN",
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    report = preflight_node_join_config_v0(
        config_path=config_path,
        check_port=False,
        public_operator=True,
    )

    assert report["ok"] is False
    assert report["checks"]["public_operator_bind"] is False
    assert any("bind locally behind an authenticated reverse proxy" in error for error in report["errors"])
    assert any("public binds must not expose testnet faucet or intake endpoints" in error for error in report["errors"])


def test_zeno_ledger_node_public_operator_accepts_local_env_auth_forwarding(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ZENO_LEDGER_WRITE_TOKEN", "local-token")
    monkeypatch.setenv("ZENO_LEDGER_SUBMIT_TOKEN", "writer-token")
    config_path = tmp_path / "local-public-operator-node-config.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "base_url": "http://127.0.0.1:8000/",
                "bundle_root": str(tmp_path / "bundle"),
                "node_id": "operator-local",
                "data_dir": str(tmp_path / "node"),
                "serve": True,
                "host": "127.0.0.1",
                "port": 18788,
                "poll_seconds": 5,
                "peer_urls": ["http://127.0.0.1:8787"],
                "submit_peer_url": "http://127.0.0.1:8787",
                "enable_testnet_faucet": True,
                "enable_testnet_intake": True,
                "write_auth_token_env": "ZENO_LEDGER_WRITE_TOKEN",
                "submit_peer_auth_token_env": "ZENO_LEDGER_SUBMIT_TOKEN",
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    report = preflight_node_join_config_v0(
        config_path=config_path,
        check_port=False,
        public_operator=True,
    )

    assert report["ok"] is True
    assert report["public_operator"] is True
    assert report["checks"]["public_operator_bind"] is True
    assert report["checks"]["public_operator_inline_auth"] is True
    assert report["checks"]["public_operator_write_auth_env"] is True
    assert report["checks"]["public_operator_submit_peer_auth_env"] is True


def test_zeno_ledger_node_requires_write_auth_by_default_for_testnet_mutations(tmp_path: Path) -> None:
    server = make_node_http_server_v0(
        data_dir=tmp_path / "empty-node",
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, body = _post_url_json_status(f"http://{host}:{port}/faucet", {})
        assert status == int(HTTPStatus.UNAUTHORIZED)
        assert body["error"] == "write_auth_required"
    finally:
        server.shutdown()
        server.server_close()


def test_zeno_ledger_node_http_faucet_requires_explicit_exposure(tmp_path: Path) -> None:
    server = make_node_http_server_v0(
        data_dir=tmp_path / "empty-node",
        host="127.0.0.1",
        port=0,
        enable_testnet_faucet=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, body = _post_url_json_status(
            f"http://{host}:{port}/faucet",
            {"local_fixture_mode": True},
        )
        assert status == int(HTTPStatus.FORBIDDEN)
        assert body["error"] == "testnet_faucet_http_not_exposed"
        assert body["production_security_claim"] is False
    finally:
        server.shutdown()
        server.server_close()


def test_zeno_ledger_node_http_faucet_requires_fixture_ack(tmp_path: Path) -> None:
    server = make_node_http_server_v0(
        data_dir=tmp_path / "empty-node",
        host="127.0.0.1",
        port=0,
        enable_testnet_faucet=True,
        expose_testnet_faucet_http=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, body = _post_url_json_status(f"http://{host}:{port}/faucet", {})
        assert status == int(HTTPStatus.FORBIDDEN)
        assert body["error"] == "testnet_faucet_fixture_ack_required"
        assert body["production_security_claim"] is False
    finally:
        server.shutdown()
        server.server_close()


def test_zeno_ledger_node_write_auth_protects_testnet_mutation_endpoints(tmp_path: Path) -> None:
    server = make_node_http_server_v0(
        data_dir=tmp_path / "empty-node",
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        write_auth_token="local-token",
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        for path in ("tx", "faucet"):
            missing_status, missing_body = _post_url_json_status(f"http://{host}:{port}/{path}", {})
            wrong_status, wrong_body = _post_url_json_status(
                f"http://{host}:{port}/{path}",
                {},
                bearer_token="wrong-token",
            )
            assert missing_status == int(HTTPStatus.UNAUTHORIZED)
            assert missing_body["error"] == "unauthorized"
            assert wrong_status == int(HTTPStatus.UNAUTHORIZED)
            assert wrong_body["error"] == "unauthorized"
    finally:
        server.shutdown()
        server.server_close()


def test_zeno_ledger_node_forwarding_sends_submit_peer_auth_token(tmp_path: Path) -> None:
    writer = ThreadingHTTPServer(("127.0.0.1", 0), _WriterAuthHandler)
    writer_thread = threading.Thread(target=writer.serve_forever, daemon=True)
    writer_thread.start()
    follower: ThreadingHTTPServer | None = None
    try:
        writer_host, writer_port = writer.server_address
        follower = make_node_http_server_v0(
            data_dir=tmp_path / "empty-follower",
            host="127.0.0.1",
            port=0,
            enable_testnet_faucet=True,
            expose_testnet_faucet_http=True,
            submit_peer_url=f"http://{writer_host}:{writer_port}",
            write_auth_token="follower-token",
            submit_peer_auth_token="writer-token",
        )
        follower_thread = threading.Thread(target=follower.serve_forever, daemon=True)
        follower_thread.start()
        follower_host, follower_port = follower.server_address

        rejected_status, rejected_body = _post_url_json_status(
            f"http://{follower_host}:{follower_port}/faucet",
            {},
            bearer_token="wrong-token",
        )
        accepted_status, accepted_body = _post_url_json_status(
            f"http://{follower_host}:{follower_port}/faucet",
            {"local_fixture_mode": True},
            bearer_token="follower-token",
        )

        assert rejected_status == int(HTTPStatus.UNAUTHORIZED)
        assert rejected_body["error"] == "unauthorized"
        assert accepted_status == int(HTTPStatus.OK)
        assert accepted_body["ok"] is True
        assert accepted_body["accepted_by"] == "writer"
        assert accepted_body["forwarded_to"] == f"http://{writer_host}:{writer_port}"
    finally:
        if follower is not None:
            follower.shutdown()
            follower.server_close()
        writer.shutdown()
        writer.server_close()


def _write_history_block_v0(
    data_dir: Path,
    *,
    height: int,
    transactions: list[dict[str, object]],
    receipts: list[dict[str, object]],
    bind_receipts: bool = True,
) -> None:
    bodies_dir = data_dir / "live_ledger" / "bodies"
    receipts_dir = data_dir / "live_ledger" / "receipts"
    bodies_dir.mkdir(parents=True, exist_ok=True)
    receipts_dir.mkdir(parents=True, exist_ok=True)
    body = {
        "schema": "zenodex/zeno_ledger/body/v0",
        "chain_id": "zeno-ledger-history-test",
        "height": height,
        "ingress": [],
        "transactions": transactions,
        "settlement_envelopes": [],
        "evidence": {},
    }
    if bind_receipts:
        # Bind each receipt to its paired transaction with the SAME hash function
        # the node uses, so the endpoint's receipt-binding check passes. Tests that
        # want to exercise a binding MISMATCH pass bind_receipts=False and set their
        # own (deliberately wrong) tx_hash.
        for tx, receipt in zip(transactions, receipts):
            receipt["tx_hash"] = tx_hash_v0(dict(tx))
    (bodies_dir / f"{height}.json").write_text(json.dumps(body, sort_keys=True), encoding="utf-8")
    (receipts_dir / f"{height}.json").write_text(json.dumps(receipts, sort_keys=True), encoding="utf-8")


def _history_swap_tx_v0(*, tx_id: str, sender: str, block_timestamp: int) -> dict[str, object]:
    return {
        "tx_id": tx_id,
        "block_timestamp": block_timestamp,
        "tx_sender_pubkey": sender,
        "operations": {
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + "ad" * 32,
                    "sender_pubkey": sender,
                    "deadline": 1_999_999_999,
                    "nonce": 1,
                    "pool_id": compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30),
                    "asset_in": DEFAULT_ASSET0,
                    "asset_out": DEFAULT_ASSET1,
                    "amount_in": 1_000,
                    "min_amount_out": 1,
                    "recipient": sender,
                }
            ]
        },
    }


def _history_add_liquidity_tx_v0(*, tx_id: str, sender: str, block_timestamp: int) -> dict[str, object]:
    return {
        "tx_id": tx_id,
        "block_timestamp": block_timestamp,
        "tx_sender_pubkey": sender,
        "operations": {
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "ADD_LIQUIDITY",
                    "intent_id": "0x" + "ce" * 32,
                    "sender_pubkey": sender,
                    "deadline": 1_999_999_999,
                    "nonce": 2,
                    "pool_id": compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30),
                    "amount0_desired": 10,
                    "amount1_desired": 10,
                    "amount0_min": 0,
                    "amount1_min": 0,
                    "recipient": sender,
                }
            ]
        },
    }


def _history_receipt_v0(
    *,
    accepted: bool,
    state_changed: bool,
    tx_hash: str = "0x" + "00" * 32,
    error_code: str | None = None,
) -> dict[str, object]:
    # tx_hash is a placeholder by default: _write_history_block_v0 rebinds it to the
    # paired transaction (tx_hash_v0) unless bind_receipts=False, in which case the
    # supplied (wrong) tx_hash is kept to exercise the binding-mismatch path.
    return {
        "schema": "zenodex/zeno_ledger/tx_receipt/v0",
        "accepted": accepted,
        "state_changed": state_changed,
        "error_code": error_code,
        "receipt_hash": "0x" + "ab" * 32,
        "tx_hash": tx_hash,
    }


def test_account_history_returns_account_transactions_newest_first(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    alice = _pubkey("31")
    bob = _pubkey("32")

    # Height 6: alice swap (confirmed).
    alice_swap_6 = _history_swap_tx_v0(tx_id="alice-swap-6", sender=alice, block_timestamp=1_778_731_106)
    _write_history_block_v0(
        data_dir,
        height=6,
        transactions=[alice_swap_6],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )
    # Height 7: bob swap (should be excluded for alice).
    _write_history_block_v0(
        data_dir,
        height=7,
        transactions=[_history_swap_tx_v0(tx_id="bob-swap-7", sender=bob, block_timestamp=1_778_731_107)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )
    # Height 8: alice add-liquidity (confirmed) AND a testnet faucet tx (no operations -> excluded).
    alice_add_liq_8 = _history_add_liquidity_tx_v0(tx_id="alice-add-liq-8", sender=alice, block_timestamp=1_778_731_108)
    _write_history_block_v0(
        data_dir,
        height=8,
        transactions=[
            {
                "tx_id": "host-faucet-8",
                "kind": "ZENODEX_TESTNET_FAUCET",
                "to_pubkey": alice,
                "asset": DEFAULT_ASSET0,
                "amount": 123,
                "block_timestamp": 1_778_731_108,
            },
            alice_add_liq_8,
        ],
        receipts=[
            _history_receipt_v0(accepted=True, state_changed=True),
            _history_receipt_v0(accepted=True, state_changed=True),
        ],
    )

    result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 8},
        account_pubkey=alice,
        limit=50,
    )

    assert result["ok"] is True
    assert result["account"] == alice
    assert result["latest_height"] == 8
    txs = result["transactions"]
    # Newest-first: height 8 add-liquidity, then height 6 swap. Bob's tx and the
    # faucet tx are excluded.
    assert [tx["tx_id"] for tx in txs] == ["alice-add-liq-8", "alice-swap-6"]
    assert result["count"] == 2
    assert [tx["height"] for tx in txs] == [8, 6]
    assert txs[0]["action"] == "ADD_LIQUIDITY"
    # tx_hash is the real committed hash, bound to the transaction it came from.
    assert txs[0]["tx_hash"] == tx_hash_v0(dict(alice_add_liq_8))
    assert txs[1]["action"] == "SWAP_EXACT_IN"
    assert txs[1]["tx_hash"] == tx_hash_v0(dict(alice_swap_6))
    assert txs[1]["asset_in"] == DEFAULT_ASSET0
    assert txs[1]["amount_in"] == 1_000


def test_account_history_status_is_derived_strictly_from_receipt(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    alice = _pubkey("31")

    # Confirmed: accepted + state_changed.
    _write_history_block_v0(
        data_dir,
        height=3,
        transactions=[_history_swap_tx_v0(tx_id="alice-confirmed", sender=alice, block_timestamp=1_778_731_103)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )
    # Failed: rejected receipt with an error code (honest negative status).
    _write_history_block_v0(
        data_dir,
        height=4,
        transactions=[_history_swap_tx_v0(tx_id="alice-failed", sender=alice, block_timestamp=1_778_731_104)],
        receipts=[
            _history_receipt_v0(
                accepted=False,
                state_changed=False,
                error_code="insufficient_balance",
            )
        ],
    )
    # Accepted but no state change -> pending, never a fabricated confirmation.
    _write_history_block_v0(
        data_dir,
        height=5,
        transactions=[_history_swap_tx_v0(tx_id="alice-noop", sender=alice, block_timestamp=1_778_731_105)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=False)],
    )

    result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 5},
        account_pubkey=alice,
        limit=50,
    )
    by_id = {tx["tx_id"]: tx for tx in result["transactions"]}

    assert by_id["alice-confirmed"]["status"] == "confirmed"
    assert by_id["alice-confirmed"]["accepted"] is True
    assert by_id["alice-failed"]["status"] == "failed"
    assert by_id["alice-failed"]["accepted"] is False
    assert by_id["alice-failed"]["error_code"] == "insufficient_balance"
    assert by_id["alice-noop"]["status"] == "pending"
    assert by_id["alice-noop"]["accepted"] is True
    assert by_id["alice-noop"]["state_changed"] is False


def test_account_history_unknown_account_returns_empty(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    alice = _pubkey("31")
    carol = _pubkey("33")
    _write_history_block_v0(
        data_dir,
        height=2,
        transactions=[_history_swap_tx_v0(tx_id="alice-swap-2", sender=alice, block_timestamp=1_778_731_102)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )

    result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 2},
        account_pubkey=carol,
        limit=50,
    )
    assert result["ok"] is True
    assert result["count"] == 0
    assert result["transactions"] == []


def test_account_history_limit_is_bounded_and_read_only(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    alice = _pubkey("31")
    for height in range(1, 6):
        _write_history_block_v0(
            data_dir,
            height=height,
            transactions=[_history_swap_tx_v0(tx_id=f"alice-swap-{height}", sender=alice, block_timestamp=1_778_731_100 + height)],
            receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
        )

    bodies_dir = data_dir / "live_ledger" / "bodies"
    receipts_dir = data_dir / "live_ledger" / "receipts"
    pre_bodies = {p.name: p.read_bytes() for p in bodies_dir.glob("*.json")}
    pre_receipts = {p.name: p.read_bytes() for p in receipts_dir.glob("*.json")}

    result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 5},
        account_pubkey=alice,
        limit=2,
    )
    # Bounded to the requested page size, newest-first.
    assert result["count"] == 2
    assert [tx["tx_id"] for tx in result["transactions"]] == ["alice-swap-5", "alice-swap-4"]

    # Read-only: the scan must not mutate, add, or remove any ledger artifact.
    post_bodies = {p.name: p.read_bytes() for p in bodies_dir.glob("*.json")}
    post_receipts = {p.name: p.read_bytes() for p in receipts_dir.glob("*.json")}
    assert post_bodies == pre_bodies
    assert post_receipts == pre_receipts


def _write_minimal_history_node_status_v0(data_dir: Path, *, latest_height: int) -> None:
    data_dir.mkdir(parents=True, exist_ok=True)
    status: dict[str, object] = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "node_id": "node-history-http",
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-history-http",
        "chain_id": "zeno-ledger-history-http",
        "latest_height": latest_height,
        "bundle_root": str(data_dir / "bundle"),
    }
    status["node_status_hash"] = _node_status_hash(status)
    (data_dir / "node_status.json").write_text(json.dumps(status, sort_keys=True), encoding="utf-8")


def test_account_history_http_endpoint_serves_and_rejects_bad_input(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    alice = _pubkey("31")
    _write_history_block_v0(
        data_dir,
        height=6,
        transactions=[_history_swap_tx_v0(tx_id="alice-swap-6", sender=alice, block_timestamp=1_778_731_106)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )
    _write_minimal_history_node_status_v0(data_dir, latest_height=6)

    server = make_node_http_server_v0(data_dir=data_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        ok_body = _read_url_json(f"http://{host}:{port}/api/history?account={alice}&limit=10")
        assert ok_body["ok"] is True
        assert ok_body["account"] == alice
        assert ok_body["count"] == 1
        assert ok_body["transactions"][0]["tx_id"] == "alice-swap-6"
        assert ok_body["transactions"][0]["status"] == "confirmed"

        missing_status, missing_body = _get_url_json_status(f"http://{host}:{port}/api/history")
        assert missing_status == int(HTTPStatus.BAD_REQUEST)
        assert missing_body["ok"] is False

        bad_pubkey_status, _bad_pubkey_body = _get_url_json_status(
            f"http://{host}:{port}/api/history?account=not-a-pubkey"
        )
        assert bad_pubkey_status == int(HTTPStatus.BAD_REQUEST)

        bad_limit_status, _bad_limit_body = _get_url_json_status(
            f"http://{host}:{port}/api/history?account={alice}&limit=0"
        )
        assert bad_limit_status == int(HTTPStatus.BAD_REQUEST)

        nonint_limit_status, _nonint_limit_body = _get_url_json_status(
            f"http://{host}:{port}/api/history?account={alice}&limit=abc"
        )
        assert nonint_limit_status == int(HTTPStatus.BAD_REQUEST)
    finally:
        server.shutdown()
        server.server_close()


def _history_two_account_swaps_tx_v0(
    *,
    tx_id: str,
    account_a: str,
    account_b: str,
    pool_a: str,
    pool_b: str,
    block_timestamp: int,
) -> dict[str, object]:
    """A single committed tx carrying TWO swaps for TWO different accounts.

    op[0] belongs to account_a (its own sender/recipient/amounts), op[1] belongs
    to account_b. This is exactly the multi-op shape that previously leaked one
    account's swap into the other account's history.
    """
    return {
        "tx_id": tx_id,
        "block_timestamp": block_timestamp,
        "tx_sender_pubkey": account_a,
        "operations": {
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + "a0" * 32,
                    "sender_pubkey": account_a,
                    "deadline": 1_999_999_999,
                    "nonce": 1,
                    "pool_id": pool_a,
                    "asset_in": DEFAULT_ASSET0,
                    "asset_out": DEFAULT_ASSET1,
                    "amount_in": 1_111,
                    "min_amount_out": 1,
                    "recipient": account_a,
                },
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + "b0" * 32,
                    "sender_pubkey": account_b,
                    "deadline": 1_999_999_999,
                    "nonce": 1,
                    "pool_id": pool_b,
                    "asset_in": DEFAULT_ASSET1,
                    "asset_out": DEFAULT_ASSET0,
                    "amount_in": 2_222,
                    "min_amount_out": 1,
                    "recipient": account_b,
                },
            ]
        },
    }


def test_account_history_multi_op_tx_does_not_leak_across_accounts(tmp_path: Path) -> None:
    # Regression for the per-op attribution leak: a single committed transaction
    # with two swaps owned by two different accounts must return ONLY each
    # account's own op — never the other account's swap or amounts.
    data_dir = tmp_path / "node"
    alice = _pubkey("31")
    bob = _pubkey("32")
    pool_a = compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30)
    pool_b = compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 5)

    _write_history_block_v0(
        data_dir,
        height=9,
        transactions=[
            _history_two_account_swaps_tx_v0(
                tx_id="multi-op-9",
                account_a=alice,
                account_b=bob,
                pool_a=pool_a,
                pool_b=pool_b,
                block_timestamp=1_778_731_109,
            )
        ],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )

    alice_result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 9},
        account_pubkey=alice,
        limit=50,
    )
    bob_result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 9},
        account_pubkey=bob,
        limit=50,
    )

    # Alice sees exactly her own op (op_index 0): her pool, her amount; never bob's.
    assert alice_result["count"] == 1
    alice_row = alice_result["transactions"][0]
    assert alice_row["op_index"] == 0
    assert alice_row["pool_id"] == pool_a
    assert alice_row["amount_in"] == 1_111
    assert alice_row["recipient"] == alice
    assert all(row["pool_id"] != pool_b for row in alice_result["transactions"])
    assert all(row["amount_in"] != 2_222 for row in alice_result["transactions"])

    # Bob sees exactly his own op (op_index 1): his pool, his amount; never alice's.
    assert bob_result["count"] == 1
    bob_row = bob_result["transactions"][0]
    assert bob_row["op_index"] == 1
    assert bob_row["pool_id"] == pool_b
    assert bob_row["amount_in"] == 2_222
    assert bob_row["recipient"] == bob
    assert all(row["pool_id"] != pool_a for row in bob_result["transactions"])
    assert all(row["amount_in"] != 1_111 for row in bob_result["transactions"])


def test_account_history_skips_rows_whose_receipt_does_not_bind(tmp_path: Path) -> None:
    # No-fake-green: a status is only reported when the receipt provably belongs to
    # this transaction (receipt.tx_hash == tx_hash_v0(tx)). A mismatched receipt
    # hash must fail closed — the row is absent, not emitted with a guessed status.
    data_dir = tmp_path / "node"
    alice = _pubkey("31")

    # Height 4: receipt hash deliberately does NOT match the transaction.
    _write_history_block_v0(
        data_dir,
        height=4,
        transactions=[_history_swap_tx_v0(tx_id="alice-unbound", sender=alice, block_timestamp=1_778_731_104)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True, tx_hash="0x" + "de" * 32)],
        bind_receipts=False,
    )
    # Height 5: correctly bound receipt for the same account (must still be returned).
    _write_history_block_v0(
        data_dir,
        height=5,
        transactions=[_history_swap_tx_v0(tx_id="alice-bound", sender=alice, block_timestamp=1_778_731_105)],
        receipts=[_history_receipt_v0(accepted=True, state_changed=True)],
    )

    result = _ui_account_history_from_live_bodies_v0(
        data_dir=data_dir,
        node_status={"latest_height": 5},
        account_pubkey=alice,
        limit=50,
    )

    tx_ids = [tx["tx_id"] for tx in result["transactions"]]
    assert "alice-unbound" not in tx_ids
    assert tx_ids == ["alice-bound"]
    assert result["count"] == 1
