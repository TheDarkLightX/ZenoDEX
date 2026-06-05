"""Node append path must pass through the state-root transition validator.

The lower-level block builder already checks that ``header.pre_state_root`` and
``header.post_state_root`` match deterministic body re-execution. This file pins
that check to the node append entrypoint so the assurance receipt cannot clear a
runtime-invariant column with a validator that only works as a standalone helper.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.zeno_ledger_node as node
from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_v0 import (
    build_header_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    dex_state_root_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import append_dex_transaction_v0, append_testnet_faucet_v0

ZERO_ROOT = "0x" + "00" * 32
_CHAIN_ID = "zeno-ledger-node-state-root-binding"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _init_node(tmp_path: Path) -> Path:
    # Keep this fixture narrow. The reviewed behavior is the live append
    # root guard, so building the full public-testnet feature suite would turn a
    # runtime-invariant regression into a slow integration rehearsal.
    bundle_root = tmp_path / "bundle"
    bootstrap_root = bundle_root / "bootstrap"
    _write_json(
        bundle_root / "public_testnet_manifest.json",
        {
            "schema": "zenodex.zeno_ledger.public_testnet_bundle.v0",
            "network_id": _CHAIN_ID,
            "chain_id": _CHAIN_ID,
            "sequencer_id": "sequencer-node-state-root-binding",
            "bootstrap_manifest_path": "bootstrap/manifest.json",
        },
    )
    _write_json(
        bootstrap_root / "manifest.json",
        {
            "schema": "zenodex.zeno_ledger.bootstrap_manifest.v0",
            "sequencer_set_hash": ZERO_ROOT,
            "config_digest": ZERO_ROOT,
            "module_versions_digest": ZERO_ROOT,
        },
    )
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    empty_snapshot = snapshot_from_state(empty_state).data
    empty_root = dex_state_root_v0(empty_state)
    app_hash = compute_app_hash_v0(
        {
            "chain_id": _CHAIN_ID,
            "height": 0,
            "post_state_root": empty_root,
            "evidence_root": ZERO_ROOT,
            "config_digest": ZERO_ROOT,
            "module_versions_digest": ZERO_ROOT,
        }
    )
    header = build_header_v0(
        chain_id=_CHAIN_ID,
        height=0,
        time_ms=1_778_730_123_000,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=ZERO_ROOT,
        ingress_root=ZERO_ROOT,
        tx_root=ZERO_ROOT,
        pre_state_root=empty_root,
        post_state_root=empty_root,
        app_hash=app_hash,
        evidence_root=ZERO_ROOT,
        body_root=ZERO_ROOT,
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=ZERO_ROOT,
        module_versions_digest=ZERO_ROOT,
        signature_set_root=ZERO_ROOT,
    )
    _write_json(bootstrap_root / "ledger" / "headers" / "0.json", header)
    _write_json(bootstrap_root / "ledger" / "snapshots" / "0.json", empty_snapshot)

    node_dir = tmp_path / "node"
    node_dir.mkdir()
    status = {
        "schema": node.NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": "node-state-root-binding",
        "node_role": "follower_watcher",
        "network_id": _CHAIN_ID,
        "chain_id": _CHAIN_ID,
        "bundle_root": str(bundle_root),
        "data_dir": str(node_dir),
        "latest_height": 0,
        "last_header_hash": canonical_header_hash_v0(header),
        "last_app_hash": app_hash,
    }
    _write_json(node_dir / "node_status.json", {**status, "node_status_hash": node._node_status_hash(status)})
    return node_dir


def test_append_dex_transaction_wires_state_root_transition_validator(
    tmp_path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # REVIEW [B- -> A-]: the state-root validator was previously strong in
    # isolation, but a reviewer found that isolation is not enough for a runtime
    # invariant claim. This pins the ordinary node DEX append lane to the live
    # block builder's transition validator. Tokenomics sidecar rewrites remain a
    # separate reviewed residual and must not be counted by this test.
    calls: list[dict[str, object]] = []

    def fail_if_called(**kwargs):
        calls.append(dict(kwargs))
        raise ValueError("node append reached state-root transition validator")

    monkeypatch.setattr(
        "tools.zeno_ledger_run_local.validate_block_state_transition_v0",
        fail_if_called,
    )
    node_dir = _init_node(tmp_path)

    tx = {
        "tx_id": "node-state-root-binding-empty-dex-tx-v0",
        "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "operations": {},
    }
    with pytest.raises(ValueError, match="node append reached state-root transition validator"):
        append_dex_transaction_v0(
            data_dir=node_dir,
            tx=tx,
            time_ms=1_778_731_123_000,
        )

    assert len(calls) == 1
    assert calls[0]["header"]["chain_id"] == _CHAIN_ID
    assert calls[0]["body"]["transactions"][0]["tx_id"] == tx["tx_id"]


def test_append_faucet_rejects_forged_post_state_root_before_live_pointer(
    tmp_path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # REVIEW [C -> A-]: this is the concrete audit corruption. The forged block
    # recomputes app_hash and header_hash around a bad post_state_root, so the
    # node must reject by comparing the committed root to the actual post-state
    # file before live_state.json advances.
    node_dir = _init_node(tmp_path)
    original_builder = node._build_faucet_block_from_body_v0

    def forged_post_root_builder(**kwargs):
        report = dict(original_builder(**kwargs))
        header_path = Path(str(report["header_path"]))
        header = json.loads(header_path.read_text(encoding="utf-8"))
        header["post_state_root"] = ZERO_ROOT
        header["app_hash"] = compute_app_hash_v0(
            {
                "chain_id": header["chain_id"],
                "height": header["height"],
                "post_state_root": header["post_state_root"],
                "evidence_root": header["evidence_root"],
                "config_digest": header["config_digest"],
                "module_versions_digest": header["module_versions_digest"],
            }
        )
        header_path.write_text(json.dumps(header, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        report["app_hash"] = header["app_hash"]
        report["header_hash"] = canonical_header_hash_v0(header)
        return report

    monkeypatch.setattr(node, "_build_faucet_block_from_body_v0", forged_post_root_builder)

    with pytest.raises(ValueError, match="post_state_root does not match post snapshot"):
        append_testnet_faucet_v0(
            data_dir=node_dir,
            to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
            asset=DEFAULT_ASSET0,
            amount=1,
            time_ms=1_778_731_123_000,
            tx_id="forged-post-root-faucet-v0",
        )

    assert not (node_dir / "live_state.json").exists()
    assert not (node_dir / "live_ledger" / "headers" / "1.json").exists()


def test_failed_live_block_validation_discards_app_state_artifact(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    app_state = data_dir / "live_ledger" / "app_states" / "1.json"
    app_state.parent.mkdir(parents=True)
    app_state.write_text("{}\n", encoding="utf-8")

    node._discard_replayed_block_artifacts_v0(
        data_dir=data_dir,
        block_report={"post_app_state_path": str(app_state)},
    )

    assert not app_state.exists()
