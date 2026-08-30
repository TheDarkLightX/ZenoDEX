#!/usr/bin/env python3
"""Build a runnable core ZenoLedger feature suite."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_feature_suite import (  # noqa: E402
    build_feature_suite_manifest_v0,
)
from tools.zeno_ledger_make_feature_lane import (  # noqa: E402
    build_feature_lane_manifest_v0,
)
from tools.zeno_ledger_make_testnet_bundle import (  # noqa: E402
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
    _body_with_transaction_v0,
    build_testnet_bundle_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.make_core_feature_suite_report.v0"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _resolve_manifest_path(manifest_path: Path, path_text: object, *, name: str) -> Path:
    if not isinstance(path_text, str) or path_text == "":
        raise ValueError(f"{name} must be a non-empty string")
    path = Path(path_text)
    if path.is_absolute():
        return path
    if ".." in path.parts:
        raise ValueError(f"{name} must not escape its manifest root")
    return manifest_path.parent / path


def _zusd_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    tag: str,
    args: dict[str, Any],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "zusd_commands": [{"tag": tag, "args": args}],
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_zusd_cutoff_v0",
    )


def _perp_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    action: str,
    params: dict[str, Any],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "perp_commands": [{"action": action, "params": params}],
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_perp_cutoff_v0",
    )


def _oracle_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    action: str,
    args: dict[str, Any],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "oracle_commands": [{"action": action, "args": args}],
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_oracle_cutoff_v0",
    )


def _oracle_reporter_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "oracle_reporter_commands": commands,
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_oracle_reporter_cutoff_v0",
    )


def _upba_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "upba_commands": commands,
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_upba_cutoff_v0",
    )


def _proof_mining_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "proof_mining_commands": commands,
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_proof_mining_cutoff_v0",
    )


def _autotrader_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "autotrader_commands": commands,
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_autotrader_cutoff_v0",
    )


def _confidential_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx_id: str,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    tx = {
        "tx_id": tx_id,
        "block_timestamp": max(0, int(time_ms) // 1000),
        "confidential_commands": commands,
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
        policy_id="core_suite_confidential_cutoff_v0",
    )


def build_core_feature_suite_v0(
    *,
    out_dir: Path,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
) -> dict[str, Any]:
    bootstrap_dir = out_dir / "spot_bootstrap"
    zusd_dir = out_dir / "zusd_core"
    perp_dir = out_dir / "perp_core"
    oracle_dir = out_dir / "oracle_core"
    oracle_reporter_dir = out_dir / "oracle_reporter_core"
    upba_dir = out_dir / "upba_core"
    proof_mining_dir = out_dir / "proof_mining_core"
    autotrader_dir = out_dir / "autotrader_core"
    confidential_dir = out_dir / "confidential_core"
    suite_path = out_dir / "feature_suite.json"

    bootstrap_report = build_testnet_bundle_v0(
        out_dir=bootstrap_dir,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms,
        token_symbol=token_symbol,
        proof_required=False,
    )
    bootstrap_manifest_path = Path(str(bootstrap_report["manifest_path"]))
    bootstrap_manifest = bootstrap_report["manifest"]
    bootstrap_profile_path = _resolve_manifest_path(
        bootstrap_manifest_path,
        bootstrap_manifest.get("profile_path"),
        name="bootstrap_manifest.profile_path",
    )

    from src.core.zusd import E8, init_state

    zusd_state_path = zusd_dir / "source" / "zusd_state.json"
    zusd_state_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(zusd_state_path, dict(init_state().__dict__))
    zusd_body_paths: list[Path] = []
    zusd_bodies = [
        _zusd_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-zusd-bootstrap-oracle-v0",
            tag="bootstrap_oracle",
            args={"price_e8": 100 * E8, "auth_ok": True},
        ),
        _zusd_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-zusd-deposit-collateral-v0",
            tag="deposit_collateral",
            args={"amount_e8": 2 * E8},
        ),
        _zusd_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-zusd-mint-v0",
            tag="mint_zusd",
            args={"amount_e8": 100 * E8},
        ),
        _zusd_body_v0(
            chain_id=chain_id,
            height=4,
            time_ms=time_ms + 3_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-zusd-rejected-withdraw-v0",
            tag="withdraw_collateral",
            args={"amount_e8": 10 * E8},
        ),
    ]
    for index, body in enumerate(zusd_bodies, start=1):
        path = zusd_dir / "source" / f"zusd_body_{index}.json"
        _write_json(path, body)
        zusd_body_paths.append(path)
    zusd_lane_report = build_feature_lane_manifest_v0(
        out_dir=zusd_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=zusd_state_path,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=zusd_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    zusd_manifest_path = Path(str(zusd_lane_report["manifest_path"]))

    from src.core.perp_epoch import perp_epoch_isolated_default_initial_state

    perp_state_path = perp_dir / "source" / "perp_state.json"
    perp_state_path.parent.mkdir(parents=True, exist_ok=True)
    perp_state = perp_epoch_isolated_default_initial_state()
    perp_state["oracle_seen"] = True
    perp_state["oracle_last_update_epoch"] = 0
    perp_state["index_price_e8"] = 100_000_000
    _write_json(perp_state_path, perp_state)
    perp_body_paths: list[Path] = []
    perp_bodies = [
        _perp_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-perp-deposit-collateral-v0",
            action="deposit_collateral",
            params={"amount": 20_000, "auth_ok": True},
        ),
        _perp_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-perp-set-position-v0",
            action="set_position",
            params={"new_position_base": 100_000, "auth_ok": True},
        ),
        _perp_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-perp-advance-epoch-v0",
            action="advance_epoch",
            params={"delta": 1},
        ),
        _perp_body_v0(
            chain_id=chain_id,
            height=4,
            time_ms=time_ms + 3_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-perp-apply-funding-v0",
            action="apply_funding",
            params={"new_rate_bps": 50, "auth_ok": True},
        ),
        _perp_body_v0(
            chain_id=chain_id,
            height=5,
            time_ms=time_ms + 4_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-perp-rejected-withdraw-v0",
            action="withdraw_collateral",
            params={"amount": 999_999, "auth_ok": True},
        ),
    ]
    for index, body in enumerate(perp_bodies, start=1):
        path = perp_dir / "source" / f"perp_body_{index}.json"
        _write_json(path, body)
        perp_body_paths.append(path)
    perp_lane_report = build_feature_lane_manifest_v0(
        out_dir=perp_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=perp_state_path,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=perp_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    perp_manifest_path = Path(str(perp_lane_report["manifest_path"]))

    from src.core.oracle import init_oracle_state

    oracle_state_path = oracle_dir / "source" / "oracle_state.json"
    oracle_state_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(oracle_state_path, dict(init_oracle_state(max_staleness_seconds=300).__dict__))
    oracle_body_paths: list[Path] = []
    oracle_bodies = [
        _oracle_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-update-v0",
            action="update_price_timestamp",
            args={"current_timestamp": 100},
        ),
        _oracle_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-require-fresh-v0",
            action="require_fresh",
            args={"current_timestamp": 350},
        ),
        _oracle_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-rejected-stale-v0",
            action="require_fresh",
            args={"current_timestamp": 401},
        ),
    ]
    for index, body in enumerate(oracle_bodies, start=1):
        path = oracle_dir / "source" / f"oracle_body_{index}.json"
        _write_json(path, body)
        oracle_body_paths.append(path)
    oracle_lane_report = build_feature_lane_manifest_v0(
        out_dir=oracle_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=oracle_state_path,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=oracle_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    oracle_manifest_path = Path(str(oracle_lane_report["manifest_path"]))

    from tools.zenodex_oracle_reporter_lifecycle import sample_lifecycle
    from tools.zenodex_oracle_reporter_token_settlement_replay import sample_settlement_replay

    oracle_reporter_state_path = oracle_reporter_dir / "source" / "oracle_reporter_state.json"
    oracle_reporter_state_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(
        oracle_reporter_state_path,
        {
            "schema": "zenodex/oracle_reporter_ledger_state/v1",
            "accepted_lifecycle_count": 0,
            "accepted_token_settlement_count": 0,
            "last_result": None,
            "last_token_settlement_result": None,
        },
    )
    oracle_reporter_good_trace = sample_lifecycle()
    oracle_reporter_bad_trace = json.loads(json.dumps(oracle_reporter_good_trace))
    oracle_reporter_bad_trace["events"] = [
        {
            "type": "submit_report",
            "epoch": 1,
            "report_id": oracle_reporter_good_trace["events"][2]["report_id"],
            "query_id": oracle_reporter_good_trace["events"][2]["query_id"],
            "value_hash": oracle_reporter_good_trace["events"][2]["value_hash"],
        }
    ]
    oracle_reporter_good_settlement = sample_settlement_replay()
    oracle_reporter_bad_settlement = json.loads(json.dumps(oracle_reporter_good_settlement))
    oracle_reporter_bad_settlement["policy"]["approved"] = False
    oracle_reporter_body_paths: list[Path] = []
    oracle_reporter_bodies = [
        _oracle_reporter_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-reporter-lifecycle-v0",
            commands=[
                {
                    "action": "verify_lifecycle_trace",
                    "args": {"trace": oracle_reporter_good_trace},
                }
            ],
        ),
        _oracle_reporter_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-reporter-rejected-v0",
            commands=[
                {
                    "action": "verify_lifecycle_trace",
                    "args": {"trace": oracle_reporter_bad_trace},
                }
            ],
        ),
        _oracle_reporter_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-reporter-token-settlement-v0",
            commands=[
                {
                    "action": "verify_token_settlement_replay",
                    "args": {"replay": oracle_reporter_good_settlement},
                }
            ],
        ),
        _oracle_reporter_body_v0(
            chain_id=chain_id,
            height=4,
            time_ms=time_ms + 3_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-oracle-reporter-token-settlement-rejected-v0",
            commands=[
                {
                    "action": "verify_token_settlement_replay",
                    "args": {"replay": oracle_reporter_bad_settlement},
                }
            ],
        ),
    ]
    for index, body in enumerate(oracle_reporter_bodies, start=1):
        path = oracle_reporter_dir / "source" / f"oracle_reporter_body_{index}.json"
        _write_json(path, body)
        oracle_reporter_body_paths.append(path)
    oracle_reporter_lane_report = build_feature_lane_manifest_v0(
        out_dir=oracle_reporter_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=oracle_reporter_state_path,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=oracle_reporter_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    oracle_reporter_manifest_path = Path(str(oracle_reporter_lane_report["manifest_path"]))

    from tools.zeno_ledger_run_local import _load_upba_ref_v0

    upba_state_path = upba_dir / "source" / "upba_state.json"
    upba_state_path.parent.mkdir(parents=True, exist_ok=True)
    upba_ref = _load_upba_ref_v0()
    _write_json(upba_state_path, dict(upba_ref.init_state().__dict__))
    upba_body_paths: list[Path] = []
    upba_bodies = [
        _upba_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-add-intents-v0",
            commands=[
                {
                    "tag": "add_intent",
                    "args": {"amount_in": 100, "min_amount_out": 70, "auth_ok": True},
                },
                {
                    "tag": "add_intent",
                    "args": {"amount_in": 50, "min_amount_out": 30, "auth_ok": True},
                },
            ],
        ),
        _upba_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-close-collection-v0",
            commands=[{"tag": "close_collection", "args": {"operator_auth": True}}],
        ),
        _upba_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-submit-solution-v0",
            commands=[
                {
                    "tag": "submit_solution",
                    "args": {
                        "solver_id": 1,
                        "proposed_clearing_price_bps": 7333,
                        "surplus_extracted_bps": 2666,
                        "clearing_valid_witness": True,
                    },
                }
            ],
        ),
        _upba_body_v0(
            chain_id=chain_id,
            height=4,
            time_ms=time_ms + 3_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-finalize-winner-v0",
            commands=[{"tag": "finalize_winner", "args": {"operator_auth": True}}],
        ),
        _upba_body_v0(
            chain_id=chain_id,
            height=5,
            time_ms=time_ms + 4_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-execute-fills-v0",
            commands=[
                {
                    "tag": "execute_fill",
                    "args": {
                        "fill_input_amount": 100,
                        "fill_output_amount": 75,
                        "fill_min_guaranteed": 70,
                        "fill_valid_witness": True,
                    },
                },
                {
                    "tag": "execute_fill",
                    "args": {
                        "fill_input_amount": 50,
                        "fill_output_amount": 35,
                        "fill_min_guaranteed": 30,
                        "fill_valid_witness": True,
                    },
                },
            ],
        ),
        _upba_body_v0(
            chain_id=chain_id,
            height=6,
            time_ms=time_ms + 5_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-upba-complete-batch-v0",
            commands=[
                {
                    "tag": "complete_batch",
                    "args": {
                        "protocol_fee_amount": 40,
                        "solver_reward_amount": 0,
                        "conservation_witness": True,
                    },
                }
            ],
        ),
    ]
    for index, body in enumerate(upba_bodies, start=1):
        path = upba_dir / "source" / f"upba_body_{index}.json"
        _write_json(path, body)
        upba_body_paths.append(path)
    upba_lane_report = build_feature_lane_manifest_v0(
        out_dir=upba_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=upba_state_path,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=upba_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    upba_manifest_path = Path(str(upba_lane_report["manifest_path"]))

    from src.core.proof_mining_claims import build_proof_mining_claim, explicit_proposal_hash
    from src.core.proof_mining_manager import ProofMiningManagerSnapshot
    from src.integration.proof_mining_context import ProofMiningContext, proof_mining_context_to_obj
    from src.integration.proof_mining_runtime import (
        ProofMiningRuntimeState,
        proof_mining_runtime_state_to_obj,
    )

    proof_mining_state_path = proof_mining_dir / "source" / "proof_mining_state.json"
    proof_mining_state_path.parent.mkdir(parents=True, exist_ok=True)
    proof_mining_state = ProofMiningRuntimeState(
        reward_pool_pubkey="proof-mining-pool",
        snapshot=ProofMiningManagerSnapshot(
            epoch=1,
            base_reward=8,
            initial_pool=20,
            reward_pool_balance=20,
            total_paid=0,
            claimed_slots={},
        ),
    )
    _write_json(proof_mining_state_path, proof_mining_runtime_state_to_obj(proof_mining_state))
    witness_hash = "sha256:core-suite-proof-mining-witness"
    prev_state_hash = "sha256:core-suite-proof-mining-prev"
    batch_hash = "sha256:core-suite-proof-mining-batch"
    dex_hash_after = "sha256:core-suite-proof-mining-after"
    proof_mining_proposal_hash = explicit_proposal_hash(
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
    )
    proof_mining_context = ProofMiningContext(
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
        proposal_hash=proof_mining_proposal_hash,
        proof_scheme="zeno-ledger-core-suite-proof-v0",
    )
    proof_mining_claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "core-suite-proof-mining-job",
            "winner": {
                "miner_id": "proof-miner-0",
                "witness_sha256": witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="core-suite-proof-mining-round-v0",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )
    proof_mining_duplicate_claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "core-suite-proof-mining-job",
            "winner": {
                "miner_id": "proof-miner-0",
                "witness_sha256": witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="core-suite-proof-mining-round-v1",
        reward_pool_before=16,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )
    proof_mining_body_paths: list[Path] = []
    proof_mining_bodies = [
        _proof_mining_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-proof-mining-submit-v0",
            commands=[
                {
                    "action": "submit_claim",
                    "args": {
                        "claim_artifact": proof_mining_claim,
                        "proof_mining_context": proof_mining_context_to_obj(proof_mining_context),
                        "actual_reward_pool_balance": 20,
                    },
                }
            ],
        ),
        _proof_mining_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-proof-mining-duplicate-rejected-v0",
            commands=[
                {
                    "action": "submit_claim",
                    "args": {
                        "claim_artifact": proof_mining_duplicate_claim,
                        "proof_mining_context": proof_mining_context_to_obj(proof_mining_context),
                        "actual_reward_pool_balance": 16,
                    },
                }
            ],
        ),
    ]
    for index, body in enumerate(proof_mining_bodies, start=1):
        path = proof_mining_dir / "source" / f"proof_mining_body_{index}.json"
        _write_json(path, body)
        proof_mining_body_paths.append(path)
    proof_mining_lane_report = build_feature_lane_manifest_v0(
        out_dir=proof_mining_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=proof_mining_state_path,
        autotrader_state_path=None,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=proof_mining_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    proof_mining_manifest_path = Path(str(proof_mining_lane_report["manifest_path"]))

    from src.agents.strategy_ir import (
        NotionalCaps,
        PolicyBackend,
        RiskLimits,
        StrategyAction,
        StrategyControls,
        StrategyIR,
        StrategyTemplate,
        StrategyWindow,
    )
    from src.core.quote_receipts import make_route_quote_receipt
    from src.core.routing import best_route_exact_in_2hop
    from src.integration.autotrader_controller import AutoTraderControllerState
    from src.state.pools import PoolState, PoolStatus
    from tools.zeno_ledger_run_local import _autotrader_controller_state_to_obj, _pool_state_to_obj

    autotrader_state_path = autotrader_dir / "source" / "autotrader_state.json"
    autotrader_state_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(autotrader_state_path, _autotrader_controller_state_to_obj(AutoTraderControllerState()))
    autotrader_strategy = StrategyIR(
        strategy_id="core.autotrader.dca.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("A", "B"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(
            per_order_max=100,
            per_window_max=500,
            lifetime_max=1_000,
        ),
        risk_limits=RiskLimits(
            max_slippage_bps=50,
            max_oracle_staleness_epochs=3,
        ),
        strategy_window=StrategyWindow(
            valid_from_epoch=1,
            valid_until_epoch=100,
            min_order_spacing_epochs=0,
        ),
        controls=StrategyControls(
            kill_switch_enabled=True,
            max_live_orders=3,
        ),
        template_params={
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "A",
            "asset_out": "B",
        },
        tau_policy_specs=(),
    )
    autotrader_pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    autotrader_quote = best_route_exact_in_2hop(
        pools_by_id=autotrader_pools,
        asset_in="A",
        asset_out="B",
        amount_in=100,
    )
    if autotrader_quote is None:
        raise RuntimeError("core autotrader quote construction failed")
    autotrader_receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=autotrader_quote,
        pools_by_id=autotrader_pools,
        quote_epoch=5,
    )
    autotrader_bad_receipt = json.loads(json.dumps(autotrader_receipt))
    autotrader_bad_receipt["body"]["amount_in"] = 90
    autotrader_pools_obj = {
        pool_id: _pool_state_to_obj(pool)
        for pool_id, pool in autotrader_pools.items()
    }
    autotrader_body_paths: list[Path] = []
    autotrader_bodies = [
        _autotrader_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-autotrader-submit-v0",
            commands=[
                {
                    "action": "evaluate_quote_receipt",
                    "args": {
                        "strategy": autotrader_strategy.to_dict(),
                        "receipt": autotrader_receipt,
                        "pools_by_id": autotrader_pools_obj,
                        "current_epoch": 5,
                        "intent_deadline": 99,
                    },
                }
            ],
        ),
        _autotrader_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-autotrader-stale-skip-v0",
            commands=[
                {
                    "action": "evaluate_quote_receipt",
                    "args": {
                        "strategy": autotrader_strategy.to_dict(),
                        "receipt": autotrader_receipt,
                        "pools_by_id": autotrader_pools_obj,
                        "current_epoch": 9,
                        "intent_deadline": 99,
                    },
                }
            ],
        ),
        _autotrader_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-autotrader-rejected-amount-v0",
            commands=[
                {
                    "action": "evaluate_quote_receipt",
                    "args": {
                        "strategy": autotrader_strategy.to_dict(),
                        "receipt": autotrader_bad_receipt,
                        "pools_by_id": autotrader_pools_obj,
                        "current_epoch": 9,
                        "intent_deadline": 99,
                    },
                }
            ],
        ),
    ]
    for index, body in enumerate(autotrader_bodies, start=1):
        path = autotrader_dir / "source" / f"autotrader_body_{index}.json"
        _write_json(path, body)
        autotrader_body_paths.append(path)
    autotrader_lane_report = build_feature_lane_manifest_v0(
        out_dir=autotrader_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=autotrader_state_path,
        confidential_state_path=None,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=autotrader_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    autotrader_manifest_path = Path(str(autotrader_lane_report["manifest_path"]))

    from src.core.confidential_extension_receipts import make_confidential_extension_receipt
    from src.core.fhe_sealed_bid_alpha import FHECipherBid, compile_fhe_sealed_bid_alpha_plan
    from src.core.sealed_bid_auction import RevealedSealedBid

    confidential_state_path = confidential_dir / "source" / "confidential_state.json"
    confidential_state_path.parent.mkdir(parents=True, exist_ok=True)
    nitro_pcr0 = "a" * 96
    nitro_pcr8 = "b" * 96
    confidential_measurement = f"nitro:pcr0:{nitro_pcr0}:pcr8:{nitro_pcr8}"
    policy_digest = "0x" + ("d" * 64)
    confidential_receipt = make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-core-confidential-1",
        policy_version="tee-policy-v1",
        policy_digest=policy_digest,
        measurement=confidential_measurement,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    plain_bids = [
        RevealedSealedBid("alice", "c1", 3, 10),
        RevealedSealedBid("bob", "c2", 4, 9),
        RevealedSealedBid("carol", "c3", 2, 11),
    ]
    cipher_bids = [
        FHECipherBid("alice", "c1", "ct:q:alice", "ct:p:alice"),
        FHECipherBid("bob", "c2", "ct:q:bob", "ct:p:bob"),
        FHECipherBid("carol", "c3", "ct:q:carol", "ct:p:carol"),
    ]
    fhe_receipt = compile_fhe_sealed_bid_alpha_plan(
        auction_id="core-suite-fhe-auction-v0",
        units_for_sale=5,
        bids=plain_bids,
        cipher_bids=cipher_bids,
        key_id="fhe-key-1",
    )
    _write_json(
        confidential_state_path,
        {
            "schema": "zenodex/confidential_ledger_state/v1",
            "approved_measurements": [confidential_measurement],
            "approved_fhe_key_ids": ["fhe-key-1"],
            "expected_policy_digest": policy_digest,
            "used_requests": [],
            "accepted_live_admission_count": 0,
            "accepted_fhe_plan_count": 0,
            "last_receipt_hash": None,
            "last_fhe_receipt_hash": None,
            "last_auction_id": None,
        },
    )
    confidential_body_paths: list[Path] = []
    confidential_bodies = [
        _confidential_body_v0(
            chain_id=chain_id,
            height=1,
            time_ms=time_ms,
            sequencer_id=sequencer_id,
            tx_id="core-suite-confidential-live-admission-v0",
            commands=[
                {
                    "action": "validate_live_admission",
                    "args": {"receipt": confidential_receipt},
                }
            ],
        ),
        _confidential_body_v0(
            chain_id=chain_id,
            height=2,
            time_ms=time_ms + 1_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-confidential-fhe-plan-v0",
            commands=[
                {
                    "action": "verify_fhe_alpha_plan",
                    "args": {
                        "receipt": fhe_receipt,
                        "trusted_plain_bids": [dict(bid.__dict__) for bid in plain_bids],
                    },
                }
            ],
        ),
        _confidential_body_v0(
            chain_id=chain_id,
            height=3,
            time_ms=time_ms + 2_000,
            sequencer_id=sequencer_id,
            tx_id="core-suite-confidential-replay-rejected-v0",
            commands=[
                {
                    "action": "validate_live_admission",
                    "args": {"receipt": confidential_receipt},
                }
            ],
        ),
    ]
    for index, body in enumerate(confidential_bodies, start=1):
        path = confidential_dir / "source" / f"confidential_body_{index}.json"
        _write_json(path, body)
        confidential_body_paths.append(path)
    confidential_lane_report = build_feature_lane_manifest_v0(
        out_dir=confidential_dir,
        profile_path=bootstrap_profile_path,
        genesis_snapshot_path=None,
        tau_app_state_path=None,
        zusd_state_path=None,
        perp_state_path=None,
        oracle_state_path=None,
        oracle_reporter_state_path=None,
        upba_state_path=None,
        proof_mining_state_path=None,
        autotrader_state_path=None,
        confidential_state_path=confidential_state_path,
        tau_chain_balances_path=None,
        tau_chain_id=None,
        tau_enable_faucet=False,
        body_paths=confidential_body_paths,
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        allow_missing_settlement=True,
        disable_intent_signatures=True,
    )
    confidential_manifest_path = Path(str(confidential_lane_report["manifest_path"]))

    suite = build_feature_suite_manifest_v0(
        suite_name="ZenoLedger core feature suite",
        lanes=[
            ("spot_bootstrap", bootstrap_manifest_path),
            ("zusd_core", zusd_manifest_path),
            ("perp_core", perp_manifest_path),
            ("oracle_core", oracle_manifest_path),
            ("oracle_reporter_core", oracle_reporter_manifest_path),
            ("upba_core", upba_manifest_path),
            ("proof_mining_core", proof_mining_manifest_path),
            ("autotrader_core", autotrader_manifest_path),
            ("confidential_core", confidential_manifest_path),
        ],
        required_features=[
            "spot_bootstrap",
            "zusd_core",
            "perp_core",
            "oracle_core",
            "oracle_reporter_core",
            "upba_core",
            "proof_mining_core",
            "autotrader_core",
            "confidential_core",
        ],
        base_dir=suite_path.parent,
    )
    _write_json(suite_path, suite)
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "suite_path": str(suite_path),
        "feature_suite_hash": suite["feature_suite_hash"],
        "feature_count": suite["feature_count"],
        "spot_bootstrap_manifest_path": str(bootstrap_manifest_path),
        "zusd_core_manifest_path": str(zusd_manifest_path),
        "perp_core_manifest_path": str(perp_manifest_path),
        "oracle_core_manifest_path": str(oracle_manifest_path),
        "oracle_reporter_core_manifest_path": str(oracle_reporter_manifest_path),
        "upba_core_manifest_path": str(upba_manifest_path),
        "proof_mining_core_manifest_path": str(proof_mining_manifest_path),
        "autotrader_core_manifest_path": str(autotrader_manifest_path),
        "confidential_core_manifest_path": str(confidential_manifest_path),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a runnable core ZenoLedger feature suite")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    args = parser.parse_args(argv)

    try:
        report = build_core_feature_suite_v0(
            out_dir=args.out_dir,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
        )
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
