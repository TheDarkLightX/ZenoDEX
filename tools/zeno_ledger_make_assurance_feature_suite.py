#!/usr/bin/env python3
"""Build a ZenoLedger suite that binds feature evidence gates to lanes."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_feature_suite import build_feature_suite_manifest_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    hash_v0,
    validate_body_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tools.support.zeno_ledger_profile_samples import (  # noqa: E402
    sample_zeno_sovereign_testnet_profile_v0,
)
from tools.zeno_ledger_make_feature_lane import build_feature_lane_manifest_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.make_assurance_feature_suite_report.v0"

REPO_FEATURE_GATES: dict[str, list[list[str]]] = {
    "spot_evidence": [["bash", "tools/run_spot_evidence.sh"]],
    "upba_batch_auction": [
        ["bash", "tools/run_batch_auction_shell_assurance_gate.sh"],
        ["bash", "tools/run_batch_auction_ifql_vmo_gate.sh"],
    ],
    "zusd_evidence": [["bash", "tools/run_zusd_evidence.sh"]],
    "perps_evidence": [["bash", "tools/run_perps_evidence.sh"]],
    "proof_mining_evidence": [
        ["bash", "tools/run_proof_mining_manager_assurance_gate.sh"],
        ["bash", "tools/run_proof_mining_claimability_assurance_gate.sh"],
    ],
    "oracle_evidence": [
        [sys.executable, "tools/zeno_oracle_workflow_evidence_status.py", "--format", "json"]
    ],
    "autotrader_evidence": [["bash", "tools/run_autotrader_evidence.sh"]],
    "confidential_extension_evidence": [
        ["bash", "tools/run_confidential_extension_live_admission_gate_assurance_gate.sh"],
        ["bash", "tools/run_confidential_extension_receipt_precheck_gate_assurance_gate.sh"],
        ["bash", "tools/run_confidential_extension_receipt_gate_assurance_gate.sh"],
        ["bash", "tools/run_confidential_request_use_gate_assurance_gate.sh"],
    ],
}


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _root(label: str, payload: object) -> str:
    return hash_v0(f"assurance_feature_suite_{label}", payload)


def _empty_evidence_with_gate_receipts(feature_id: str, commands: list[list[str]]) -> dict[str, list[object]]:
    proof_receipts: list[dict[str, object]] = []
    for index, command in enumerate(commands):
        body = {
            "schema": "zenodex.zeno_ledger.feature_gate_descriptor.v0",
            "feature_id": feature_id,
            "gate_index": index,
            "command": command,
        }
        proof_receipts.append({**body, "descriptor_hash": hash_v0("feature_gate_descriptor_v0", body)})
    return {
        "upba_certificates": [],
        "price_grid_tables": [],
        "uniform_batch_hypergraph_roots": [],
        "oracle_packets": [],
        "proof_receipts": proof_receipts,
        "rejection_receipts": [],
    }


def _gate_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    feature_id: str,
    commands: list[list[str]],
) -> dict[str, Any]:
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": time_ms,
                "cutoff_sequence": height * 1_000,
                "sequencer_id": sequencer_id,
                "policy_id": "assurance_feature_gate_cutoff_v0",
                "policy_digest": _root("ingress_policy", {"chain_id": chain_id, "feature_id": feature_id}),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": _empty_evidence_with_gate_receipts(feature_id, commands),
    }
    validate_body_v0(body)
    return body


def _smoke_feature_gates(feature_ids: list[str]) -> dict[str, list[list[str]]]:
    gates: dict[str, list[list[str]]] = {}
    for feature_id in feature_ids:
        gates[feature_id] = [
            [
                sys.executable,
                "-c",
                (
                    "import json; "
                    f"print(json.dumps({{'ok': True, 'feature_id': {feature_id!r}}}))"
                ),
            ]
        ]
    return gates


def _feature_gates_for_mode(mode: str) -> dict[str, list[list[str]]]:
    if mode == "repo":
        return {key: [list(command) for command in commands] for key, commands in REPO_FEATURE_GATES.items()}
    if mode == "smoke":
        return _smoke_feature_gates(list(REPO_FEATURE_GATES.keys()))
    raise ValueError("mode must be 'repo' or 'smoke'")


def build_assurance_feature_suite_v0(
    *,
    out_dir: Path,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
    mode: str,
) -> dict[str, Any]:
    feature_gates = _feature_gates_for_mode(mode)
    config_digest = _root("config", {"chain_id": chain_id, "profile": "assurance_feature_suite_v0"})
    sequencer_set_hash = _root("sequencer_set", {"sequencer_id": sequencer_id})
    module_versions_digest = _root("module_versions", {"schema": "zeno_ledger_v0", "mode": mode})
    token_asset_id = _root("token_asset", {"chain_id": chain_id, "symbol": token_symbol})
    source_dir = out_dir / "source"
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis_snapshot.json"
    suite_path = out_dir / "feature_suite.json"

    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id=chain_id,
        config_digest=config_digest,
        sequencer_set_hash=sequencer_set_hash,
        token_symbol=token_symbol,
        token_asset_id=token_asset_id,
    )
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(empty_state).data)

    lane_paths: list[tuple[str, Path]] = []
    for index, (feature_id, commands) in enumerate(sorted(feature_gates.items()), start=1):
        lane_dir = out_dir / feature_id
        body_path = source_dir / f"{feature_id}_body.json"
        _write_json(
            body_path,
            _gate_body_v0(
                chain_id=chain_id,
                height=1,
                time_ms=time_ms + index,
                sequencer_id=sequencer_id,
                feature_id=feature_id,
                commands=commands,
            ),
        )
        lane_report = build_feature_lane_manifest_v0(
            out_dir=lane_dir,
            profile_path=profile_path,
            genesis_snapshot_path=genesis_path,
            tau_app_state_path=None,
            zusd_state_path=None,
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
            body_paths=[body_path],
            module_versions_digest=module_versions_digest,
            allow_missing_settlement=True,
            disable_intent_signatures=True,
            feature_gate_commands=commands,
        )
        lane_paths.append((feature_id, Path(str(lane_report["manifest_path"]))))

    suite = build_feature_suite_manifest_v0(
        suite_name=f"ZenoLedger assurance feature suite ({mode})",
        lanes=lane_paths,
        required_features=[feature_id for feature_id, _path in lane_paths],
    )
    _write_json(suite_path, suite)
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "mode": mode,
        "suite_path": str(suite_path),
        "feature_suite_hash": suite["feature_suite_hash"],
        "feature_count": suite["feature_count"],
        "features": [feature_id for feature_id, _path in lane_paths],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a ZenoLedger feature-gate assurance suite")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    parser.add_argument("--mode", choices=("repo", "smoke"), default="repo")
    args = parser.parse_args(argv)

    try:
        report = build_assurance_feature_suite_v0(
            out_dir=args.out_dir,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
            mode=args.mode,
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
