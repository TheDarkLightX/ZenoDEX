#!/usr/bin/env python3
"""Build app-root/JMT production-promotion evidence from release replay paths.

This producer tool exercises the two supported live root paths guarded by the
``app_root_jmt`` promotion lane:

* plain Dex snapshot root through ``tools.zeno_ledger_node``;
* local block pre-snapshot header root through ``tools.zeno_ledger_run_local``.

It also includes a lane-tamper negative check. The verifier in
``src.integration.production_promotion_evidence`` remains authoritative; this
tool only constructs a replayable evidence body and attaches its self-binding
hash.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
import time
from copy import deepcopy
from pathlib import Path
from typing import Any, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from src.core.dex import DexState  # noqa: E402
from src.integration.dex_snapshot import snapshot_from_state  # noqa: E402
from src.integration.production_promotion_evidence import (  # noqa: E402
    APP_ROOT_JMT_EVIDENCE_SCHEMA_V2,
    attach_production_app_root_jmt_hash_v2,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    compute_dex_snapshot_app_root_v0,
    hash_v0,
)
from src.state.app_root import APP_ROOT_LANE_KINDS  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402
from tools.zeno_ledger_node import _state_root_for_state_file_obj_v0  # noqa: E402
from tools.zeno_ledger_run_local import ZERO_ROOT, build_local_block_v0  # noqa: E402


def _bare_root(root: str) -> str:
    if root.startswith(("0x", "0X")):
        return root[2:].lower()
    return root.lower()


def _source_hash(value: object) -> str:
    return _bare_root(hash_v0("app_root_jmt_evidence_source_v1", value))


def _root(label: str) -> str:
    return hash_v0("app_root_jmt_evidence_root_v1", {"label": label})


def _base_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _base_snapshot() -> dict[str, Any]:
    snapshot = snapshot_from_state(_base_state()).data
    snapshot["oracle"] = {"price_timestamp": 17, "max_staleness_seconds": 300}
    snapshot["vault"] = {
        "acc_reward_per_share": 0,
        "last_update_acc": 0,
        "pending_rewards": 0,
        "reward_balance": 0,
        "staked_lp_shares": 0,
    }
    snapshot["perps"] = {"version": 5, "markets": []}
    return snapshot


def _body() -> dict[str, Any]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "height": 1,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": "zeno-ledger-devnet-0",
                "height": 1,
                "cutoff_time_ms": 1_778_730_000_000,
                "cutoff_sequence": 12345,
                "sequencer_id": "sequencer-dev-0",
                "policy_id": "public_cutoff_v0",
                "policy_digest": _root("cutoff-policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [],
            "proof_receipts": [],
            "rejection_receipts": [],
        },
    }


def _plain_snapshot_check(*, checked_at: int) -> dict[str, Any]:
    snapshot = _base_snapshot()
    observed_root = _bare_root(_state_root_for_state_file_obj_v0(snapshot))
    recomputed_root = _bare_root(compute_dex_snapshot_app_root_v0(snapshot))
    return {
        "check_id": "plain-dex-snapshot",
        "mode": "plain_dex_snapshot_live_root",
        "source_kind": "release_replay",
        "source_payload": snapshot,
        "observed_root": observed_root,
        "recomputed_root": recomputed_root,
        "source_state_hash": _source_hash(snapshot),
        "required_lane_kinds": sorted(APP_ROOT_LANE_KINDS),
        "live_path": "tools/zeno_ledger_node.py:_state_root_for_state_file_obj_v0",
        "derivation_path": (
            "src/integration/zeno_ledger_v0.py:compute_dex_snapshot_app_root_v0"
        ),
        "checked_at": checked_at,
    }


def _local_pre_snapshot_header_check(*, checked_at: int) -> dict[str, Any]:
    snapshot = _base_snapshot()
    with tempfile.TemporaryDirectory(prefix="zenodex-app-root-jmt-") as raw_tmp:
        tmp = Path(raw_tmp)
        snapshot_path = tmp / "pre-snapshot.json"
        body_path = tmp / "body.json"
        snapshot_path.write_text(json.dumps(snapshot, sort_keys=True), encoding="utf-8")
        body_path.write_text(json.dumps(_body(), sort_keys=True), encoding="utf-8")
        report = build_local_block_v0(
            body_path=body_path,
            out_dir=tmp / "ledger",
            time_ms=1_778_730_000_000,
            pre_snapshot_path=snapshot_path,
            trusted_prev_header_hash=ZERO_ROOT,
            sequencer_set_hash=_root("sequencer-set"),
            data_availability_root=_root("data-availability"),
            proof_journal_hash=ZERO_ROOT,
            config_digest=_root("config"),
            module_versions_digest=_root("module-versions"),
            signature_set_root=ZERO_ROOT,
        )
        header = json.loads(Path(str(report["header_path"])).read_text(encoding="utf-8"))
    observed_root = _bare_root(str(header["pre_state_root"]))
    recomputed_root = _bare_root(compute_dex_snapshot_app_root_v0(snapshot))
    return {
        "check_id": "local-block-pre-snapshot",
        "mode": "local_block_pre_snapshot_header",
        "source_kind": "release_replay",
        "source_payload": snapshot,
        "observed_root": observed_root,
        "recomputed_root": recomputed_root,
        "source_state_hash": _source_hash(snapshot),
        "required_lane_kinds": sorted(APP_ROOT_LANE_KINDS),
        "live_path": "tools/zeno_ledger_run_local.py:build_local_block_v0",
        "derivation_path": (
            "src/integration/zeno_ledger_v0.py:compute_dex_snapshot_app_root_v0"
        ),
        "checked_at": checked_at,
    }


def _lane_tamper_negative(*, checked_at: int) -> dict[str, Any]:
    snapshot = _base_snapshot()
    baseline = _bare_root(_state_root_for_state_file_obj_v0(snapshot))
    tampered = deepcopy(snapshot)
    tampered["oracle"] = {"price_timestamp": 18, "max_staleness_seconds": 300}
    tampered_root = _bare_root(_state_root_for_state_file_obj_v0(tampered))
    return {
        "check_id": "lane-tamper",
        "mutation": "lane_tamper_rejected",
        "mode": "plain_dex_snapshot_live_root",
        "source_kind": "release_replay",
        "baseline_payload": snapshot,
        "mutated_payload": tampered,
        "baseline_root": baseline,
        "mutated_root": tampered_root,
        "required_lane_kinds": sorted(APP_ROOT_LANE_KINDS),
        "derivation_path": (
            "src/integration/zeno_ledger_v0.py:compute_dex_snapshot_app_root_v0"
        ),
        "rejected": tampered_root != baseline,
        "checked_at": checked_at,
    }


def build_evidence(*, now: int | None = None) -> dict[str, Any]:
    checked_at = int(time.time() if now is None else now)
    body: Mapping[str, Any] = {
        "schema": APP_ROOT_JMT_EVIDENCE_SCHEMA_V2,
        "evidence_kind": "live_replay",
        "root_system": "typed_app_root_jmt_v1",
        "required_lane_kinds": sorted(APP_ROOT_LANE_KINDS),
        "live_root_checks": [
            _plain_snapshot_check(checked_at=checked_at),
            _local_pre_snapshot_header_check(checked_at=checked_at),
        ],
        "negative_checks": [_lane_tamper_negative(checked_at=checked_at)],
        "issued_at": checked_at,
    }
    return attach_production_app_root_jmt_hash_v2(body)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="path to write app-root/JMT evidence JSON")
    parser.add_argument("--now", type=int, default=None, help="pin evidence checked_at/issued_at unix timestamp")
    return parser.parse_args(list(argv))


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    evidence = build_evidence(now=args.now)
    _write_json(args.out, evidence)
    print(json.dumps({"ok": True, "path": str(args.out), "evidence_hash": evidence["evidence_hash"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
