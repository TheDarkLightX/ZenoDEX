#!/usr/bin/env python3
"""Build a local ZenoLedger v0 block envelope from a supplied body."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import sys
from contextlib import contextmanager
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.consensus_time import (
    ClockPolicyScheduleV1,
    VerifiedExecutionClockV1,
    clock_policy_schedule_hash_v1,
    default_height_only_clock_schedule_v1,
    verify_execution_clock_v1,
)
from src.core.dex import DexConfig, DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.proof_toolchain_lock import proof_toolchain_lock_hash_v0
from src.integration.risc0_tx_order_body_summary import (
    apply_route_order_receipt_policy_to_body_v1,
)
from src.integration.zeno_ledger_cross_shard_effect_application import (
    apply_terminal_cross_shard_ledger_effects_to_state_v0,
    build_cross_shard_ledger_effects_artifact_v0,
    cross_shard_applied_effects_state_from_payload_v0,
    empty_cross_shard_applied_effects_state_v0,
)
from src.integration.zeno_ledger_cross_shard_global_conservation import (
    build_cross_shard_global_conservation_receipt_v0,
)
from src.integration.zeno_ledger_tau_export import (
    CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0,
    CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0,
    CrossShardPostingSummaryBodyEvidenceV0,
    cross_shard_terminal_admission_set_hash_v0,
    infer_cross_shard_posting_summary_body_evidence_detail_v0,
    validate_cross_shard_posting_summary_export_v0,
)
from src.integration.zeno_ledger_v0 import (
    TAU_APP_STATE_SCHEMA_V1,
    TAU_APP_STATE_VERSION_V1,
    apply_body_transactions_v0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    build_tx_receipt_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_dex_snapshot_app_root_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tau_app_state_app_root_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
    stable_error_code_v0,
    tx_hash_v0,
    validate_body_v0,
    validate_header_chain_linkage_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
)
from src.state.balances import BalanceTable
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from src.state.lp import LPTable

ZERO_ROOT = "0x" + "00" * 32
REPORT_SCHEMA = "zenodex.zeno_ledger.run_local_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def _normalize_cross_shard_posting_summary_paths_v0(
    *,
    posting_summary_path: Path | None,
    posting_summary_paths: Sequence[Path] | None,
) -> tuple[Path, ...]:
    single = () if posting_summary_path is None else (posting_summary_path,)
    many = () if posting_summary_paths is None else tuple(posting_summary_paths)
    if single and many:
        raise ValueError(
            "use either cross_shard_posting_summary_path or "
            "cross_shard_posting_summary_paths"
        )
    return tuple(Path(path) for path in (*single, *many))


def _normalize_cross_shard_terminal_admission_paths_v0(
    terminal_admission_paths: Sequence[Path] | None,
) -> tuple[Path, ...]:
    if terminal_admission_paths is None:
        return ()
    return tuple(Path(path) for path in terminal_admission_paths)


def _load_cross_shard_writer_posting_summaries_v0(
    *,
    body: Mapping[str, Any],
    posting_summary_paths: Sequence[Path],
) -> tuple[Mapping[str, Any], ...]:
    body_evidence = infer_cross_shard_posting_summary_body_evidence_detail_v0(body)
    requirement = body_evidence.requirement
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0
        and not posting_summary_paths
    ):
        raise ValueError("cross-shard posting summary is required by body evidence")
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0
        and posting_summary_paths
    ):
        raise ValueError("cross-shard posting summary is forbidden by body evidence")
    if not posting_summary_paths:
        return ()
    if (
        body_evidence.expected_posting_summary_hash is not None
        and len(posting_summary_paths) != 1
    ):
        raise ValueError(
            "body-pinned cross-shard posting summary hash requires exactly one "
            "posting summary"
        )
    posting_summaries = tuple(
        validate_cross_shard_posting_summary_export_v0(_load_json_object(path))
        for path in posting_summary_paths
    )
    posting_hashes = tuple(
        str(posting_summary["posting_summary_hash"])
        for posting_summary in posting_summaries
    )
    if len(set(posting_hashes)) != len(posting_hashes):
        raise ValueError("duplicate cross-shard posting summary hash")
    sorted_posting_summaries = tuple(
        sorted(
            posting_summaries,
            key=lambda posting_summary: str(posting_summary["posting_summary_hash"]),
        )
    )
    sorted_posting_hashes = tuple(
        str(posting_summary["posting_summary_hash"])
        for posting_summary in sorted_posting_summaries
    )
    if (
        body_evidence.expected_posting_summary_hash is not None
        and posting_summaries[0]["posting_summary_hash"]
        != body_evidence.expected_posting_summary_hash
    ):
        raise ValueError("cross-shard posting summary hash conflicts with body evidence")
    if (
        body_evidence.expected_posting_summary_set_hash is not None
        and sorted_posting_hashes != body_evidence.expected_posting_summary_hashes
    ):
        raise ValueError("cross-shard posting summary set conflicts with body evidence")
    return sorted_posting_summaries


def _load_cross_shard_writer_terminal_admissions_v0(
    *,
    body: Mapping[str, Any],
    posting_summaries: Sequence[Mapping[str, Any]],
    terminal_admission_paths: Sequence[Path],
) -> tuple[Mapping[str, Any], ...]:
    body_evidence = infer_cross_shard_posting_summary_body_evidence_detail_v0(body)
    if not posting_summaries:
        if terminal_admission_paths:
            raise ValueError("cross-shard terminal admission supplied without posting summary")
        return ()
    if not terminal_admission_paths:
        raise ValueError("cross-shard terminal admission is required for posting summary application")
    if len(terminal_admission_paths) != len(posting_summaries):
        raise ValueError("cross-shard terminal admission count must match posting summary count")

    admissions = tuple(_load_json_object(path) for path in terminal_admission_paths)
    admission_hashes = tuple(
        _terminal_admission_posting_summary_hash_v0(admission)
        for admission in admissions
    )
    if len(set(admission_hashes)) != len(admission_hashes):
        raise ValueError("duplicate cross-shard terminal admission posting summary hash")
    sorted_admissions = tuple(
        admission
        for _, admission in sorted(zip(admission_hashes, admissions), key=lambda row: row[0])
    )
    expected_hashes = tuple(
        str(posting_summary["posting_summary_hash"])
        for posting_summary in posting_summaries
    )
    sorted_admission_hashes = tuple(
        _terminal_admission_posting_summary_hash_v0(admission)
        for admission in sorted_admissions
    )
    if sorted_admission_hashes != expected_hashes:
        raise ValueError("cross-shard terminal admission set conflicts with posting summaries")
    _validate_body_pinned_terminal_admissions_v0(
        sorted_admissions=sorted_admissions,
        body_evidence=body_evidence,
    )
    return sorted_admissions


def _validate_body_pinned_terminal_admissions_v0(
    *,
    sorted_admissions: Sequence[Mapping[str, Any]],
    body_evidence: CrossShardPostingSummaryBodyEvidenceV0,
) -> None:
    expected_terminal_hashes = body_evidence.expected_terminal_admission_hashes
    if not expected_terminal_hashes:
        return
    supplied_terminal_hashes = tuple(
        _terminal_admission_hash_v0(admission)
        for admission in sorted_admissions
    )
    if body_evidence.expected_terminal_admission_set_hash is None:
        if len(supplied_terminal_hashes) != 1:
            raise ValueError(
                "body-pinned cross-shard terminal admission hash requires exactly "
                "one terminal admission"
            )
        if supplied_terminal_hashes[0] != expected_terminal_hashes[0]:
            raise ValueError(
                "cross-shard terminal admission hash conflicts with body evidence"
            )
        return
    canonical_supplied_hashes = tuple(sorted(supplied_terminal_hashes))
    if canonical_supplied_hashes != expected_terminal_hashes:
        raise ValueError(
            "cross-shard terminal admission set conflicts with body evidence"
        )
    if (
        cross_shard_terminal_admission_set_hash_v0(canonical_supplied_hashes)
        != body_evidence.expected_terminal_admission_set_hash
    ):
        raise ValueError(
            "cross-shard terminal admission set hash conflicts with body evidence"
        )


def _terminal_admission_hash_v0(admission: Mapping[str, Any]) -> str:
    value = admission.get("admission_hash")
    if not isinstance(value, str):
        raise TypeError("cross-shard terminal admission admission_hash must be a string")
    canonical = canonical_hex_fixed_allow_0x(
        value,
        nbytes=32,
        name="cross_shard_terminal_admission.admission_hash",
    )
    if value != canonical:
        raise ValueError("cross-shard terminal admission admission_hash must be canonical")
    return canonical


def _terminal_admission_posting_summary_hash_v0(admission: Mapping[str, Any]) -> str:
    value = admission.get("posting_summary_hash")
    if not isinstance(value, str):
        raise TypeError("cross-shard terminal admission posting_summary_hash must be a string")
    canonical = canonical_hex_fixed_allow_0x(
        value,
        nbytes=32,
        name="cross_shard_terminal_admission.posting_summary_hash",
    )
    if value != canonical:
        raise ValueError(
            "cross-shard terminal admission posting_summary_hash must be canonical"
        )
    return canonical


def _load_cross_shard_writer_posting_summary_v0(
    *,
    body: Mapping[str, Any],
    posting_summary_path: Path | None,
) -> Mapping[str, Any] | None:
    posting_summaries = _load_cross_shard_writer_posting_summaries_v0(
        body=body,
        posting_summary_paths=()
        if posting_summary_path is None
        else (posting_summary_path,),
    )
    if not posting_summaries:
        return None
    return posting_summaries[0]


def _canonical_json_text_v0(value: object) -> str:
    return canonical_json_bytes(value).decode("utf-8")


def _cross_shard_replay_state_from_optional_payload_v0(value: object):
    if value is None:
        return empty_cross_shard_applied_effects_state_v0()
    if not isinstance(value, Mapping):
        raise TypeError("cross_shard replay state must be an object or null")
    return cross_shard_applied_effects_state_from_payload_v0(value)


def _preserve_snapshot_app_root_lanes_v0(
    *,
    source_snapshot: Mapping[str, Any],
    target_snapshot: dict[str, Any],
) -> dict[str, Any]:
    if "cross_shard" in source_snapshot and "cross_shard" not in target_snapshot:
        target_snapshot["cross_shard"] = source_snapshot["cross_shard"]
    if "governance" in source_snapshot and "governance" not in target_snapshot:
        target_snapshot["governance"] = source_snapshot["governance"]
    return target_snapshot


def _apply_cross_shard_writer_effects_to_snapshot_v0(
    *,
    snapshot: Mapping[str, Any],
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    terminal_admission: Mapping[str, Any],
):
    snapshot_obj = dict(snapshot)
    replay_state = _cross_shard_replay_state_from_optional_payload_v0(
        snapshot_obj.get("cross_shard")
    )
    state = state_from_snapshot(snapshot_obj)
    result = apply_terminal_cross_shard_ledger_effects_to_state_v0(
        balances=state.balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        replay_state=replay_state,
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
    )
    if not result.ok:
        raise ValueError(str(result.error))
    receipt = build_cross_shard_global_conservation_receipt_v0(
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
        pre_replay_state=replay_state,
        post_replay_state=result.post_replay_state,  # type: ignore[arg-type]
    )
    updated = snapshot_from_state(state).data
    _preserve_snapshot_app_root_lanes_v0(
        source_snapshot=snapshot_obj,
        target_snapshot=updated,
    )
    updated["cross_shard"] = result.post_replay_state.to_payload()  # type: ignore[union-attr]
    return updated, result, receipt


def _tau_app_state_obj_from_json_v0(app_state_json: str) -> dict[str, Any]:
    raw = (app_state_json or "").strip()
    if not raw:
        obj: Mapping[str, Any] = snapshot_from_state(
            DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
        ).data
    else:
        obj = json.loads(raw)
    if not isinstance(obj, Mapping):
        raise TypeError("tau app state must decode to a JSON object")
    if obj.get("schema") == TAU_APP_STATE_SCHEMA_V1:
        return dict(obj)
    return {
        "schema": TAU_APP_STATE_SCHEMA_V1,
        "version": TAU_APP_STATE_VERSION_V1,
        "dex_state": dict(obj),
    }


def _preserve_tau_wrapper_lanes_v0(
    *,
    source_app_state: Mapping[str, Any] | None,
    target_app_state: dict[str, Any],
) -> dict[str, Any]:
    if source_app_state is None:
        return target_app_state
    for key in (
        "proof_mining",
        "zusd_monetary",
        "clob",
        "orderbook",
        "cross_shard",
        "governance",
    ):
        if key in source_app_state and key not in target_app_state:
            target_app_state[key] = source_app_state[key]
    return target_app_state


def _apply_cross_shard_writer_effects_to_tau_app_state_v0(
    *,
    app_state_json: str,
    pre_app_state: Mapping[str, Any] | None,
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    terminal_admission: Mapping[str, Any],
):
    app_state = _tau_app_state_obj_from_json_v0(app_state_json)
    _preserve_tau_wrapper_lanes_v0(
        source_app_state=pre_app_state,
        target_app_state=app_state,
    )
    dex_snapshot = app_state.get("dex_state")
    if not isinstance(dex_snapshot, Mapping):
        raise TypeError("app_state.dex_state must be an object")
    updated_dex_snapshot, result, receipt = _apply_cross_shard_writer_effects_to_snapshot_v0(
        snapshot=dex_snapshot,
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
        terminal_admission=terminal_admission,
    )
    app_state["dex_state"] = updated_dex_snapshot
    app_state["cross_shard"] = result.post_replay_state.to_payload()  # type: ignore[union-attr]
    return app_state, result, receipt


def _cross_shard_writer_output_path_v0(
    *,
    out_dir: Path,
    subdir: str,
    height: int,
    index: int,
    count: int,
) -> Path:
    name = f"{height}.json" if count == 1 else f"{height}-{index:04d}.json"
    return out_dir / subdir / name


def _load_chain_balances(path: Path | None) -> dict[str, int]:
    if path is None:
        return {}
    obj = _load_json_object(path)
    out: dict[str, int] = {}
    for key, value in obj.items():
        if not isinstance(key, str):
            raise TypeError("chain balance keys must be strings")
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError("chain balance values must be non-negative ints")
        out[key] = value
    return out


def _zusd_state_root_v0(state: object) -> str:
    return hash_v0("zusd_state_v0", dict(getattr(state, "__dict__")))


def _perp_state_root_v0(state: Mapping[str, Any]) -> str:
    return hash_v0("perp_state_v0", dict(state))


def _oracle_state_root_v0(state: object) -> str:
    return hash_v0("oracle_state_v0", dict(getattr(state, "__dict__")))


def _oracle_reporter_state_root_v0(state: Mapping[str, Any]) -> str:
    return hash_v0("oracle_reporter_state_v0", dict(state))


def _upba_state_root_v0(state: object) -> str:
    return hash_v0("upba_state_v0", dict(getattr(state, "__dict__")))


def _proof_mining_state_root_v0(state: object) -> str:
    from src.integration.proof_mining_runtime import proof_mining_runtime_state_to_obj

    return hash_v0("proof_mining_state_v0", proof_mining_runtime_state_to_obj(state))  # type: ignore[arg-type]


def _autotrader_state_root_v0(state: object) -> str:
    return hash_v0("autotrader_state_v0", _autotrader_controller_state_to_obj(state))


def _confidential_state_root_v0(state: Mapping[str, Any]) -> str:
    return hash_v0("confidential_state_v0", dict(state))


def _load_confidential_state(path: Path) -> dict[str, Any]:
    return dict(_load_json_object(path))


def _strategy_budget_state_to_obj(state: object) -> dict[str, Any]:
    from src.kernels.python.strategy_budget_guard_v1_adapter import StrategyBudgetState

    if not isinstance(state, StrategyBudgetState):
        raise TypeError("budget_state must be a StrategyBudgetState")
    return {
        "window_id": int(state.window_id),
        "spent_in_window": int(state.spent_in_window),
        "kill_switch_on": bool(state.kill_switch_on),
    }


def _strategy_budget_state_from_obj(obj: object) -> object:
    from src.kernels.python.strategy_budget_guard_v1_adapter import StrategyBudgetState

    if not isinstance(obj, Mapping):
        raise TypeError("budget_state must be an object")
    kill_switch_on = obj.get("kill_switch_on", False)
    if not isinstance(kill_switch_on, bool):
        raise TypeError("budget_state.kill_switch_on must be a bool")
    return StrategyBudgetState(
        window_id=obj.get("window_id", 0),
        spent_in_window=obj.get("spent_in_window", 0),
        kill_switch_on=kill_switch_on,
    )


def _autotrader_controller_state_to_obj(state: object) -> dict[str, Any]:
    from src.integration.autotrader_controller import AutoTraderControllerState

    if not isinstance(state, AutoTraderControllerState):
        raise TypeError("autotrader_state must be an AutoTraderControllerState")
    return {
        "schema": "zenodex/autotrader_controller_state/v1",
        "budget_state": _strategy_budget_state_to_obj(state.budget_state),
        "last_action_epoch": state.last_action_epoch,
        "lifetime_spent": int(state.lifetime_spent),
        "live_orders": int(state.live_orders),
    }


def _autotrader_controller_state_from_obj(obj: object) -> object:
    from src.integration.autotrader_controller import AutoTraderControllerState

    if not isinstance(obj, Mapping):
        raise TypeError("autotrader_state must be an object")
    schema = obj.get("schema", "zenodex/autotrader_controller_state/v1")
    if schema != "zenodex/autotrader_controller_state/v1":
        raise ValueError("autotrader_state schema mismatch")
    return AutoTraderControllerState(
        budget_state=_strategy_budget_state_from_obj(obj.get("budget_state", {})),
        last_action_epoch=obj.get("last_action_epoch"),
        lifetime_spent=obj.get("lifetime_spent", 0),
        live_orders=obj.get("live_orders", 0),
    )


def _pool_state_to_obj(pool: object) -> dict[str, Any]:
    from src.state.pools import PoolState

    if not isinstance(pool, PoolState):
        raise TypeError("pool must be a PoolState")
    return {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "lp_supply": int(pool.lp_supply),
        "status": pool.status.value,
        "created_at": int(pool.created_at),
        "curve_tag": pool.curve_tag,
        "curve_params": pool.curve_params,
    }


def _pool_state_from_obj(obj: object) -> object:
    from src.state.pools import PoolState, PoolStatus

    if not isinstance(obj, Mapping):
        raise TypeError("pool state must be an object")
    status = obj.get("status", PoolStatus.ACTIVE.value)
    if isinstance(status, PoolStatus):
        pool_status = status
    elif isinstance(status, str):
        pool_status = PoolStatus(status)
    else:
        raise TypeError("pool status must be a string")
    return PoolState(
        pool_id=obj["pool_id"],
        asset0=obj["asset0"],
        asset1=obj["asset1"],
        reserve0=obj["reserve0"],
        reserve1=obj["reserve1"],
        fee_bps=obj["fee_bps"],
        lp_supply=obj.get("lp_supply", 0),
        status=pool_status,
        created_at=obj.get("created_at", 0),
        curve_tag=obj.get("curve_tag", "CPMM"),
        curve_params=obj.get("curve_params", ""),
    )


@lru_cache(maxsize=1)
def _load_upba_ref_v0() -> Any:
    ref_path = ROOT / "generated" / "batch_auction_settler_v1" / "python_ref" / "batch_auction_settler_v1_ref.py"
    if not ref_path.exists():
        raise FileNotFoundError(f"batch auction reference model not found at {ref_path}")
    spec = importlib.util.spec_from_file_location("zeno_ledger_batch_auction_settler_v1_ref", ref_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load batch auction reference model at {ref_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[str(spec.name)] = module
    spec.loader.exec_module(module)
    return module


def _execute_zusd_body_v0(
    *,
    zusd_state: object,
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    from src.core.zusd import ZUSDCommand, ZUSDState, step

    if not isinstance(zusd_state, ZUSDState):
        raise TypeError("zusd_state must be a ZUSDState")
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = zusd_state
    pre_state_root = _zusd_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("zusd_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].zusd_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].zusd_commands[{command_index}] must be an object"
                break
            tag = raw_command.get("tag")
            args = raw_command.get("args", {})
            if not isinstance(tag, str) or tag == "":
                error = f"transactions[{index}].zusd_commands[{command_index}].tag is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].zusd_commands[{command_index}].args must be an object"
                break
            result = step(candidate_state, ZUSDCommand(tag=tag, args=dict(args)))  # type: ignore[arg-type]
            if not result.ok:
                error = result.error or "zusd command rejected"
                break
            if result.state is None:
                error = "accepted zUSD command returned no state"
                break
            candidate_state = result.state

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _zusd_state_root_v0(working_state)
    return pre_state_root, post_state_root, dict(working_state.__dict__), executed_body, receipts


def _load_zusd_state(path: Path) -> object:
    from src.core.zusd import ZUSDState

    return ZUSDState(**dict(_load_json_object(path)))


def _load_perp_state(path: Path) -> dict[str, Any]:
    return dict(_load_json_object(path))


def _load_oracle_state(path: Path) -> object:
    from src.core.oracle import OracleState

    return OracleState(**dict(_load_json_object(path)))


def _load_oracle_reporter_state(path: Path) -> dict[str, Any]:
    return dict(_load_json_object(path))


def _load_upba_state(path: Path) -> object:
    ref = _load_upba_ref_v0()
    return ref.State(**dict(_load_json_object(path)))


def _load_proof_mining_state(path: Path) -> object:
    from src.integration.proof_mining_runtime import proof_mining_runtime_state_from_obj

    return proof_mining_runtime_state_from_obj(_load_json_object(path))


def _load_autotrader_state(path: Path) -> object:
    return _autotrader_controller_state_from_obj(_load_json_object(path))


def _execute_perp_body_v0(
    *,
    perp_state: Mapping[str, Any],
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from src.core.perp_epoch import perp_epoch_isolated_default_apply

    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = dict(perp_state)
    pre_state_root = _perp_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("perp_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].perp_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].perp_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            params = raw_command.get("params", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].perp_commands[{command_index}].action is required"
                break
            if not isinstance(params, Mapping):
                error = f"transactions[{index}].perp_commands[{command_index}].params must be an object"
                break
            result = perp_epoch_isolated_default_apply(
                state=candidate_state,
                action=action,
                params=dict(params),
            )
            if not result.ok:
                reason = result.error or result.code or "perp command rejected"
                error = f"{action}:{reason}"
                break
            if result.state is None:
                error = "accepted perp command returned no state"
                break
            candidate_state = dict(result.state)

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _perp_state_root_v0(working_state)
    return pre_state_root, post_state_root, working_state, executed_body, receipts


def _execute_oracle_body_v0(
    *,
    oracle_state: object,
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from src.core.oracle import OracleState, is_fresh, update_price_timestamp

    if not isinstance(oracle_state, OracleState):
        raise TypeError("oracle_state must be an OracleState")
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = oracle_state
    pre_state_root = _oracle_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("oracle_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].oracle_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].oracle_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            args = raw_command.get("args", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].oracle_commands[{command_index}].action is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].oracle_commands[{command_index}].args must be an object"
                break
            try:
                if action == "update_price_timestamp":
                    candidate_state = update_price_timestamp(
                        candidate_state,
                        int(args["current_timestamp"]),
                    )
                elif action == "require_fresh":
                    fresh = is_fresh(candidate_state, int(args["current_timestamp"]))
                    if not fresh:
                        error = "oracle_not_fresh"
                        break
                else:
                    error = f"unknown oracle action: {action}"
                    break
            except (KeyError, TypeError, ValueError) as exc:
                error = str(exc)
                break

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _oracle_state_root_v0(working_state)
    return pre_state_root, post_state_root, dict(working_state.__dict__), executed_body, receipts


def _execute_oracle_reporter_body_v0(
    *,
    oracle_reporter_state: Mapping[str, Any],
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from tools.zenodex_oracle_reporter_lifecycle import verify_lifecycle_trace
    from tools.zenodex_oracle_reporter_token_settlement_replay import (
        verify_reporter_token_settlement,
    )

    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = dict(oracle_reporter_state)
    pre_state_root = _oracle_reporter_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("oracle_reporter_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].oracle_reporter_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = dict(working_state)
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].oracle_reporter_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            args = raw_command.get("args", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].oracle_reporter_commands[{command_index}].action is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].oracle_reporter_commands[{command_index}].args must be an object"
                break
            try:
                if action == "verify_lifecycle_trace":
                    trace = args.get("trace")
                    if not isinstance(trace, Mapping):
                        error = "oracle reporter lifecycle trace must be an object"
                        break
                    result = verify_lifecycle_trace(trace).to_json_obj()
                    if result["status"] != "accepted":
                        errors = result.get("errors", [])
                        suffix = "_".join(str(item) for item in errors[:3]) if isinstance(errors, list) else "unknown"
                        error = f"oracle_reporter_lifecycle_rejected:{suffix}"
                        break
                    candidate_state = dict(candidate_state)
                    candidate_state.update(
                        {
                            "schema": "zenodex/oracle_reporter_ledger_state/v1",
                            "accepted_lifecycle_count": int(candidate_state.get("accepted_lifecycle_count", 0)) + 1,
                            "last_result": result,
                            "last_reporter_id": result.get("reporter_id"),
                            "last_epoch": result.get("last_epoch"),
                            "total_slashed": result.get("total_slashed"),
                            "total_withdrawn": result.get("total_withdrawn"),
                        }
                    )
                elif action == "verify_token_settlement_replay":
                    replay = args.get("replay")
                    if not isinstance(replay, Mapping):
                        error = "oracle reporter token settlement replay must be an object"
                        break
                    result = verify_reporter_token_settlement(replay).to_json_obj()
                    if result["status"] != "accepted":
                        errors = result.get("errors", [])
                        suffix = "_".join(str(item) for item in errors[:3]) if isinstance(errors, list) else "unknown"
                        error = f"oracle_reporter_token_settlement_rejected:{suffix}"
                        break
                    policy = replay.get("policy")
                    candidate_state = dict(candidate_state)
                    candidate_state.update(
                        {
                            "schema": "zenodex/oracle_reporter_ledger_state/v1",
                            "accepted_token_settlement_count": int(
                                candidate_state.get("accepted_token_settlement_count", 0)
                            )
                            + 1,
                            "last_token_settlement_result": result,
                            "last_policy_id": policy.get("policy_id") if isinstance(policy, Mapping) else None,
                            "token_transfer_count": result.get("transfer_count"),
                            "token_total_debits_e8": result.get("total_debits_e8"),
                            "token_total_credits_e8": result.get("total_credits_e8"),
                        }
                    )
                else:
                    error = f"unknown oracle reporter action: {action}"
                    break
            except (TypeError, ValueError) as exc:
                error = str(exc)
                break

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _oracle_reporter_state_root_v0(working_state)
    return pre_state_root, post_state_root, working_state, executed_body, receipts


def _execute_upba_body_v0(
    *,
    upba_state: object,
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    ref = _load_upba_ref_v0()
    if not isinstance(upba_state, ref.State):
        raise TypeError("upba_state must be a batch_auction_settler_v1 State")
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = upba_state
    pre_state_root = _upba_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("upba_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].upba_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].upba_commands[{command_index}] must be an object"
                break
            tag = raw_command.get("tag")
            args = raw_command.get("args", {})
            if not isinstance(tag, str) or tag == "":
                error = f"transactions[{index}].upba_commands[{command_index}].tag is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].upba_commands[{command_index}].args must be an object"
                break
            result = ref.step(candidate_state, ref.Command(tag=tag, args=dict(args)))
            if not result.ok:
                error = result.error or "upba command rejected"
                break
            if result.state is None:
                error = "accepted UPBA command returned no state"
                break
            candidate_state = result.state

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _upba_state_root_v0(working_state)
    return pre_state_root, post_state_root, dict(working_state.__dict__), executed_body, receipts


def _execute_proof_mining_body_v0(
    *,
    proof_mining_state: object,
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from src.integration.proof_mining_context import proof_mining_context_from_obj
    from src.integration.proof_mining_runtime import (
        ProofMiningRuntimeState,
        apply_proof_mining_claim,
        proof_mining_runtime_state_to_obj,
        sync_proof_mining_runtime_balance,
    )

    if not isinstance(proof_mining_state, ProofMiningRuntimeState):
        raise TypeError("proof_mining_state must be a ProofMiningRuntimeState")
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = proof_mining_state
    pre_state_root = _proof_mining_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("proof_mining_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].proof_mining_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].proof_mining_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            args = raw_command.get("args", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].proof_mining_commands[{command_index}].action is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].proof_mining_commands[{command_index}].args must be an object"
                break
            try:
                if action == "submit_claim":
                    claim_artifact = args.get("claim_artifact")
                    context_obj = args.get("proof_mining_context")
                    if not isinstance(claim_artifact, Mapping):
                        error = "proof_mining claim_artifact must be an object"
                        break
                    if not isinstance(context_obj, Mapping):
                        error = "proof_mining proof_mining_context must be an object"
                        break
                    actual_reward_pool_balance = int(args["actual_reward_pool_balance"])
                    next_state, result = apply_proof_mining_claim(
                        runtime_state=candidate_state,
                        claim_artifact=claim_artifact,
                        actual_reward_pool_balance=actual_reward_pool_balance,
                        proof_mining_context=proof_mining_context_from_obj(context_obj),
                    )
                    if not result.ok:
                        error = result.error_message or result.error_code or "proof mining claim rejected"
                        break
                    candidate_state = next_state
                elif action == "sync_balance":
                    candidate_state = sync_proof_mining_runtime_balance(
                        runtime_state=candidate_state,
                        actual_reward_pool_balance=int(args["actual_reward_pool_balance"]),
                    )
                else:
                    error = f"unknown proof mining action: {action}"
                    break
            except (KeyError, TypeError, ValueError) as exc:
                error = str(exc)
                break

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _proof_mining_state_root_v0(working_state)
    return pre_state_root, post_state_root, proof_mining_runtime_state_to_obj(working_state), executed_body, receipts


def _execute_autotrader_body_v0(
    *,
    autotrader_state: object,
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from src.agents.strategy_ir import strategy_ir_from_dict
    from src.integration.autotrader_controller import (
        AutoTraderControllerState,
        AutoTraderDecisionTag,
        AutoTraderTauConfig,
        evaluate_autotrader_quote_receipt,
    )

    if not isinstance(autotrader_state, AutoTraderControllerState):
        raise TypeError("autotrader_state must be an AutoTraderControllerState")
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = autotrader_state
    pre_state_root = _autotrader_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("autotrader_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].autotrader_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = working_state
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].autotrader_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            args = raw_command.get("args", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].autotrader_commands[{command_index}].action is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].autotrader_commands[{command_index}].args must be an object"
                break
            try:
                if action != "evaluate_quote_receipt":
                    error = f"unknown autotrader action: {action}"
                    break
                strategy_obj = args.get("strategy")
                receipt_obj = args.get("receipt")
                pools_obj = args.get("pools_by_id")
                if not isinstance(strategy_obj, Mapping):
                    error = "autotrader strategy must be an object"
                    break
                if not isinstance(receipt_obj, Mapping):
                    error = "autotrader receipt must be an object"
                    break
                if not isinstance(pools_obj, Mapping):
                    error = "autotrader pools_by_id must be an object"
                    break
                pools_by_id = {
                    str(pool_id): _pool_state_from_obj(pool_obj)
                    for pool_id, pool_obj in pools_obj.items()
                }
                tau_config_obj = args.get("tau_config")
                tau_config: AutoTraderTauConfig | None = None
                if isinstance(tau_config_obj, Mapping):
                    tau_config = AutoTraderTauConfig(
                        enabled=bool(tau_config_obj.get("enabled", False)),
                        timeout_s=float(tau_config_obj.get("timeout_s", 2.0)),
                        tau_bin=tau_config_obj.get("tau_bin"),  # type: ignore[arg-type]
                        allow_path_lookup=bool(tau_config_obj.get("allow_path_lookup", False)),
                    )
                decision = evaluate_autotrader_quote_receipt(
                    strategy=strategy_ir_from_dict(strategy_obj),
                    controller_state=candidate_state,
                    receipt=dict(receipt_obj),
                    pools_by_id=pools_by_id,  # type: ignore[arg-type]
                    current_epoch=int(args["current_epoch"]),
                    intent_deadline=int(args["intent_deadline"]),
                    slippage_bps=None if args.get("slippage_bps") is None else int(args["slippage_bps"]),
                    nonce_start=None if args.get("nonce_start") is None else int(args["nonce_start"]),
                    tau_config=tau_config,
                )
                if decision.tag is AutoTraderDecisionTag.REJECT:
                    error = decision.reason
                    break
                candidate_state = decision.state
            except (KeyError, TypeError, ValueError) as exc:
                error = str(exc)
                break

        if error is None:
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _autotrader_state_root_v0(working_state)
    return pre_state_root, post_state_root, _autotrader_controller_state_to_obj(working_state), executed_body, receipts


def _confidential_request_table_from_state(state: Mapping[str, Any]) -> object:
    from src.state.confidential_requests import ConfidentialRequestKey, ConfidentialRequestTable

    table = ConfidentialRequestTable()
    raw_used = state.get("used_requests", [])
    if not isinstance(raw_used, list):
        raise TypeError("confidential_state.used_requests must be a list")
    for index, item in enumerate(raw_used):
        if not isinstance(item, Mapping):
            raise TypeError(f"confidential_state.used_requests[{index}] must be an object")
        used = item.get("used", True)
        if not isinstance(used, bool):
            raise TypeError(f"confidential_state.used_requests[{index}].used must be a bool")
        if used:
            table.mark_used(
                ConfidentialRequestKey(
                    extension_id=item.get("extension_id"),
                    provider_id=item.get("provider_id"),
                    request_id=item.get("request_id"),
                )
            )
    return table


def _confidential_request_table_to_used_requests(table: object) -> list[dict[str, Any]]:
    from src.state.confidential_requests import ConfidentialRequestKey, ConfidentialRequestTable

    if not isinstance(table, ConfidentialRequestTable):
        raise TypeError("request_table must be a ConfidentialRequestTable")
    out: list[dict[str, Any]] = []
    for key, used in table.get_all().items():
        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError("confidential request table key must be a ConfidentialRequestKey")
        if bool(used):
            out.append(
                {
                    "extension_id": key.extension_id,
                    "provider_id": key.provider_id,
                    "request_id": key.request_id,
                    "used": True,
                }
            )
    out.sort(key=lambda item: (item["extension_id"], item["provider_id"], item["request_id"]))
    return out


def _revealed_sealed_bid_from_obj(obj: object) -> object:
    from src.core.sealed_bid_auction import RevealedSealedBid

    if not isinstance(obj, Mapping):
        raise TypeError("trusted_plain_bids entries must be objects")
    return RevealedSealedBid(
        bidder_id=obj.get("bidder_id"),
        commitment=obj.get("commitment"),
        quantity=obj.get("quantity"),
        limit_price=obj.get("limit_price"),
    )


def _confidential_state_with_defaults(state: Mapping[str, Any]) -> dict[str, Any]:
    schema = state.get("schema", "zenodex/confidential_ledger_state/v1")
    if schema != "zenodex/confidential_ledger_state/v1":
        raise ValueError("confidential_state schema mismatch")
    approved_measurements = state.get("approved_measurements", [])
    if not isinstance(approved_measurements, list) or not all(isinstance(x, str) and x for x in approved_measurements):
        raise TypeError("confidential_state.approved_measurements must be a non-empty string list")
    approved_fhe_key_ids = state.get("approved_fhe_key_ids", [])
    if not isinstance(approved_fhe_key_ids, list) or not all(isinstance(x, str) and x for x in approved_fhe_key_ids):
        raise TypeError("confidential_state.approved_fhe_key_ids must be a non-empty string list")
    expected_policy_digest = state.get("expected_policy_digest")
    if not isinstance(expected_policy_digest, str) or not expected_policy_digest:
        raise TypeError("confidential_state.expected_policy_digest must be a non-empty string")
    return {
        "schema": schema,
        "approved_measurements": sorted(str(x) for x in approved_measurements),
        "approved_fhe_key_ids": sorted(str(x) for x in approved_fhe_key_ids),
        "expected_policy_digest": expected_policy_digest,
        "used_requests": _confidential_request_table_to_used_requests(_confidential_request_table_from_state(state)),
        "accepted_live_admission_count": int(state.get("accepted_live_admission_count", 0)),
        "accepted_fhe_plan_count": int(state.get("accepted_fhe_plan_count", 0)),
        "last_receipt_hash": state.get("last_receipt_hash"),
        "last_fhe_receipt_hash": state.get("last_fhe_receipt_hash"),
        "last_auction_id": state.get("last_auction_id"),
    }


def _execute_confidential_body_v0(
    *,
    confidential_state: Mapping[str, Any],
    body: dict[str, Any],
) -> tuple[str, str, dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    from src.core.confidential_extension_live_admission import (
        validate_confidential_extension_live_admission,
    )
    from src.core.fhe_sealed_bid_alpha import verify_fhe_sealed_bid_alpha_plan

    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])
    working_state = _confidential_state_with_defaults(confidential_state)
    pre_state_root = _confidential_state_root_v0(working_state)

    for index, tx in enumerate(executed_body["transactions"]):
        if not isinstance(tx, Mapping):
            raise TypeError(f"transactions[{index}] must be an object")
        tx_hash = tx_hash_v0(tx)
        commands = tx.get("confidential_commands")
        if not isinstance(commands, list) or not commands:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(f"transactions[{index}].confidential_commands is required"),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
            receipts.append(receipt)
            continue

        candidate_state = dict(working_state)
        error: str | None = None
        for command_index, raw_command in enumerate(commands):
            if not isinstance(raw_command, Mapping):
                error = f"transactions[{index}].confidential_commands[{command_index}] must be an object"
                break
            action = raw_command.get("action")
            args = raw_command.get("args", {})
            if not isinstance(action, str) or action == "":
                error = f"transactions[{index}].confidential_commands[{command_index}].action is required"
                break
            if not isinstance(args, Mapping):
                error = f"transactions[{index}].confidential_commands[{command_index}].args must be an object"
                break
            try:
                if action == "validate_live_admission":
                    receipt_obj = args.get("receipt")
                    if not isinstance(receipt_obj, Mapping):
                        error = "confidential receipt must be an object"
                        break
                    ok, err, updated_table = validate_confidential_extension_live_admission(
                        receipt=receipt_obj,
                        approved_measurements=candidate_state["approved_measurements"],
                        expected_policy_digest=str(candidate_state["expected_policy_digest"]),
                        request_table=_confidential_request_table_from_state(candidate_state),
                    )
                    if not ok or updated_table is None:
                        error = f"confidential_live_admission_rejected:{err or 'unknown'}"
                        break
                    body_obj = receipt_obj["body"]
                    if not isinstance(body_obj, Mapping):
                        error = "confidential receipt body must be an object"
                        break
                    candidate_state = dict(candidate_state)
                    candidate_state["used_requests"] = _confidential_request_table_to_used_requests(updated_table)
                    candidate_state["accepted_live_admission_count"] = int(
                        candidate_state.get("accepted_live_admission_count", 0)
                    ) + 1
                    candidate_state["last_receipt_hash"] = receipt_obj.get("receipt_hash")
                elif action == "verify_fhe_alpha_plan":
                    receipt_obj = args.get("receipt")
                    if not isinstance(receipt_obj, Mapping):
                        error = "fhe receipt must be an object"
                        break
                    raw_plain_bids = args.get("trusted_plain_bids")
                    if not isinstance(raw_plain_bids, list):
                        error = "trusted_plain_bids must be a list"
                        break
                    plain_bids = [_revealed_sealed_bid_from_obj(item) for item in raw_plain_bids]
                    ok, err = verify_fhe_sealed_bid_alpha_plan(
                        dict(receipt_obj),
                        approved_key_ids=candidate_state["approved_fhe_key_ids"],
                        trusted_plain_bids=plain_bids,  # type: ignore[arg-type]
                    )
                    if not ok:
                        error = f"fhe_alpha_plan_rejected:{err}"
                        break
                    body_obj = receipt_obj["body"]
                    if not isinstance(body_obj, Mapping):
                        error = "fhe receipt body must be an object"
                        break
                    candidate_state = dict(candidate_state)
                    candidate_state["accepted_fhe_plan_count"] = int(
                        candidate_state.get("accepted_fhe_plan_count", 0)
                    ) + 1
                    candidate_state["last_fhe_receipt_hash"] = receipt_obj.get("receipt_hash")
                    candidate_state["last_auction_id"] = body_obj.get("auction_id")
                else:
                    error = f"unknown confidential action: {action}"
                    break
            except (KeyError, TypeError, ValueError) as exc:
                error = str(exc)
                break

        if error is None:
            candidate_state = _confidential_state_with_defaults(candidate_state)
            state_changed = candidate_state != working_state
            working_state = candidate_state
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=True,
                error_code=None,
                state_changed=state_changed,
            )
        else:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=stable_error_code_v0(error),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    post_state_root = _confidential_state_root_v0(working_state)
    return pre_state_root, post_state_root, working_state, executed_body, receipts


def _root_from_app_hash(app_hash_hex: str) -> str:
    return canonical_hex_fixed_allow_0x(app_hash_hex, nbytes=32, name="app_hash")


@contextmanager
def _temporary_env(updates: Mapping[str, str]):
    prior: dict[str, str | None] = {key: os.environ.get(key) for key in updates}
    try:
        for key, value in updates.items():
            os.environ[key] = value
        yield
    finally:
        for key, value in prior.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def _execute_tau_app_body_v0(
    *,
    app_state_json: str,
    body: dict[str, Any],
    chain_balances: dict[str, int],
    tau_chain_id: str,
    allow_missing_settlement: bool,
    require_intent_signatures: bool,
    allow_unsigned_intents_if_tx_sender_matches: bool = False,
    enable_faucet: bool,
    execution_clock: VerifiedExecutionClockV1,
) -> tuple[str, str, str, dict[str, Any], list[dict[str, Any]]]:
    # Keep the Tau bridge optional. Sovereign ZenoLedger modes must not fail to
    # import just because a Tau adapter is absent or rejected upstream.
    from src.integration.tau_testnet_dex_plugin import apply_app_tx

    env = {
        "TAU_DEX_ALLOW_MISSING_SETTLEMENT": "1" if allow_missing_settlement else "0",
        "TAU_DEX_REQUIRE_INTENT_SIGS": "1" if require_intent_signatures else "0",
        "TAU_DEX_ALLOW_UNSIGNED_INTENTS_IF_TX_SENDER_MATCHES": (
            "1" if allow_unsigned_intents_if_tx_sender_matches else "0"
        ),
        "TAU_DEX_FAUCET": "1" if enable_faucet else "0",
        "TAU_DEX_CHAIN_ID": tau_chain_id,
    }
    executed_body = json.loads(json.dumps(body))
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    receipts: list[dict[str, Any]] = []
    height = int(executed_body["height"])

    with _temporary_env(env):
        ok, canonical_state, pre_app_hash, _patch, err = apply_app_tx(
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            operations={},
            tx_sender_pubkey="",
            block_timestamp=execution_clock.height,
            execution_clock=execution_clock,
        )
        if not ok:
            raise ValueError(err or "Tau app state pre-sync rejected")
        app_state_json = canonical_state
        pre_state_root = _root_from_app_hash(pre_app_hash)

        for index, tx in enumerate(executed_body["transactions"]):
            if not isinstance(tx, Mapping):
                raise TypeError(f"transactions[{index}] must be an object")
            tx_hash = tx_hash_v0(tx)
            operations = tx.get("operations")
            sender = tx.get("tx_sender_pubkey")
            if "block_timestamp" in tx:
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=False,
                    error_code=stable_error_code_v0(
                        f"transactions[{index}].block_timestamp is forbidden"
                    ),
                    state_changed=False,
                )
                rejection_receipts.append(receipt)
                receipts.append(receipt)
                continue
            if not isinstance(operations, Mapping):
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=False,
                    error_code=stable_error_code_v0(f"transactions[{index}].operations is required"),
                    state_changed=False,
                )
                rejection_receipts.append(receipt)
                receipts.append(receipt)
                continue
            if sender is None:
                sender = ""
            if not isinstance(sender, str):
                raise TypeError(f"transactions[{index}].tx_sender_pubkey must be a string")

            before_state_json = app_state_json
            ok, next_state_json, _app_hash, _patch, err = apply_app_tx(
                app_state_json=app_state_json,
                chain_balances=chain_balances,
                operations=dict(operations),
                tx_sender_pubkey=sender,
                block_timestamp=execution_clock.height,
                execution_clock=execution_clock,
            )
            if ok:
                app_state_json = next_state_json
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=True,
                    error_code=None,
                    state_changed=app_state_json != before_state_json,
                )
            else:
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=False,
                    error_code=stable_error_code_v0(err),
                    state_changed=False,
                )
                rejection_receipts.append(receipt)
            receipts.append(receipt)

        ok, canonical_state, post_app_hash, _patch, err = apply_app_tx(
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            operations={},
            tx_sender_pubkey="",
            block_timestamp=execution_clock.height,
            execution_clock=execution_clock,
        )
        if not ok:
            raise ValueError(err or "Tau app state post-sync rejected")
        app_state_json = canonical_state
        post_state_root = _root_from_app_hash(post_app_hash)

    validate_body_v0(executed_body)
    return pre_state_root, post_state_root, app_state_json, executed_body, receipts


def build_local_block_v0(
    *,
    body_path: Path,
    out_dir: Path,
    time_ms: int,
    clock_policy_schedule_path: Path | None = None,
    expected_clock_policy_schedule_hash: str | None = None,
    pre_snapshot_path: Path | None = None,
    tau_app_state_path: Path | None = None,
    zusd_state_path: Path | None = None,
    perp_state_path: Path | None = None,
    oracle_state_path: Path | None = None,
    oracle_reporter_state_path: Path | None = None,
    upba_state_path: Path | None = None,
    proof_mining_state_path: Path | None = None,
    autotrader_state_path: Path | None = None,
    confidential_state_path: Path | None = None,
    tau_chain_balances_path: Path | None = None,
    tau_chain_id: str | None = None,
    tau_enable_faucet: bool = False,
    prev_header_path: Path | None = None,
    trusted_prev_header_hash: str = ZERO_ROOT,
    trusted_prev_height: int | None = None,
    pre_state_root: str | None = None,
    post_state_root: str | None = None,
    sequencer_set_hash: str,
    data_availability_root: str,
    proof_journal_hash: str,
    proof_kind: str | None = None,
    proof_program_id: str | None = None,
    proof_verifier_id: str | None = None,
    proof_commitment: str | None = None,
    proof_public_input_hash: str | None = None,
    proof_raw_journal_hash: str | None = None,
    conflict_schedule_hash: str = ZERO_ROOT,
    feature_suite_hash: str = ZERO_ROOT,
    dependency_lock_hash: str = ZERO_ROOT,
    toolchain_lock_hash: str | None = None,
    tee_measurement_hash: str = ZERO_ROOT,
    child_receipts_root: str = ZERO_ROOT,
    config_digest: str,
    module_versions_digest: str,
    signature_set_root: str,
    cross_shard_posting_summary_path: Path | None = None,
    cross_shard_posting_summary_paths: Sequence[Path] | None = None,
    cross_shard_terminal_admission_paths: Sequence[Path] | None = None,
    allow_missing_settlement: bool = False,
    require_intent_signatures: bool = True,
    allow_unsigned_intents_if_tx_sender_matches: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: object | None = None,
) -> dict[str, Any]:
    body = dict(_load_json_object(body_path))
    validate_body_v0(body)
    route_order_receipt_attached = apply_route_order_receipt_policy_to_body_v1(body)
    if route_order_receipt_attached:
        validate_body_v0(body)
    height = int(body["height"])
    chain_id = str(body["chain_id"])
    prev_header: dict[str, Any] | None = None
    if prev_header_path is not None:
        prev_header = dict(_load_json_object(prev_header_path))
        validate_header_v0(prev_header)
        prev_header_hash = canonical_header_hash_v0(prev_header)
        if prev_header["chain_id"] != chain_id:
            raise ValueError("current chain_id must equal previous header chain_id")
        if int(prev_header["height"]) == (1 << 64) - 1:
            raise ValueError("candidate height overflows u64")
        if height != int(prev_header["height"]) + 1:
            raise ValueError("current height must immediately follow previous header height")
    else:
        prev_header_hash = canonical_hex_fixed_allow_0x(
            trusted_prev_header_hash,
            nbytes=32,
            name="trusted_prev_header_hash",
        )
        if tau_app_state_path is not None and height != 0:
            if trusted_prev_height is None:
                raise ValueError(
                    "Tau app execution above genesis requires --prev-header "
                    "or --trusted-prev-height"
                )
            if prev_header_hash == ZERO_ROOT:
                raise ValueError("trusted previous header hash must be non-zero")
            if (
                type(trusted_prev_height) is not int
                or trusted_prev_height < 0
                or trusted_prev_height >= (1 << 64) - 1
            ):
                raise ValueError("trusted previous height must be a valid u64 parent")
            if height != trusted_prev_height + 1:
                raise ValueError("current height must follow trusted previous height")
    receipts: list[dict[str, Any]] = []
    post_snapshot: dict[str, Any] | None = None
    pre_tau_app_state_obj: dict[str, Any] | None = None
    mounted_execution_clock: VerifiedExecutionClockV1 | None = None
    mounted_clock_schedule_hash: str | None = None
    cross_shard_application_results: list[Any] = []
    cross_shard_global_conservation_receipts: list[dict[str, Any]] = []

    supplied_state_modes = sum(
        value is not None
        for value in (
            pre_snapshot_path,
            tau_app_state_path,
            zusd_state_path,
            perp_state_path,
            oracle_state_path,
            oracle_reporter_state_path,
            upba_state_path,
            proof_mining_state_path,
            autotrader_state_path,
            confidential_state_path,
        )
    )
    if supplied_state_modes > 1:
        raise ValueError(
            "--pre-snapshot, --tau-app-state, --zusd-state, --perp-state, --oracle-state, "
            "--oracle-reporter-state, --upba-state, --proof-mining-state, --autotrader-state, "
            "and --confidential-state "
            "are mutually exclusive"
        )

    if pre_snapshot_path is not None:
        pre_snapshot = _load_json_object(pre_snapshot_path)
        pre_state = state_from_snapshot(pre_snapshot)
        pre_state_root = compute_dex_snapshot_app_root_v0(pre_snapshot)
        engine_config = DexEngineConfig(
            allow_missing_settlement=allow_missing_settlement,
            require_intent_signatures=require_intent_signatures,
            allow_unsigned_intents_if_tx_sender_matches=allow_unsigned_intents_if_tx_sender_matches,
            chain_id=chain_id,
            dex_config=DexConfig(
                protocol_fee_share_bps=protocol_fee_share_bps,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            ),
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        )
        post_state, body, receipts = apply_body_transactions_v0(
            state=pre_state,
            body=body,
            config=engine_config,
        )
        post_snapshot = snapshot_from_state(post_state).data
        _preserve_snapshot_app_root_lanes_v0(
            source_snapshot=pre_snapshot,
            target_snapshot=post_snapshot,
        )
        post_state_root = compute_dex_snapshot_app_root_v0(post_snapshot)

    post_app_state_json: str | None = None
    if tau_app_state_path is not None:
        if clock_policy_schedule_path is None:
            clock_schedule = default_height_only_clock_schedule_v1(
                chain_id=chain_id
            )
        else:
            clock_schedule = ClockPolicyScheduleV1.from_obj(
                _load_json_object(clock_policy_schedule_path)
            )
            if expected_clock_policy_schedule_hash is None:
                raise ValueError(
                    "custom --clock-policy-schedule requires "
                    "--clock-policy-schedule-hash"
                )
        computed_schedule_hash = clock_policy_schedule_hash_v1(clock_schedule)
        if expected_clock_policy_schedule_hash is None:
            expected_schedule_hash = computed_schedule_hash
        else:
            expected_schedule_hash = canonical_hex_fixed_allow_0x(
                expected_clock_policy_schedule_hash,
                nbytes=32,
                name="expected_clock_policy_schedule_hash",
            )
        execution_clock = verify_execution_clock_v1(
            chain_id=chain_id,
            height=height,
            schedule=clock_schedule,
            expected_schedule_hash=expected_schedule_hash,
        )
        if execution_clock.deployment_profile.immediate_clock_authority != (
            "zeno_ledger_consensus"
        ):
            raise ValueError(
                "Tau app execution requires a ZenoLedger clock authority profile"
            )
        mounted_execution_clock = execution_clock
        mounted_clock_schedule_hash = computed_schedule_hash
        pre_app_state_json = tau_app_state_path.read_text(encoding="utf-8")
        pre_tau_app_state_obj = _tau_app_state_obj_from_json_v0(pre_app_state_json)
        pre_state_root, post_state_root, post_app_state_json, body, receipts = _execute_tau_app_body_v0(
            app_state_json=pre_app_state_json,
            body=body,
            chain_balances=_load_chain_balances(tau_chain_balances_path),
            tau_chain_id=tau_chain_id or chain_id,
            allow_missing_settlement=allow_missing_settlement,
            require_intent_signatures=require_intent_signatures,
            allow_unsigned_intents_if_tx_sender_matches=allow_unsigned_intents_if_tx_sender_matches,
            enable_faucet=tau_enable_faucet,
            execution_clock=execution_clock,
        )

    post_zusd_state: dict[str, Any] | None = None
    if zusd_state_path is not None:
        pre_zusd_state = _load_zusd_state(zusd_state_path)
        pre_state_root, post_state_root, post_zusd_state, body, receipts = _execute_zusd_body_v0(
            zusd_state=pre_zusd_state,
            body=body,
        )

    post_perp_state: dict[str, Any] | None = None
    if perp_state_path is not None:
        pre_perp_state = _load_perp_state(perp_state_path)
        pre_state_root, post_state_root, post_perp_state, body, receipts = _execute_perp_body_v0(
            perp_state=pre_perp_state,
            body=body,
        )

    post_oracle_state: dict[str, Any] | None = None
    if oracle_state_path is not None:
        pre_oracle_state = _load_oracle_state(oracle_state_path)
        pre_state_root, post_state_root, post_oracle_state, body, receipts = _execute_oracle_body_v0(
            oracle_state=pre_oracle_state,
            body=body,
        )

    post_oracle_reporter_state: dict[str, Any] | None = None
    if oracle_reporter_state_path is not None:
        pre_oracle_reporter_state = _load_oracle_reporter_state(oracle_reporter_state_path)
        pre_state_root, post_state_root, post_oracle_reporter_state, body, receipts = _execute_oracle_reporter_body_v0(
            oracle_reporter_state=pre_oracle_reporter_state,
            body=body,
        )

    post_upba_state: dict[str, Any] | None = None
    if upba_state_path is not None:
        pre_upba_state = _load_upba_state(upba_state_path)
        pre_state_root, post_state_root, post_upba_state, body, receipts = _execute_upba_body_v0(
            upba_state=pre_upba_state,
            body=body,
        )

    post_proof_mining_state: dict[str, Any] | None = None
    if proof_mining_state_path is not None:
        pre_proof_mining_state = _load_proof_mining_state(proof_mining_state_path)
        pre_state_root, post_state_root, post_proof_mining_state, body, receipts = _execute_proof_mining_body_v0(
            proof_mining_state=pre_proof_mining_state,
            body=body,
        )

    post_autotrader_state: dict[str, Any] | None = None
    if autotrader_state_path is not None:
        pre_autotrader_state = _load_autotrader_state(autotrader_state_path)
        pre_state_root, post_state_root, post_autotrader_state, body, receipts = _execute_autotrader_body_v0(
            autotrader_state=pre_autotrader_state,
            body=body,
        )

    post_confidential_state: dict[str, Any] | None = None
    if confidential_state_path is not None:
        pre_confidential_state = _load_confidential_state(confidential_state_path)
        pre_state_root, post_state_root, post_confidential_state, body, receipts = _execute_confidential_body_v0(
            confidential_state=pre_confidential_state,
            body=body,
        )

    normalized_cross_shard_posting_summary_paths = (
        _normalize_cross_shard_posting_summary_paths_v0(
            posting_summary_path=cross_shard_posting_summary_path,
            posting_summary_paths=cross_shard_posting_summary_paths,
        )
    )
    cross_shard_posting_summaries = _load_cross_shard_writer_posting_summaries_v0(
        body=body,
        posting_summary_paths=normalized_cross_shard_posting_summary_paths,
    )
    cross_shard_terminal_admissions = _load_cross_shard_writer_terminal_admissions_v0(
        body=body,
        posting_summaries=cross_shard_posting_summaries,
        terminal_admission_paths=_normalize_cross_shard_terminal_admission_paths_v0(
            cross_shard_terminal_admission_paths
        ),
    )
    cross_shard_ledger_effects_artifacts = tuple(
        build_cross_shard_ledger_effects_artifact_v0(
            posting_summary=posting_summary
        )
        for posting_summary in cross_shard_posting_summaries
    )

    for posting_summary, effects_artifact, terminal_admission in zip(
        cross_shard_posting_summaries,
        cross_shard_ledger_effects_artifacts,
        cross_shard_terminal_admissions,
        strict=True,
    ):
        if post_snapshot is not None:
            post_snapshot, result, receipt = _apply_cross_shard_writer_effects_to_snapshot_v0(
                snapshot=post_snapshot,
                posting_summary=posting_summary,
                effects_artifact=effects_artifact,
                terminal_admission=terminal_admission,
            )
            post_state_root = compute_dex_snapshot_app_root_v0(post_snapshot)
        elif post_app_state_json is not None:
            post_app_state, result, receipt = (
                _apply_cross_shard_writer_effects_to_tau_app_state_v0(
                    app_state_json=post_app_state_json,
                    pre_app_state=pre_tau_app_state_obj,
                    posting_summary=posting_summary,
                    effects_artifact=effects_artifact,
                    terminal_admission=terminal_admission,
                )
            )
            post_app_state_json = _canonical_json_text_v0(post_app_state)
            post_state_root = compute_tau_app_state_app_root_v0(post_app_state)
        else:
            raise ValueError(
                "cross-shard posting summary requires --pre-snapshot or --tau-app-state "
                "to persist replay state"
            )
        cross_shard_application_results.append(result)
        cross_shard_global_conservation_receipts.append(receipt)

    if pre_state_root is None:
        raise ValueError("pre_state_root is required when --pre-snapshot is not supplied")
    if post_state_root is None:
        raise ValueError("post_state_root is required when --pre-snapshot is not supplied")

    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    ingress_root = compute_ingress_root_v0(body["ingress"])  # type: ignore[arg-type]
    tx_root = compute_tx_root_v0(body["transactions"])  # type: ignore[arg-type]
    body_root = canonical_body_root_v0(body)
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )

    proof_metadata: dict[str, Any] | None = None
    if proof_kind is not None:
        if proof_journal_hash != ZERO_ROOT:
            raise ValueError("--proof-kind cannot be combined with --proof-journal-hash")
        missing = [
            name
            for name, value in (
                ("--proof-program-id", proof_program_id),
                ("--proof-verifier-id", proof_verifier_id),
                ("--proof-commitment", proof_commitment),
                ("--proof-public-input-hash", proof_public_input_hash),
                ("--proof-raw-journal-hash", proof_raw_journal_hash),
            )
            if value is None
        ]
        if missing:
            raise ValueError(f"{', '.join(missing)} required when --proof-kind is supplied")
        resolved_toolchain_lock_hash = toolchain_lock_hash or proof_toolchain_lock_hash_v0(ROOT)
        proof_metadata = build_proof_metadata_v0(
            chain_id=chain_id,
            height=height,
            proof_kind=proof_kind,
            program_id=str(proof_program_id),
            verifier_id=str(proof_verifier_id),
            proof_commitment=str(proof_commitment),
            public_input_hash=str(proof_public_input_hash),
            journal_hash=str(proof_raw_journal_hash),
            pre_state_root=pre_state_root,
            post_state_root=post_state_root,
            tx_root=tx_root,
            evidence_root=evidence_root,
            body_root=body_root,
            conflict_schedule_hash=conflict_schedule_hash,
            feature_suite_hash=feature_suite_hash,
            dependency_lock_hash=dependency_lock_hash,
            toolchain_lock_hash=resolved_toolchain_lock_hash,
            tee_measurement_hash=tee_measurement_hash,
            child_receipts_root=child_receipts_root,
        )
        proof_journal_hash = proof_metadata_hash_v0(proof_metadata)

    header = build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=ingress_root,
        tx_root=tx_root,
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=body_root,
        data_availability_root=data_availability_root,
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=signature_set_root,
    )
    if prev_header is not None:
        validate_header_chain_linkage_v0([prev_header, header])
    if proof_metadata is not None:
        validate_proof_metadata_header_binding_v0(proof_metadata, header)
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)

    header_path = out_dir / "headers" / f"{height}.json"
    output_body_path = out_dir / "bodies" / f"{height}.json"
    checkpoint_path = out_dir / "checkpoints" / f"{height}.json"
    receipts_path = out_dir / "receipts" / f"{height}.json"
    proof_metadata_path = out_dir / "proof_metadata" / f"{height}.json"
    cross_shard_artifact_count = len(cross_shard_posting_summaries)
    cross_shard_posting_summary_output_paths = tuple(
        _cross_shard_writer_output_path_v0(
            out_dir=out_dir,
            subdir="cross_shard_posting_summaries",
            height=height,
            index=index,
            count=cross_shard_artifact_count,
        )
        for index in range(cross_shard_artifact_count)
    )
    cross_shard_ledger_effects_output_paths = tuple(
        _cross_shard_writer_output_path_v0(
            out_dir=out_dir,
            subdir="cross_shard_ledger_effects",
            height=height,
            index=index,
            count=cross_shard_artifact_count,
        )
        for index in range(cross_shard_artifact_count)
    )
    cross_shard_terminal_admission_output_paths = tuple(
        _cross_shard_writer_output_path_v0(
            out_dir=out_dir,
            subdir="cross_shard_terminal_admissions",
            height=height,
            index=index,
            count=cross_shard_artifact_count,
        )
        for index in range(cross_shard_artifact_count)
    )
    cross_shard_global_conservation_receipt_output_paths = tuple(
        _cross_shard_writer_output_path_v0(
            out_dir=out_dir,
            subdir="cross_shard_global_conservation_receipts",
            height=height,
            index=index,
            count=cross_shard_artifact_count,
        )
        for index in range(cross_shard_artifact_count)
    )
    post_snapshot_path = out_dir / "snapshots" / f"{height}.json"
    post_app_state_path = out_dir / "app_states" / f"{height}.json"
    post_zusd_state_path = out_dir / "zusd_states" / f"{height}.json"
    post_perp_state_path = out_dir / "perp_states" / f"{height}.json"
    post_oracle_state_path = out_dir / "oracle_states" / f"{height}.json"
    post_oracle_reporter_state_path = out_dir / "oracle_reporter_states" / f"{height}.json"
    post_upba_state_path = out_dir / "upba_states" / f"{height}.json"
    post_proof_mining_state_path = out_dir / "proof_mining_states" / f"{height}.json"
    post_autotrader_state_path = out_dir / "autotrader_states" / f"{height}.json"
    post_confidential_state_path = out_dir / "confidential_states" / f"{height}.json"
    _write_json(header_path, header)
    _write_json(output_body_path, body)
    _write_json(checkpoint_path, checkpoint)
    _write_json(receipts_path, receipts)
    for path, posting_summary in zip(
        cross_shard_posting_summary_output_paths,
        cross_shard_posting_summaries,
        strict=True,
    ):
        _write_json(path, posting_summary)
    for path, effects_artifact in zip(
        cross_shard_ledger_effects_output_paths,
        cross_shard_ledger_effects_artifacts,
        strict=True,
    ):
        _write_json(path, effects_artifact)
    for path, terminal_admission in zip(
        cross_shard_terminal_admission_output_paths,
        cross_shard_terminal_admissions,
        strict=True,
    ):
        _write_json(path, terminal_admission)
    for path, receipt in zip(
        cross_shard_global_conservation_receipt_output_paths,
        cross_shard_global_conservation_receipts,
        strict=True,
    ):
        _write_json(path, receipt)
    if proof_metadata is not None:
        _write_json(proof_metadata_path, proof_metadata)
    if post_snapshot is not None:
        _write_json(post_snapshot_path, post_snapshot)
    if post_app_state_json is not None:
        _write_text(post_app_state_path, post_app_state_json + "\n")
    if post_zusd_state is not None:
        _write_json(post_zusd_state_path, post_zusd_state)
    if post_perp_state is not None:
        _write_json(post_perp_state_path, post_perp_state)
    if post_oracle_state is not None:
        _write_json(post_oracle_state_path, post_oracle_state)
    if post_oracle_reporter_state is not None:
        _write_json(post_oracle_reporter_state_path, post_oracle_reporter_state)
    if post_upba_state is not None:
        _write_json(post_upba_state_path, post_upba_state)
    if post_proof_mining_state is not None:
        _write_json(post_proof_mining_state_path, post_proof_mining_state)
    if post_autotrader_state is not None:
        _write_json(post_autotrader_state_path, post_autotrader_state)
    if post_confidential_state is not None:
        _write_json(post_confidential_state_path, post_confidential_state)

    report = {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "chain_id": chain_id,
        "height": height,
        "header_hash": header_hash,
        "header_path": str(header_path),
        "body_path": str(output_body_path),
        "checkpoint_path": str(checkpoint_path),
        "receipts_path": str(receipts_path),
        "post_state_root": post_state_root,
        "app_hash": app_hash,
    }
    if mounted_execution_clock is not None:
        report["execution_clock"] = {
            "chain_id": mounted_execution_clock.chain_id,
            "consensus_domain_id": mounted_execution_clock.consensus_domain_id,
            "deployment_profile": mounted_execution_clock.deployment_profile.value,
            "height": mounted_execution_clock.height,
            "derived_epoch": mounted_execution_clock.derived_epoch,
            "clock_policy_hash": mounted_execution_clock.clock_policy_hash,
            "clock_policy_schedule_hash": mounted_clock_schedule_hash,
        }
    if proof_metadata is not None:
        report["proof_metadata_path"] = str(proof_metadata_path)
        report["proof_journal_hash"] = proof_journal_hash
    if route_order_receipt_attached:
        report["body_tx_execution_order_commitment_receipt_attached"] = True
    if cross_shard_posting_summaries:
        report["cross_shard_posting_summary_paths"] = [
            str(path) for path in cross_shard_posting_summary_output_paths
        ]
        report["cross_shard_posting_summary_hashes"] = [
            posting_summary["posting_summary_hash"]
            for posting_summary in cross_shard_posting_summaries
        ]
        report["cross_shard_ledger_effects_paths"] = [
            str(path) for path in cross_shard_ledger_effects_output_paths
        ]
        report["cross_shard_ledger_effects_hashes"] = [
            effects_artifact["ledger_effects_hash"]
            for effects_artifact in cross_shard_ledger_effects_artifacts
        ]
        report["cross_shard_terminal_admission_paths"] = [
            str(path) for path in cross_shard_terminal_admission_output_paths
        ]
        report["cross_shard_terminal_admission_hashes"] = [
            terminal_admission["admission_hash"]
            for terminal_admission in cross_shard_terminal_admissions
        ]
        report["cross_shard_global_conservation_receipt_paths"] = [
            str(path) for path in cross_shard_global_conservation_receipt_output_paths
        ]
        report["cross_shard_global_conservation_receipt_hashes"] = [
            receipt["receipt_hash"]
            for receipt in cross_shard_global_conservation_receipts
        ]
    if len(cross_shard_posting_summaries) == 1:
        cross_shard_posting_summary = cross_shard_posting_summaries[0]
        report["cross_shard_posting_summary_path"] = str(
            cross_shard_posting_summary_output_paths[0]
        )
        report["cross_shard_posting_summary_hash"] = cross_shard_posting_summary[
            "posting_summary_hash"
        ]
    if len(cross_shard_ledger_effects_artifacts) == 1:
        cross_shard_ledger_effects = cross_shard_ledger_effects_artifacts[0]
        report["cross_shard_ledger_effects_path"] = str(
            cross_shard_ledger_effects_output_paths[0]
        )
        report["cross_shard_ledger_effects_hash"] = cross_shard_ledger_effects[
            "ledger_effects_hash"
        ]
    if len(cross_shard_terminal_admissions) == 1:
        cross_shard_terminal_admission = cross_shard_terminal_admissions[0]
        report["cross_shard_terminal_admission_path"] = str(
            cross_shard_terminal_admission_output_paths[0]
        )
        report["cross_shard_terminal_admission_hash"] = (
            cross_shard_terminal_admission["admission_hash"]
        )
    if len(cross_shard_global_conservation_receipts) == 1:
        cross_shard_global_conservation_receipt = (
            cross_shard_global_conservation_receipts[0]
        )
        report["cross_shard_global_conservation_receipt_path"] = str(
            cross_shard_global_conservation_receipt_output_paths[0]
        )
        report["cross_shard_global_conservation_receipt_hash"] = (
            cross_shard_global_conservation_receipt["receipt_hash"]
        )
    if cross_shard_application_results:
        report["cross_shard_replay_state_pre_root"] = (
            cross_shard_application_results[0].pre_replay_state_root
        )
        report["cross_shard_replay_state_post_root"] = (
            cross_shard_application_results[-1].post_replay_state_root
        )
        report["cross_shard_replay_transitions"] = [
            {
                "ledger_effects_hash": effects_artifact["ledger_effects_hash"],
                "terminal_admission_hash": result.terminal_admission_hash,
                "pre_replay_state_root": result.pre_replay_state_root,
                "post_replay_state_root": result.post_replay_state_root,
            }
            for effects_artifact, result in zip(
                cross_shard_ledger_effects_artifacts,
                cross_shard_application_results,
                strict=True,
            )
        ]
        report["cross_shard_applied_effect_count"] = sum(
            int(result.applied_effect_count)
            for result in cross_shard_application_results
        )
        report["cross_shard_total_debit_atoms"] = sum(
            int(result.total_debit_atoms)
            for result in cross_shard_application_results
        )
        report["cross_shard_total_credit_atoms"] = sum(
            int(result.total_credit_atoms)
            for result in cross_shard_application_results
        )
    if post_snapshot is not None:
        report["post_snapshot_path"] = str(post_snapshot_path)
    if post_app_state_json is not None:
        report["post_app_state_path"] = str(post_app_state_path)
    if post_zusd_state is not None:
        report["post_zusd_state_path"] = str(post_zusd_state_path)
    if post_perp_state is not None:
        report["post_perp_state_path"] = str(post_perp_state_path)
    if post_oracle_state is not None:
        report["post_oracle_state_path"] = str(post_oracle_state_path)
    if post_oracle_reporter_state is not None:
        report["post_oracle_reporter_state_path"] = str(post_oracle_reporter_state_path)
    if post_upba_state is not None:
        report["post_upba_state_path"] = str(post_upba_state_path)
    if post_proof_mining_state is not None:
        report["post_proof_mining_state_path"] = str(post_proof_mining_state_path)
    if post_autotrader_state is not None:
        report["post_autotrader_state_path"] = str(post_autotrader_state_path)
    if post_confidential_state is not None:
        report["post_confidential_state_path"] = str(post_confidential_state_path)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a local ZenoLedger v0 block envelope from a supplied body"
    )
    parser.add_argument("--body", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--time-ms", required=True, type=int)
    parser.add_argument("--clock-policy-schedule", type=Path)
    parser.add_argument("--clock-policy-schedule-hash")
    parser.add_argument("--pre-snapshot", type=Path)
    parser.add_argument("--tau-app-state", type=Path)
    parser.add_argument("--zusd-state", type=Path)
    parser.add_argument("--perp-state", type=Path)
    parser.add_argument("--oracle-state", type=Path)
    parser.add_argument("--oracle-reporter-state", type=Path)
    parser.add_argument("--upba-state", type=Path)
    parser.add_argument("--proof-mining-state", type=Path)
    parser.add_argument("--autotrader-state", type=Path)
    parser.add_argument("--confidential-state", type=Path)
    parser.add_argument("--tau-chain-balances", type=Path)
    parser.add_argument("--tau-chain-id")
    parser.add_argument("--tau-enable-faucet", action="store_true")
    parser.add_argument("--prev-header", type=Path)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    parser.add_argument("--trusted-prev-height", type=int)
    parser.add_argument("--pre-state-root")
    parser.add_argument("--post-state-root")
    parser.add_argument("--sequencer-set-hash", required=True)
    parser.add_argument("--data-availability-root", default=ZERO_ROOT)
    parser.add_argument("--proof-journal-hash", default=ZERO_ROOT)
    parser.add_argument("--proof-kind")
    parser.add_argument("--proof-program-id")
    parser.add_argument("--proof-verifier-id")
    parser.add_argument("--proof-commitment")
    parser.add_argument("--proof-public-input-hash")
    parser.add_argument("--proof-raw-journal-hash")
    parser.add_argument("--conflict-schedule-hash", default=ZERO_ROOT)
    parser.add_argument("--feature-suite-hash", default=ZERO_ROOT)
    parser.add_argument("--dependency-lock-hash", default=ZERO_ROOT)
    parser.add_argument("--toolchain-lock-hash")
    parser.add_argument("--tee-measurement-hash", default=ZERO_ROOT)
    parser.add_argument("--child-receipts-root", default=ZERO_ROOT)
    parser.add_argument("--config-digest", required=True)
    parser.add_argument("--module-versions-digest", required=True)
    parser.add_argument("--signature-set-root", default=ZERO_ROOT)
    parser.add_argument("--cross-shard-posting-summary", type=Path, action="append")
    parser.add_argument("--cross-shard-terminal-admission", type=Path, action="append")
    parser.add_argument("--allow-missing-settlement", action="store_true")
    parser.add_argument("--disable-intent-signatures", action="store_true")
    args = parser.parse_args(argv)

    try:
        result = build_local_block_v0(
            body_path=args.body,
            out_dir=args.out_dir,
            time_ms=args.time_ms,
            clock_policy_schedule_path=args.clock_policy_schedule,
            expected_clock_policy_schedule_hash=args.clock_policy_schedule_hash,
            pre_snapshot_path=args.pre_snapshot,
            tau_app_state_path=args.tau_app_state,
            zusd_state_path=args.zusd_state,
            perp_state_path=args.perp_state,
            oracle_state_path=args.oracle_state,
            oracle_reporter_state_path=args.oracle_reporter_state,
            upba_state_path=args.upba_state,
            proof_mining_state_path=args.proof_mining_state,
            autotrader_state_path=args.autotrader_state,
            confidential_state_path=args.confidential_state,
            tau_chain_balances_path=args.tau_chain_balances,
            tau_chain_id=args.tau_chain_id,
            tau_enable_faucet=args.tau_enable_faucet,
            prev_header_path=args.prev_header,
            trusted_prev_header_hash=args.trusted_prev_header_hash,
            trusted_prev_height=args.trusted_prev_height,
            pre_state_root=args.pre_state_root,
            post_state_root=args.post_state_root,
            sequencer_set_hash=args.sequencer_set_hash,
            data_availability_root=args.data_availability_root,
            proof_journal_hash=args.proof_journal_hash,
            proof_kind=args.proof_kind,
            proof_program_id=args.proof_program_id,
            proof_verifier_id=args.proof_verifier_id,
            proof_commitment=args.proof_commitment,
            proof_public_input_hash=args.proof_public_input_hash,
            proof_raw_journal_hash=args.proof_raw_journal_hash,
            conflict_schedule_hash=args.conflict_schedule_hash,
            feature_suite_hash=args.feature_suite_hash,
            dependency_lock_hash=args.dependency_lock_hash,
            toolchain_lock_hash=args.toolchain_lock_hash,
            tee_measurement_hash=args.tee_measurement_hash,
            child_receipts_root=args.child_receipts_root,
            config_digest=args.config_digest,
            module_versions_digest=args.module_versions_digest,
            signature_set_root=args.signature_set_root,
            cross_shard_posting_summary_paths=args.cross_shard_posting_summary,
            cross_shard_terminal_admission_paths=args.cross_shard_terminal_admission,
            allow_missing_settlement=args.allow_missing_settlement,
            require_intent_signatures=not args.disable_intent_signatures,
            allow_unsigned_intents_if_tx_sender_matches=args.disable_intent_signatures,
        )
    except Exception as exc:
        result = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
