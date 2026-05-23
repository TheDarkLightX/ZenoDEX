#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.local_policy import parse_local_policy_document  # noqa: E402
from src.agents.zenograph_fact_pack import (  # noqa: E402
    load_zenograph_fact_pack_file,
    zenograph_fact_pack_from_dict,
    zenograph_runtime_facts,
)
from src.agents.zenograph_rules import ZGTrustTier  # noqa: E402
from src.integration.autotrader_controller import (  # noqa: E402
    AutoTraderControllerState,
    AutoTraderTauConfig,
)
from src.integration.zenograph_shadow_compare import (  # noqa: E402
    build_zenograph_autotrader_shadow_comparison,
)
from src.kernels.python.strategy_budget_guard_v1_adapter import StrategyBudgetState  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _pool_status(value: object) -> PoolStatus:
    if not isinstance(value, str):
        raise ValueError("pool status must be a string")
    return PoolStatus(value.strip().upper())


def _pool_from_object(data: Mapping[str, object]) -> PoolState:
    return PoolState(
        pool_id=str(data["pool_id"]),
        asset0=str(data["asset0"]),
        asset1=str(data["asset1"]),
        reserve0=int(data["reserve0"]),
        reserve1=int(data["reserve1"]),
        fee_bps=int(data.get("fee_bps", 0)),
        lp_supply=int(data.get("lp_supply", 1)),
        status=_pool_status(data.get("status", "ACTIVE")),
        created_at=int(data.get("created_at", 0)),
        curve_tag=str(data.get("curve_tag", "CPMM")),
        curve_params=str(data.get("curve_params", "")),
    )


def _load_pools(payload: object) -> dict[str, PoolState]:
    if isinstance(payload, list):
        pools = {}
        for row in payload:
            if not isinstance(row, Mapping):
                raise ValueError("pool entries must be objects")
            pool = _pool_from_object(row)
            pools[pool.pool_id] = pool
        return pools
    if isinstance(payload, Mapping):
        if "pools" in payload:
            return _load_pools(payload["pools"])
        return {str(pid): _pool_from_object(row) for pid, row in payload.items()}
    raise ValueError("pools must be a list or object")


def _load_facts(payload: object) -> dict[tuple[str, str], object]:
    if payload is None:
        return {}
    if isinstance(payload, Mapping):
        if "facts" in payload:
            return _load_facts(payload["facts"])
        out: dict[tuple[str, str], object] = {}
        for subject_id, predicates in payload.items():
            if not isinstance(subject_id, str) or not isinstance(predicates, Mapping):
                raise ValueError("nested facts form must map subject_id -> predicate object")
            for predicate, value in predicates.items():
                if not isinstance(predicate, str):
                    raise ValueError("fact predicate must be a string")
                out[(subject_id, predicate)] = value
        return out
    if isinstance(payload, list):
        out: dict[tuple[str, str], object] = {}
        for row in payload:
            if not isinstance(row, Mapping):
                raise ValueError("fact entries must be objects")
            subject_id = row.get("subject_id")
            predicate = row.get("predicate")
            if not isinstance(subject_id, str) or not isinstance(predicate, str):
                raise ValueError("fact entries require string subject_id and predicate")
            if "value" in row:
                out[(subject_id, predicate)] = row["value"]
            elif "object_id" in row:
                out[(subject_id, predicate)] = row["object_id"]
            else:
                raise ValueError("fact entries require value or object_id")
        return out
    raise ValueError("facts must be an object or list")


def _load_controller_state(payload: object) -> AutoTraderControllerState:
    if payload is None:
        return AutoTraderControllerState()
    if not isinstance(payload, Mapping):
        raise ValueError("controller_state must be an object")
    budget_raw = payload.get("budget_state", {})
    if not isinstance(budget_raw, Mapping):
        raise ValueError("controller_state.budget_state must be an object")
    return AutoTraderControllerState(
        budget_state=StrategyBudgetState(
            window_id=int(budget_raw.get("window_id", 0)),
            spent_in_window=int(budget_raw.get("spent_in_window", 0)),
            kill_switch_on=bool(budget_raw.get("kill_switch_on", False)),
        ),
        last_action_epoch=None
        if payload.get("last_action_epoch") is None
        else int(payload["last_action_epoch"]),
        lifetime_spent=int(payload.get("lifetime_spent", 0)),
        live_orders=int(payload.get("live_orders", 0)),
    )


def _load_trust_tier(value: object) -> ZGTrustTier:
    if value is None:
        return ZGTrustTier.ADVISORY
    if not isinstance(value, str):
        raise ValueError("zenograph_source_trust must be a string")
    try:
        return ZGTrustTier(value)
    except ValueError as exc:
        raise ValueError(f"unsupported zenograph_source_trust: {value!r}") from exc


def _cases_from_payload(payload: Mapping[str, object]) -> list[dict[str, object]]:
    if not isinstance(payload, Mapping):
        raise ValueError("input must be an object")
    raw_cases = payload.get("cases")
    if not isinstance(raw_cases, list) or not raw_cases:
        raise ValueError("input must contain a non-empty cases list")
    cases: list[dict[str, object]] = []
    for index, raw_case in enumerate(raw_cases):
        if not isinstance(raw_case, Mapping):
            raise ValueError(f"case[{index}] must be an object")
        policy_document = raw_case.get("policy_document")
        receipt = raw_case.get("receipt")
        pools = raw_case.get("pools")
        if not isinstance(policy_document, Mapping):
            raise ValueError(f"case[{index}] missing policy_document")
        if not isinstance(receipt, Mapping):
            raise ValueError(f"case[{index}] missing receipt")
        cases.append(
            {
                "case_id": str(raw_case.get("case_id", f"case-{index}")),
                "strategy": parse_local_policy_document(policy_document),
                "receipt": dict(receipt),
                "pools_by_id": _load_pools(pools),
                "controller_state": _load_controller_state(raw_case.get("controller_state")),
                "current_epoch": int(raw_case.get("current_epoch", 0)),
                "intent_deadline": int(raw_case.get("intent_deadline", 0)),
                "chain_id": str(raw_case.get("chain_id", "tau-net-alpha")),
                "facts": (
                    zenograph_runtime_facts(
                        zenograph_fact_pack_from_dict(raw_case["zenograph_fact_pack"])
                    )
                    if "zenograph_fact_pack" in raw_case
                    else _load_facts(raw_case.get("zenograph_facts"))
                ),
                "signals": dict(raw_case.get("zenograph_signals", {})),
                "user_state": dict(raw_case.get("zenograph_user_state", {})),
                "source_trust": _load_trust_tier(raw_case.get("zenograph_source_trust")),
                "liquidity_state": raw_case.get("zenograph_liquidity_state"),
                "controller_slippage_bps": (
                    None
                    if raw_case.get("controller_slippage_bps") is None
                    else int(raw_case.get("controller_slippage_bps"))
                ),
            }
        )
    return cases


def _load_cases(path: Path) -> list[dict[str, object]]:
    payload = _load_json(path)
    return _cases_from_payload(payload)


def _run_compare_cases(
    *,
    input_path: Path,
    cases: list[dict[str, object]],
    report_path: Path | None = None,
    log_path: Path | None = None,
) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for case in cases:
        observation = build_zenograph_autotrader_shadow_comparison(
            strategy=case["strategy"],
            controller_state=case["controller_state"],
            receipt=case["receipt"],
            pools_by_id=case["pools_by_id"],
            current_epoch=int(case["current_epoch"]),
            intent_deadline=int(case["intent_deadline"]),
            chain_id=str(case["chain_id"]),
            facts=case["facts"],
            signals=case["signals"],
            user_state=case["user_state"],
            source_trust=case["source_trust"],
            liquidity_state=case["liquidity_state"],
            controller_slippage_bps=case["controller_slippage_bps"],
            tau_config=AutoTraderTauConfig(enabled=False),
        )
        row = observation.to_dict()
        row["case_id"] = case["case_id"]
        rows.append(row)

    controller_tag_counts: dict[str, int] = {}
    template_counts: dict[str, int] = {}
    current_disagreement_count = 0
    selected_mismatch_count = 0
    submit_vs_block_count = 0
    block_vs_allow_count = 0
    for row in rows:
        controller_tag = str(row["controller_tag"])
        current_template = str(row["disagreement"]["current_template"])
        controller_tag_counts[controller_tag] = controller_tag_counts.get(controller_tag, 0) + 1
        template_counts[current_template] = template_counts.get(current_template, 0) + 1
        disagreement = row["disagreement"]
        current_disagreement_count += int(bool(disagreement["disagreement"]))
        selected_mismatch_count += int(bool(disagreement["selected_template_mismatch"]))
        submit_vs_block_count += int(bool(disagreement["controller_submit_vs_zenograph_block"]))
        block_vs_allow_count += int(bool(disagreement["controller_block_vs_zenograph_allow"]))

    case_count = float(len(rows))
    report = {
        "schema": "zenodex/zenograph-autotrader-shadow-compare-report/v1",
        "input_path": str(input_path),
        "case_count": len(rows),
        "controller_tag_summary": {
            tag: int(controller_tag_counts[tag]) for tag in sorted(controller_tag_counts)
        },
        "template_summary": {
            template: int(template_counts[template]) for template in sorted(template_counts)
        },
        "disagreement_rate": current_disagreement_count / case_count,
        "selected_template_mismatch_rate": selected_mismatch_count / case_count,
        "controller_submit_vs_zenograph_block_rate": submit_vs_block_count / case_count,
        "controller_block_vs_zenograph_allow_rate": block_vs_allow_count / case_count,
        "first_disagreement": next(
            (row for row in rows if bool(row["disagreement"]["disagreement"])),
            None,
        ),
        "log_path": None if log_path is None else str(log_path),
    }

    if log_path is not None:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        with log_path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, sort_keys=True) + "\n")

    if report_path is not None:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return report


def run_compare_file(
    *,
    input_path: Path,
    report_path: Path | None = None,
    log_path: Path | None = None,
) -> dict[str, object]:
    return _run_compare_cases(
        input_path=input_path,
        cases=_load_cases(input_path),
        report_path=report_path,
        log_path=log_path,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Replay local-policy auto-trader cases and compare controller decisions against ZenoGraph advisory outputs."
    )
    parser.add_argument("--input", type=Path, required=True, help="JSON file containing replay cases.")
    parser.add_argument(
        "--zenograph-fact-pack-file",
        type=Path,
        default=None,
        help="Optional reviewed signed ZenoGraph fact pack for single-case inputs without embedded facts.",
    )
    parser.add_argument("--report-out", type=Path, default=None, help="Optional path for the summary JSON report.")
    parser.add_argument("--log-out", type=Path, default=None, help="Optional path for the per-case JSONL log.")
    args = parser.parse_args()

    if args.zenograph_fact_pack_file is not None:
        payload = _load_json(args.input)
        if not isinstance(payload, Mapping):
            raise ValueError("input must be an object")
        raw_cases = payload.get("cases")
        if not isinstance(raw_cases, list):
            raise ValueError("input must contain a cases list")
        if len(raw_cases) != 1:
            raise ValueError("--zenograph-fact-pack-file requires a single-case input")
        if "zenograph_facts" in raw_cases[0] or "zenograph_fact_pack" in raw_cases[0]:
            raise ValueError(
                "--zenograph-fact-pack-file cannot be combined with embedded zenograph facts"
            )
        pack = load_zenograph_fact_pack_file(args.zenograph_fact_pack_file)
        raw_cases[0] = dict(raw_cases[0])
        raw_cases[0]["zenograph_fact_pack"] = pack.to_dict()
        cases = _cases_from_payload(dict(payload))
        report = _run_compare_cases(
            input_path=args.input,
            cases=cases,
            report_path=args.report_out,
            log_path=args.log_out,
        )
    else:
        report = run_compare_file(
            input_path=args.input,
            report_path=args.report_out,
            log_path=args.log_out,
        )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
