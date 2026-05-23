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
    zenograph_runtime_facts,
)
from src.agents.zenograph_rules import ZGTrustTier  # noqa: E402
from src.integration.autotrader_risk_disclosure import (  # noqa: E402
    build_autotrader_risk_disclosure,
)
from src.integration.zenograph_autotrader_adapter import (  # noqa: E402
    build_zenograph_autotrader_advisory_observation,
)
from src.integration.zenograph_ranking_stage import (  # noqa: E402
    build_zenograph_autotrader_ranking_stage_observation,
)
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


def _load_trust_tier(value: object) -> ZGTrustTier:
    if value is None:
        return ZGTrustTier.ADVISORY
    if not isinstance(value, str):
        raise ValueError("zenograph_source_trust must be a string")
    try:
        return ZGTrustTier(value)
    except ValueError as exc:
        raise ValueError(f"unsupported zenograph_source_trust: {value!r}") from exc


def _infer_current_epoch(receipt: Mapping[str, object]) -> int:
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        raise ValueError("receipt.body must be an object to infer current_epoch")
    value = body.get("quote_epoch")
    if not isinstance(value, int):
        raise ValueError("receipt.body.quote_epoch must be an integer to infer current_epoch")
    return int(value)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a ranking-only ZenoGraph staging observation. Never affects execution.",
        epilog=(
            "Advanced experimental automation and AI staging tool. "
            "This surface is ranking-only and remains at your own risk."
        ),
    )
    parser.add_argument("--policy-file", required=True, type=Path)
    parser.add_argument("--receipt-file", required=True, type=Path)
    parser.add_argument("--pools-file", required=True, type=Path)
    parser.add_argument("--gate-report-file", required=True, type=Path)
    parser.add_argument("--current-epoch", type=int, default=None)
    parser.add_argument("--chain-id", type=str, default="tau-net-alpha")
    parser.add_argument("--zenograph-facts-file", type=Path, default=None)
    parser.add_argument("--zenograph-fact-pack-file", type=Path, default=None)
    parser.add_argument("--zenograph-signals-file", type=Path, default=None)
    parser.add_argument("--zenograph-user-state-file", type=Path, default=None)
    parser.add_argument("--zenograph-source-trust", type=str, default="advisory")
    parser.add_argument("--zenograph-liquidity-state", type=str, default=None)
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    policy_document = _load_json(args.policy_file)
    if not isinstance(policy_document, Mapping):
        raise ValueError("policy-file must contain an object")
    strategy = parse_local_policy_document(policy_document)
    receipt = _load_json(args.receipt_file)
    if not isinstance(receipt, Mapping):
        raise ValueError("receipt-file must contain an object")
    pools = _load_pools(_load_json(args.pools_file))
    gate_report = _load_json(args.gate_report_file)
    if not isinstance(gate_report, Mapping):
        raise ValueError("gate-report-file must contain an object")

    if args.zenograph_fact_pack_file is not None and args.zenograph_facts_file is not None:
        raise ValueError("use either --zenograph-fact-pack-file or --zenograph-facts-file")
    if args.zenograph_fact_pack_file is not None:
        facts = zenograph_runtime_facts(load_zenograph_fact_pack_file(args.zenograph_fact_pack_file))
    elif args.zenograph_facts_file is not None:
        facts = _load_facts(_load_json(args.zenograph_facts_file))
    else:
        facts = {}

    signals = {}
    if args.zenograph_signals_file is not None:
        signals_payload = _load_json(args.zenograph_signals_file)
        if not isinstance(signals_payload, Mapping):
            raise ValueError("zenograph-signals-file must contain an object")
        signals = dict(signals_payload)

    user_state = {}
    if args.zenograph_user_state_file is not None:
        user_state_payload = _load_json(args.zenograph_user_state_file)
        if not isinstance(user_state_payload, Mapping):
            raise ValueError("zenograph-user-state-file must contain an object")
        user_state = dict(user_state_payload)

    current_epoch = (
        _infer_current_epoch(receipt)
        if args.current_epoch is None
        else int(args.current_epoch)
    )

    advisory = build_zenograph_autotrader_advisory_observation(
        strategy=strategy,
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=current_epoch,
        chain_id=args.chain_id,
        facts=facts,
        signals=signals,
        user_state=user_state,
        source_trust=_load_trust_tier(args.zenograph_source_trust),
        liquidity_state=args.zenograph_liquidity_state,
        include_krr=False,
    )
    stage = build_zenograph_autotrader_ranking_stage_observation(
        strategy=strategy,
        advisory=advisory,
        gate_report=gate_report,
    )

    payload = {
        "schema": "zenodex/zenograph-autotrader-ranking-stage-report/v1",
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="shadow",
            requires_explicit_acknowledgement=False,
            user_acknowledged=False,
        ),
        "ranking_stage": stage.to_dict(),
        "zenograph_advisory": advisory.to_dict(),
        "source_gate_report_schema": gate_report.get("schema"),
    }

    text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
