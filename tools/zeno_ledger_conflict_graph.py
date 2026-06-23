#!/usr/bin/env python3
"""Build a conservative ZenoLedger transaction conflict graph."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_conflict_graph_v0 import (
    build_conflict_graph_v0,
    build_conflict_schedule_v0,
)
from src.integration.zeno_ledger_v0 import validate_body_v0


def _load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _transactions_from_input(*, body_path: Path | None, txs_path: Path | None) -> list[object]:
    if (body_path is None) == (txs_path is None):
        raise ValueError("provide exactly one of --body or --transactions")
    if body_path is not None:
        body = _load_json(body_path)
        if not isinstance(body, dict):
            raise ValueError("--body must decode to a JSON object")
        validate_body_v0(body)
        transactions = body.get("transactions")
        if not isinstance(transactions, list):
            raise ValueError("body.transactions must be a list")
        return list(transactions)
    raw = _load_json(txs_path)  # type: ignore[arg-type]
    if not isinstance(raw, list):
        raise ValueError("--transactions must decode to a JSON list")
    return list(raw)


def build_conflict_graph_report_v0(
    *,
    body_path: Path | None = None,
    txs_path: Path | None = None,
    max_parallel_components: int | None = None,
) -> dict[str, Any]:
    transactions = _transactions_from_input(body_path=body_path, txs_path=txs_path)
    graph = build_conflict_graph_v0(transactions)
    schedule = build_conflict_schedule_v0(
        transactions,
        max_parallel_components=max_parallel_components,
    )
    return {
        "schema": "zenodex.zeno_ledger.conflict_graph_report.v0",
        "ok": True,
        "status": "accepted",
        "source": {
            "body_path": str(body_path) if body_path is not None else None,
            "transactions_path": str(txs_path) if txs_path is not None else None,
        },
        "transaction_count": graph["transaction_count"],
        "edge_count": graph["edge_count"],
        "parallel_component_count": graph["component_count"],
        "conflict_graph": graph,
        "conflict_schedule": schedule,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--body", type=Path, help="ZenoLedger body JSON")
    source.add_argument("--transactions", type=Path, help="JSON list of transactions")
    parser.add_argument(
        "--max-parallel-components",
        type=int,
        help="Limit scheduled components per wave; omit to schedule all independent components together.",
    )
    parser.add_argument("--out", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        report = build_conflict_graph_report_v0(
            body_path=args.body,
            txs_path=args.transactions,
            max_parallel_components=args.max_parallel_components,
        )
        if args.out is not None:
            _write_json(args.out, report)
            report = {**report, "report_path": str(args.out)}
    except Exception as exc:
        report = {
            "schema": "zenodex.zeno_ledger.conflict_graph_report.v0",
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
