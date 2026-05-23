from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

from .strategy_ir import StrategyIR, strategy_ir_from_dict

LOCAL_POLICY_SCHEMA = "zenodex/local-policy/v1"


def parse_local_policy_document(document: Mapping[str, Any]) -> StrategyIR:
    if not isinstance(document, Mapping):
        raise TypeError("local policy document must be a mapping")
    schema = document.get("schema")
    if schema != LOCAL_POLICY_SCHEMA:
        raise ValueError(f"unsupported local policy schema: {schema!r}")
    strategy = document.get("strategy")
    if not isinstance(strategy, Mapping):
        raise ValueError("local policy document.strategy must be an object")
    return strategy_ir_from_dict(strategy)


def load_local_policy_file(path: str | Path) -> StrategyIR:
    p = Path(path)
    data = json.loads(p.read_text(encoding="utf-8"))
    return parse_local_policy_document(data)


def dump_local_policy_document(strategy: StrategyIR) -> dict[str, Any]:
    return {
        "schema": LOCAL_POLICY_SCHEMA,
        "strategy": strategy.to_dict(),
    }
