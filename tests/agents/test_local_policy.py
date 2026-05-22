from __future__ import annotations

import json

import pytest

from src.agents.local_policy import (
    LOCAL_POLICY_SCHEMA,
    dump_local_policy_document,
    load_local_policy_file,
    parse_local_policy_document,
)
from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)


def _strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="strat.alpha",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=75, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=10, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )


def test_local_policy_roundtrip_document() -> None:
    strategy = _strategy()
    document = dump_local_policy_document(strategy)
    assert document["schema"] == LOCAL_POLICY_SCHEMA
    parsed = parse_local_policy_document(document)
    assert parsed.to_dict() == strategy.to_dict()


def test_load_local_policy_file(tmp_path) -> None:
    strategy = _strategy()
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(dump_local_policy_document(strategy)), encoding="utf-8")
    loaded = load_local_policy_file(path)
    assert loaded.strategy_hash_hex() == strategy.strategy_hash_hex()


def test_parse_local_policy_rejects_wrong_schema() -> None:
    with pytest.raises(ValueError, match="unsupported local policy schema"):
        parse_local_policy_document({"schema": "wrong", "strategy": {}})


def test_parse_local_policy_rejects_non_mapping() -> None:
    with pytest.raises(TypeError, match="local policy document must be a mapping"):
        parse_local_policy_document(["bad"])  # type: ignore[arg-type]


def test_parse_local_policy_rejects_missing_strategy_object() -> None:
    with pytest.raises(ValueError, match="local policy document.strategy must be an object"):
        parse_local_policy_document({"schema": LOCAL_POLICY_SCHEMA, "strategy": "bad"})
