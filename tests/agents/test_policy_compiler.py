from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.agents.policy_compiler as policy_compiler
from src.agents.policy_compiler import compile_policy_candidate


def _candidate(**overrides: object) -> dict[str, object]:
    candidate: dict[str, object] = {
        "strategy_id": "dca.1",
        "owner_pubkey": "owner.pubkey.1",
        "policy_backend": "local",
        "template": "dca",
        "asset_universe": ["BTC", "zUSD"],
        "notional_caps": {
            "per_order_max": 100,
            "per_window_max": 500,
            "lifetime_max": 1_000,
        },
        "risk_limits": {
            "max_slippage_bps": 100,
            "max_oracle_staleness_epochs": 3,
        },
        "strategy_window": {
            "valid_from_epoch": 1,
            "valid_until_epoch": 100,
        },
        "template_params": {
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
    }
    candidate.update(overrides)
    return candidate


def test_compile_policy_candidate_dca_defaults_actions() -> None:
    result = compile_policy_candidate(_candidate())
    assert result.strategy.template.value == "dca"
    assert [action.value for action in result.strategy.allowed_actions] == ["place_swap_exact_in"]
    assert result.explain[0] == "template=dca"


def test_compile_policy_candidate_accepts_alias_allowed_actions() -> None:
    result = compile_policy_candidate(
        _candidate(strategy_id="dca.alias.1", allowed_actions=["order_intent", "swap exact in"])
    )
    assert [action.value for action in result.strategy.allowed_actions] == [
        "place_order_intent",
        "place_swap_exact_in",
    ]


def test_compile_policy_candidate_rejects_missing_required_template_params() -> None:
    with pytest.raises(ValueError, match="template_params missing required keys"):
        compile_policy_candidate(_candidate(template_params={"fixed_order_size": 100}))


def test_compile_policy_candidate_rejects_unsupported_template() -> None:
    with pytest.raises(ValueError):
        compile_policy_candidate(_candidate(strategy_id="x", template="martingale"))


def test_compile_policy_candidate_accepts_template_alias_and_default_backend() -> None:
    result = compile_policy_candidate(
        _candidate(
            policy_backend=None,
            template="stop",
            template_params={
                "trigger_price": 1_500,
                "fixed_order_size": 100,
                "asset_in": "zUSD",
                "asset_out": "BTC",
            },
        )
    )
    assert result.strategy.policy_backend.value == "local"
    assert result.strategy.template.value == "stop_loss"


def test_compile_policy_candidate_accepts_none_template_params() -> None:
    with pytest.raises(ValueError, match="template_params missing required keys"):
        compile_policy_candidate(_candidate(template_params=None))


@pytest.mark.parametrize(
    ("field", "value", "match"),
    [
        ("notional_caps", "bad", "notional_caps must be an object"),
        ("risk_limits", "bad", "risk_limits must be an object"),
        ("strategy_window", "bad", "strategy_window must be an object"),
        ("controls", "bad", "controls must be an object"),
        ("asset_universe", "bad", "asset_universe must be a list"),
        ("template_params", ["bad"], "template_params must be an object"),
        ("allowed_actions", "bad", "allowed_actions must be a list"),
    ],
)
def test_compile_policy_candidate_rejects_bad_shapes(field: str, value: object, match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        compile_policy_candidate(_candidate(**{field: value}))


def test_compile_policy_candidate_rejects_non_mapping_candidate() -> None:
    with pytest.raises(TypeError, match="candidate must be a mapping"):
        compile_policy_candidate(["bad"])  # type: ignore[arg-type]


def test_compile_policy_candidate_rejects_bad_backend_type() -> None:
    with pytest.raises(TypeError, match="policy_backend must be a string"):
        compile_policy_candidate(_candidate(policy_backend=1))


def test_compile_policy_candidate_rejects_non_string_template() -> None:
    with pytest.raises(TypeError, match="template must be a string"):
        compile_policy_candidate(_candidate(template=1))


def test_compile_policy_candidate_rejects_bad_allowed_action_entries() -> None:
    with pytest.raises(TypeError, match="allowed_actions entries must be strings"):
        compile_policy_candidate(_candidate(allowed_actions=[1]))  # type: ignore[list-item]
    with pytest.raises(ValueError, match="allowed_actions must be non-empty"):
        compile_policy_candidate(_candidate(allowed_actions=[]))
    with pytest.raises(ValueError):
        compile_policy_candidate(_candidate(allowed_actions=["invent_a_trade"]))


def test_compile_policy_candidate_deduplicates_allowed_actions() -> None:
    result = compile_policy_candidate(
        _candidate(allowed_actions=["swap exact in", "swap_exact_in", "order_intent"])
    )
    assert [action.value for action in result.strategy.allowed_actions] == [
        "place_swap_exact_in",
        "place_order_intent",
    ]


def test_compile_policy_candidate_fails_closed_on_compile_contract_reject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        policy_compiler,
        "check_strategy_compile_contract",
        lambda strategy: SimpleNamespace(ok=False, error="compile_contract_rejected"),
    )
    with pytest.raises(ValueError, match="strategy compile contract rejected: compile_contract_rejected"):
        compile_policy_candidate(_candidate())


def test_compile_policy_candidate_rejects_action_scope_outside_template_contract() -> None:
    with pytest.raises(ValueError, match="strategy compile contract rejected: allowed_actions_invalid"):
        compile_policy_candidate(_candidate(strategy_id="dca.bad_action", allowed_actions=["order_intent"]))


def test_compile_policy_candidate_rejects_assets_outside_template_contract() -> None:
    with pytest.raises(ValueError, match="strategy compile contract rejected: asset_scope_invalid"):
        compile_policy_candidate(_candidate(strategy_id="dca.bad_assets", asset_universe=["BTC", "ETH"]))
