from __future__ import annotations

import json

import pytest

from src.agents.strategy_ir import (
    _LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V1,
    _LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V2,
    AUTOTRADER_TAU_POLICY_SPECS,
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
    _normalize_scalar,
    _normalize_string_tuple,
    _require_int,
    _require_safe_token,
    strategy_budget_window_duration_epochs,
    strategy_budget_window_id,
    strategy_ir_from_dict,
)


def _make_strategy(
    *,
    backend: PolicyBackend = PolicyBackend.LOCAL,
    tau_policy_specs: tuple[str, ...] = (),
    tau_policy_spec: str | None = None,
) -> StrategyIR:
    return StrategyIR(
        strategy_id="strat.alpha",
        owner_pubkey="owner.pubkey.1",
        policy_backend=backend,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100, min_order_spacing_epochs=1),
        controls=StrategyControls(kill_switch_enabled=True, max_live_orders=2),
        template_params={
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
            "enabled": True,
        },
        tau_policy_specs=tau_policy_specs,
        tau_policy_spec=tau_policy_spec,
    )


def test_require_safe_token_accepts_allow_empty() -> None:
    assert _require_safe_token("   ", name="token", allow_empty=True) == ""


@pytest.mark.parametrize(
    ("value", "name", "match"),
    [
        (1, "token", "token must be a string"),
        ("   ", "token", "token must be non-empty"),
        ("bad token", "token", "token contains unsupported characters"),
    ],
)
def test_require_safe_token_rejects_invalid_values(value: object, name: str, match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        _require_safe_token(value, name=name)


def test_require_int_accepts_bounds() -> None:
    assert _require_int(5, name="n", minimum=1, maximum=10) == 5


@pytest.mark.parametrize(
    ("value", "kwargs", "match"),
    [
        (True, {"name": "n"}, "n must be an int"),
        ("5", {"name": "n"}, "n must be an int"),
        (0, {"name": "n", "minimum": 1}, "n must be >= 1"),
        (11, {"name": "n", "maximum": 10}, "n must be <= 10"),
    ],
)
def test_require_int_rejects_invalid_values(value: object, kwargs: dict[str, object], match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        _require_int(value, **kwargs)


def test_normalize_scalar_accepts_supported_types() -> None:
    assert _normalize_scalar(True, name="x") is True
    assert _normalize_scalar(7, name="x") == 7
    assert _normalize_scalar("owner.pubkey.1", name="x") == "owner.pubkey.1"


def test_normalize_scalar_rejects_unsupported_type() -> None:
    with pytest.raises(TypeError, match="x must be a string, int, or bool"):
        _normalize_scalar({"bad": "value"}, name="x")


def test_normalize_string_tuple_deduplicates_strings_and_actions() -> None:
    normalized = _normalize_string_tuple(
        ["BTC", "BTC", StrategyAction.PLACE_SWAP_EXACT_IN, StrategyAction.PLACE_SWAP_EXACT_IN],
        name="items",
    )
    assert normalized == ("BTC", "place_swap_exact_in")


def test_normalize_string_tuple_rejects_invalid_inputs() -> None:
    with pytest.raises(ValueError, match="items must be non-empty"):
        _normalize_string_tuple([], name="items")
    with pytest.raises(ValueError, match="items\\[0\\] contains unsupported characters"):
        _normalize_string_tuple(["bad token"], name="items")


def test_strategy_ir_roundtrip_hash_is_stable() -> None:
    strategy = _make_strategy()
    roundtrip = strategy_ir_from_dict(strategy.to_dict())
    assert roundtrip.to_dict() == strategy.to_dict()
    assert roundtrip.strategy_hash_hex() == strategy.strategy_hash_hex()
    assert roundtrip.to_json_bytes() == json.dumps(
        strategy.to_dict(),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def test_strategy_budget_window_id_uses_static_strategy_buckets() -> None:
    whole_window = StrategyWindow(valid_from_epoch=1, valid_until_epoch=100)
    assert strategy_budget_window_duration_epochs(whole_window) == 100
    assert strategy_budget_window_id(whole_window, 5) == 1
    assert strategy_budget_window_id(whole_window, 99) == 1

    fixed_window = StrategyWindow(valid_from_epoch=1, valid_until_epoch=100, budget_window_epochs=4)
    assert strategy_budget_window_duration_epochs(fixed_window) == 4
    assert strategy_budget_window_id(fixed_window, 1) == 1
    assert strategy_budget_window_id(fixed_window, 4) == 1
    assert strategy_budget_window_id(fixed_window, 5) == 5
    assert strategy_budget_window_id(fixed_window, 9) == 9


def test_strategy_ir_tau_backend_requires_spec() -> None:
    with pytest.raises(ValueError, match="tau_policy_specs is required"):
        _make_strategy(backend=PolicyBackend.TAU)


def test_strategy_ir_tau_roundtrip_preserves_canonical_bundle() -> None:
    strategy = _make_strategy(
        backend=PolicyBackend.TAU,
        tau_policy_specs=AUTOTRADER_TAU_POLICY_SPECS,
    )
    assert strategy.to_dict()["tau_policy_specs"] == list(AUTOTRADER_TAU_POLICY_SPECS)
    assert strategy_ir_from_dict(strategy.to_dict()).tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS


def test_strategy_ir_legacy_tau_spec_expands_to_canonical_bundle() -> None:
    strategy = _make_strategy(
        backend=PolicyBackend.TAU,
        tau_policy_spec="autotrader_budget_guard_v1",
    )
    assert strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS
    assert strategy.tau_policy_spec is None
    roundtrip = strategy_ir_from_dict(
        {
            **strategy.to_dict(),
            "tau_policy_spec": "autotrader_budget_guard_v1",
        }
    )
    assert roundtrip.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS


def test_strategy_ir_legacy_tau_bundle_expands_to_canonical_bundle() -> None:
    strategy = _make_strategy(
        backend=PolicyBackend.TAU,
        tau_policy_specs=_LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V1,
    )
    assert strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS


def test_strategy_ir_previous_canonical_tau_bundle_expands_to_new_bundle() -> None:
    strategy = _make_strategy(
        backend=PolicyBackend.TAU,
        tau_policy_specs=_LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V2,
    )
    assert strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        ({"per_order_max": 200, "per_window_max": 100, "lifetime_max": 1_000}, "per_order_max must be <= per_window_max"),
        ({"per_order_max": 100, "per_window_max": 500, "lifetime_max": 400}, "per_window_max must be <= lifetime_max"),
        ({"per_order_max": True, "per_window_max": 500, "lifetime_max": 1_000}, "per_order_max must be an int"),
    ],
)
def test_notional_caps_reject_invalid_inputs(kwargs: dict[str, object], match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        NotionalCaps(**kwargs)


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        ({"max_slippage_bps": 10_001, "max_oracle_staleness_epochs": 3}, "max_slippage_bps must be <= 10000"),
        ({"max_slippage_bps": 100, "max_oracle_staleness_epochs": 0}, "max_oracle_staleness_epochs must be >= 1"),
        ({"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3, "require_quote_receipts": 1}, "require_quote_receipts must be a bool"),
    ],
)
def test_risk_limits_reject_invalid_inputs(kwargs: dict[str, object], match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        RiskLimits(**kwargs)


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        ({"valid_from_epoch": 10, "valid_until_epoch": 1}, "valid_from_epoch must be <= valid_until_epoch"),
        ({"valid_from_epoch": 1, "valid_until_epoch": 100, "min_order_spacing_epochs": True}, "min_order_spacing_epochs must be an int"),
        ({"valid_from_epoch": 1, "valid_until_epoch": 100, "budget_window_epochs": True}, "budget_window_epochs must be an int"),
    ],
)
def test_strategy_window_reject_invalid_inputs(kwargs: dict[str, object], match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        StrategyWindow(**kwargs)


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        ({"kill_switch_enabled": 1, "max_live_orders": 1}, "kill_switch_enabled must be a bool"),
        ({"kill_switch_enabled": True, "max_live_orders": 0}, "max_live_orders must be >= 1"),
        ({"kill_switch_enabled": True, "max_live_orders": 1, "max_intents_per_order": 0}, "max_intents_per_order must be >= 1"),
    ],
)
def test_strategy_controls_reject_invalid_inputs(kwargs: dict[str, object], match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        StrategyControls(**kwargs)


@pytest.mark.parametrize(
    ("overrides", "match"),
    [
        ({"asset_universe": ("BTC",)}, "asset_universe must contain at least two assets"),
        ({"policy_backend": "local"}, "policy_backend must be a PolicyBackend"),
        ({"template": "dca"}, "template must be a StrategyTemplate"),
        ({"notional_caps": object()}, "notional_caps must be a NotionalCaps"),
        ({"risk_limits": object()}, "risk_limits must be a RiskLimits"),
        ({"strategy_window": object()}, "strategy_window must be a StrategyWindow"),
        ({"controls": object()}, "controls must be a StrategyControls"),
        ({"allowed_actions": ()}, "allowed_actions must be non-empty"),
        ({"template_params": {"Bad-Key": 1}}, "invalid template_params key"),
        ({"template_params": {"fixed_order_size": object()}}, "template_params.fixed_order_size must be a string, int, or bool"),
        ({"tau_policy_spec": "bad spec"}, "tau_policy_spec contains unsupported characters"),
        (
            {
                "policy_backend": PolicyBackend.TAU,
                "tau_policy_spec": "other_spec",
            },
            "tau_policy_spec is unsupported; expected a canonical tau_policy_specs bundle",
        ),
        (
            {
                "policy_backend": PolicyBackend.TAU,
                "tau_policy_specs": ("autotrader_budget_guard_v1",),
            },
            "tau_policy_specs must equal the supported autotrader bundle",
        ),
        (
            {
                "policy_backend": PolicyBackend.LOCAL,
                "tau_policy_specs": AUTOTRADER_TAU_POLICY_SPECS,
            },
            "tau_policy_specs is only allowed when policy_backend=tau",
        ),
    ],
)
def test_strategy_ir_rejects_invalid_fields(overrides: dict[str, object], match: str) -> None:
    kwargs = {
        "strategy_id": "strat.alpha",
        "owner_pubkey": "owner.pubkey.1",
        "policy_backend": PolicyBackend.LOCAL,
        "template": StrategyTemplate.DCA,
        "asset_universe": ("BTC", "zUSD", "BTC"),
        "allowed_actions": (
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_SWAP_EXACT_IN,
        ),
        "notional_caps": NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        "risk_limits": RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        "strategy_window": StrategyWindow(valid_from_epoch=1, valid_until_epoch=100, min_order_spacing_epochs=1),
        "controls": StrategyControls(kill_switch_enabled=True, max_live_orders=2),
        "template_params": {
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
        "tau_policy_specs": (),
        "tau_policy_spec": None,
    }
    kwargs.update(overrides)
    with pytest.raises((TypeError, ValueError), match=match):
        StrategyIR(**kwargs)


def test_strategy_ir_normalizes_duplicates() -> None:
    strategy = StrategyIR(
        strategy_id="strat.alpha",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD", "BTC"),
        allowed_actions=(
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_ORDER_INTENT,
        ),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
    )
    assert strategy.asset_universe == ("BTC", "zUSD")
    assert [action.value for action in strategy.allowed_actions] == [
        "place_swap_exact_in",
        "place_order_intent",
    ]


@pytest.mark.parametrize(
    ("payload", "match"),
    [
        (["bad"], "strategy policy data must be a mapping"),
        ({"notional_caps": []}, "notional_caps must be an object"),
        ({"notional_caps": {}, "risk_limits": []}, "risk_limits must be an object"),
        ({"notional_caps": {}, "risk_limits": {}, "strategy_window": []}, "strategy_window must be an object"),
        ({"notional_caps": {}, "risk_limits": {}, "strategy_window": {}, "controls": []}, "controls must be an object"),
        ({"notional_caps": {}, "risk_limits": {}, "strategy_window": {}, "asset_universe": "BTC"}, "asset_universe must be a list"),
        ({"notional_caps": {}, "risk_limits": {}, "strategy_window": {}, "allowed_actions": "swap"}, "allowed_actions must be a list"),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": 1,
                "template": "dca",
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": ["place_swap_exact_in"],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "policy_backend must be a string",
        ),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": "bad",
                "template": "dca",
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": ["place_swap_exact_in"],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "policy_backend must be one of",
        ),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": "local",
                "template": 1,
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": ["place_swap_exact_in"],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "template must be a string",
        ),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": "local",
                "template": "bad",
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": ["place_swap_exact_in"],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "template must be one of",
        ),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": "local",
                "template": "dca",
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": [1],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "allowed_actions must be a string",
        ),
        (
            {
                "strategy_id": "strat.alpha",
                "owner_pubkey": "owner.pubkey.1",
                "policy_backend": "local",
                "template": "dca",
                "asset_universe": ["BTC", "zUSD"],
                "allowed_actions": ["bad"],
                "notional_caps": {"per_order_max": 100, "per_window_max": 500, "lifetime_max": 1_000},
                "risk_limits": {"max_slippage_bps": 100, "max_oracle_staleness_epochs": 3},
                "strategy_window": {"valid_from_epoch": 1, "valid_until_epoch": 100},
            },
            "allowed_actions must be one of",
        ),
    ],
)
def test_strategy_ir_from_dict_rejects_invalid_shapes(payload: object, match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        strategy_ir_from_dict(payload)
