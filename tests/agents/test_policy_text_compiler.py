from __future__ import annotations

import pytest

from src.agents.policy_text_compiler import compile_policy_text
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS


def test_compile_policy_text_dca_sentence() -> None:
    result = compile_policy_text(
        "dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps "
        "per window max 300 lifetime max 900 backend tau max live orders 2",
        owner_pubkey="owner.pubkey.1",
    )
    assert result.source_form == "sentence"
    assert result.compiled.strategy.template.value == "dca"
    assert result.compiled.strategy.policy_backend.value == "tau"
    assert result.compiled.strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS
    assert result.compiled.strategy.notional_caps.per_order_max == 100
    assert result.compiled.strategy.notional_caps.per_window_max == 300
    assert result.compiled.strategy.notional_caps.lifetime_max == 900
    assert result.compiled.strategy.controls.max_live_orders == 2
    assert result.compiled.strategy.risk_limits.max_slippage_bps == 25
    assert result.compiled.strategy.strategy_window.valid_until_epoch == 20


def test_compile_policy_text_kv_mode() -> None:
    text = """
template: dca
strategy_id: dca.kv.1
owner_pubkey: owner.pubkey.1
backend: local
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
max_slippage_bps: 50
max_oracle_staleness_epochs: 3
valid_from_epoch: 1
valid_until_epoch: 100
min_order_spacing_epochs: 2
kill_switch_enabled: true
max_live_orders: 1
""".strip()
    result = compile_policy_text(text)
    assert result.source_form == "kv"
    assert result.compiled.strategy.strategy_id == "dca.kv.1"
    assert result.compiled.strategy.policy_backend.value == "local"
    assert result.compiled.strategy.template_params["asset_in"] == "zUSD"
    assert result.compiled.strategy.strategy_window.min_order_spacing_epochs == 2


def test_compile_policy_text_kv_mode_tau_asset_universe_and_actions() -> None:
    text = """
# controlled policy
template: dca
backend: tau
asset_universe: zUSD,BTC
allowed_actions: order_intent, swap exact in
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
label: slow-and-steady
""".strip()
    result = compile_policy_text(text, owner_pubkey="owner.pubkey.1")
    assert result.source_form == "kv"
    assert result.compiled.strategy.policy_backend.value == "tau"
    assert result.compiled.strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS
    assert result.compiled.strategy.asset_universe == ("zUSD", "BTC")
    assert [action.value for action in result.compiled.strategy.allowed_actions] == [
        "place_order_intent",
        "place_swap_exact_in",
    ]
    assert result.compiled.strategy.template_params["label"] == "slow-and-steady"


def test_compile_policy_text_kv_mode_accepts_false_booleans() -> None:
    text = """
template: dca
owner_pubkey: owner.pubkey.1
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
require_quote_receipts: off
kill_switch_enabled: no
""".strip()
    result = compile_policy_text(text)
    assert result.compiled.strategy.risk_limits.require_quote_receipts is False
    assert result.compiled.strategy.controls.kill_switch_enabled is False


def test_compile_policy_text_kv_mode_respects_explicit_tau_policy_specs() -> None:
    tau_specs = ", ".join(AUTOTRADER_TAU_POLICY_SPECS)
    text = """
template: dca
owner_pubkey: owner.pubkey.1
backend: tau
tau_policy_specs: __TAU_SPECS__
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
""".replace("__TAU_SPECS__", tau_specs).strip()
    result = compile_policy_text(text)
    assert result.compiled.strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS


def test_compile_policy_text_sentence_window_and_optional_flags() -> None:
    result = compile_policy_text(
        "dca 100 zUSD into BTC every 4 epochs window 5 to 20 "
        "max oracle staleness 9 epochs quote receipts disabled "
        "kill switch disabled min order spacing 2 epochs",
        owner_pubkey="owner.pubkey.1",
    )
    assert result.source_form == "sentence"
    assert result.compiled.strategy.strategy_window.valid_from_epoch == 5
    assert result.compiled.strategy.strategy_window.valid_until_epoch == 20
    assert result.compiled.strategy.strategy_window.min_order_spacing_epochs == 2
    assert result.compiled.strategy.risk_limits.max_oracle_staleness_epochs == 9
    assert result.compiled.strategy.risk_limits.require_quote_receipts is False
    assert result.compiled.strategy.controls.kill_switch_enabled is False


def test_compile_policy_text_rejects_unsupported_text() -> None:
    with pytest.raises(ValueError, match="unsupported policy text"):
        compile_policy_text("ape into BTC whenever vibes look strong", owner_pubkey="owner.pubkey.1")


def test_compile_policy_text_rejects_missing_owner() -> None:
    with pytest.raises(ValueError):
        compile_policy_text("dca 100 zUSD into BTC every 4 epochs")


def test_compile_policy_text_rejects_bad_kv_line() -> None:
    bad = """
template: dca
owner_pubkey: owner.pubkey.1
this line is malformed
    """.strip()
    with pytest.raises(ValueError, match="unsupported policy text"):
        compile_policy_text(bad)


@pytest.mark.parametrize(
    ("text", "match"),
    [
        ("dca 100 BTC into BTC every 4 epochs", "asset_in and asset_out must differ"),
        ("template: dca\nowner_pubkey: owner.pubkey.1", "key-value policy text must define asset_universe"),
        ("owner_pubkey: owner.pubkey.1\nasset_in: zUSD\nasset_out: BTC", "key-value policy text must define template"),
        ("template: dca\nowner_pubkey: owner.pubkey.1\nper_order_max: nope", "per_order_max must be a non-negative integer"),
        ("template: dca\nowner_pubkey: owner.pubkey.1\nmax_slippage_bps: 10001", "max_slippage_bps out of range"),
        ("template: dca\nowner_pubkey: owner.pubkey.1\nrequire_quote_receipts: maybe", "require_quote_receipts must be a boolean-like value"),
        ("# comment only", "unsupported policy text"),
    ],
)
def test_compile_policy_text_rejects_invalid_inputs(text: str, match: str) -> None:
    with pytest.raises((TypeError, ValueError), match=match):
        compile_policy_text(text, owner_pubkey="owner.pubkey.1")


def test_compile_policy_text_rejects_non_string_and_empty() -> None:
    with pytest.raises(TypeError, match="text must be a string"):
        compile_policy_text(123, owner_pubkey="owner.pubkey.1")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="policy text must be non-empty"):
        compile_policy_text("   ", owner_pubkey="owner.pubkey.1")
