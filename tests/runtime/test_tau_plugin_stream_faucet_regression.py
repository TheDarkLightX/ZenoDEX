"""
S1 hardening regressions for the tau_testnet_dex_plugin multiplexer.

Locks two invariants that the audit verified hold but that lacked a dedicated
plugin-level test:

  D-STREAM-001  stream "5" overload (upstream DEX intents vs legacy perp ops) must
                never apply the same payload to BOTH the DEX and perp engines.
                The selectors are complementary on `dex_like`: DEX selects "5"
                iff dex_like; perp-legacy selects "5" iff (not dex_like and
                perp_like). An ambiguous payload (looks like both) must route to
                exactly ONE engine (DEX wins) — never both.

  D-FAUCET-001  the test-only faucet must be rejected unless TAU_DEX_FAUCET=1 and
                must never mint the native asset (no protocol-balance leakage via
                a fixture path outside explicit local-test mode).
"""
from __future__ import annotations

from src.core.dex import DexState
from src.core.managed_asset_policy import build_zusd_managed_asset_policy
from src.integration.tau_testnet_dex_plugin import (
    _DEX_INTENTS_KEY,
    _LEGACY_DEX_INTENTS_KEY,
    _LEGACY_PERP_OPS_KEY,
    _PERP_OPS_KEY,
    _apply_faucet,
    _looks_like_dex_intents,
    _looks_like_perp_ops,
    _select_dex_ops,
    _select_perp_ops,
)
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable

_PK = "0x" + "11" * 48
_TOKEN = "0x" + "0a" * 32
_MANAGED_TOKEN = "0x" + "0b" * 32


def _state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable(), nonces=NonceTable())


def _managed_asset_policy():
    return build_zusd_managed_asset_policy(_MANAGED_TOKEN)


# --- D-STREAM-001: stream "5" never double-applies -----------------------------
def test_ambiguous_stream5_routes_to_dex_only_no_double_apply():
    # A payload whose first op carries BOTH a DEX "kind" and a perp "action".
    ambiguous = [{"kind": "SWAP_EXACT_IN", "action": "set_position"}]
    assert _looks_like_dex_intents(ambiguous) is True
    assert _looks_like_perp_ops(ambiguous) is True
    ops = {_DEX_INTENTS_KEY: ambiguous}  # stream "5"
    dex_sel = _select_dex_ops(ops)
    perp_sel = _select_perp_ops(ops)
    # DEX claims it (remapped to the legacy intents key); perp must NOT also claim it.
    assert dex_sel.get(_LEGACY_DEX_INTENTS_KEY) == ambiguous
    assert perp_sel == {}, "ambiguous stream-5 payload was selected by BOTH engines (double-apply)"


def test_pure_perp_like_stream5_routes_to_perp_only():
    perp_payload = [{"module": "TauPerp", "action": "set_position"}]
    ops = {_DEX_INTENTS_KEY: perp_payload}  # stream "5" == legacy perp key
    assert _select_dex_ops(ops) == {}  # not dex_like -> DEX ignores it
    assert _select_perp_ops(ops).get(_LEGACY_PERP_OPS_KEY) == perp_payload


def test_stream5_with_legacy_dex_2_present_is_not_double_counted():
    # "2" (legacy dex intents) present alongside "5": DEX uses "2", and "5" must
    # not be selected by perp (legacy-dex-conflict) -> no double application.
    legacy = [{"module": "TauSwap", "kind": "SWAP_EXACT_IN"}]
    five = [{"module": "TauPerp", "action": "set_position"}]
    ops = {_LEGACY_DEX_INTENTS_KEY: legacy, _DEX_INTENTS_KEY: five}
    dex_sel = _select_dex_ops(ops)
    perp_sel = _select_perp_ops(ops)
    assert dex_sel.get(_LEGACY_DEX_INTENTS_KEY) == legacy  # DEX takes "2"
    assert perp_sel == {}  # perp refuses "5" while a legacy dex stream is present


def test_upstream_perp_stream8_and_dex_stream5_are_independent():
    dex5 = [{"module": "TauSwap", "kind": "SWAP_EXACT_IN"}]
    perp8 = [{"module": "TauPerp", "action": "set_position"}]
    ops = {_DEX_INTENTS_KEY: dex5, _PERP_OPS_KEY: perp8}
    assert _select_dex_ops(ops).get(_LEGACY_DEX_INTENTS_KEY) == dex5
    assert _select_perp_ops(ops).get(_LEGACY_PERP_OPS_KEY) == perp8


# --- D-FAUCET-001: faucet gated + native-safe ----------------------------------
def test_faucet_none_is_noop():
    ok, _state_out, err = _apply_faucet(
        _state(), None, allow=False, managed_asset_policy=_managed_asset_policy()
    )
    assert ok is True and err is None


def test_faucet_rejected_when_disabled():
    ok, _state_out, err = _apply_faucet(
        _state(), {"mint": []}, allow=False, managed_asset_policy=_managed_asset_policy()
    )
    assert ok is False and "faucet disabled" in (err or "")


def test_faucet_cannot_mint_native_even_when_enabled():
    ok, _state_out, err = _apply_faucet(
        _state(),
        {"mint": [[_PK, NATIVE_ASSET, 5]]},
        allow=True,
        managed_asset_policy=_managed_asset_policy(),
    )
    assert ok is False and "native" in (err or "")


def test_faucet_mints_non_native_when_enabled():
    ok, state_out, err = _apply_faucet(
        _state(),
        {"mint": [[_PK, _TOKEN, 100]]},
        allow=True,
        managed_asset_policy=_managed_asset_policy(),
    )
    assert ok is True and err is None
    assert state_out.balances.get(_PK, _TOKEN) == 100
    # native untouched
    assert state_out.balances.get(_PK, NATIVE_ASSET) == 0
