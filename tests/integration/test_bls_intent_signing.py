from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from src.core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from src.integration import bls_intent_signing

REPO_ROOT = Path(__file__).resolve().parents[2]
FIXED_PUBKEY_25 = (
    "acb58c81ae0cae2e9d4d446b730922239923c345744eee58efaadb36e9a09255"
    "45b18a987acf0bad469035b291e37269"
)
FIXED_DEX_SIGNATURE_25 = (
    "0x8037e209f122cd8bd3fbaa2440ce2ba7f318843ca39b9cbf7ee53da38d3d8053"
    "5870ab0e14c8a8a7b5195d8da1e39d06056ed788fd977c6e2f19795d5bf2417f"
    "958e31cfe653f7d105c8767e0dc9d62a2819ab7ba2bb316d094e6a647fa13654"
)


def _fixed_intent() -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "11" * 32,
        "sender_pubkey": "0x" + "22" * 48,
        "deadline": 100,
        "nonce": 1,
        "pool_id": "0x" + "33" * 32,
        "asset_in": "0x" + "44" * 32,
        "asset_out": "0x" + "55" * 32,
        "amount_in": 10,
        "min_amount_out": 9,
        "recipient": "0x" + "22" * 48,
    }


@pytest.mark.skipif(not bls_intent_signing.BLS_AVAILABLE, reason="py_ecc unavailable")
def test_pure_signing_matches_fixed_vector_and_independent_bls_call() -> None:
    from py_ecc.bls import G2Basic

    intent = _fixed_intent()
    message_hash = hash_dex_intent_auth_message_v1(intent, chain_id="parity-chain")

    assert bls_intent_signing.bls_pubkey_hex_from_privkey(25) == FIXED_PUBKEY_25
    assert (
        bls_intent_signing.sign_dex_intent_for_engine(
            intent,
            privkey=25,
            chain_id="parity-chain",
        )
        == FIXED_DEX_SIGNATURE_25
    )
    assert FIXED_DEX_SIGNATURE_25 == "0x" + G2Basic.Sign(25, message_hash).hex()


def test_pure_privkey_parser_covers_scalar_and_byte_boundaries() -> None:
    order = bls_intent_signing.BLS12_381_CURVE_ORDER
    assert order is not None
    assert bls_intent_signing.parse_privkey_to_int(order - 1) == order - 1
    assert bls_intent_signing.parse_privkey_to_int(b"\x00" * 31 + b"\x01") == 1
    assert bls_intent_signing.parse_privkey_to_int(" 7 ") == 7

    for invalid in (False, True, 0, order):
        with pytest.raises((TypeError, ValueError)):
            bls_intent_signing.parse_privkey_to_int(invalid)
    for invalid_bytes in (b"\x01" * 31, b"\x01" * 33):
        with pytest.raises(ValueError, match="privkey bytes must be length 32"):
            bls_intent_signing.parse_privkey_to_int(invalid_bytes)


@pytest.mark.skipif(not bls_intent_signing.BLS_AVAILABLE, reason="py_ecc unavailable")
def test_pure_signing_matches_retired_tau_client_compatibility_exports() -> None:
    from src.integration import tau_net_client

    intent = _fixed_intent()
    pure_signature = bls_intent_signing.sign_dex_intent_for_engine(
        intent,
        privkey=25,
        chain_id="parity-chain",
    )

    assert bls_intent_signing.bls_pubkey_hex_from_privkey(25) == (
        tau_net_client.bls_pubkey_hex_from_privkey(25)
    )
    assert pure_signature == tau_net_client.sign_dex_intent_for_engine(
        intent,
        privkey=25,
        chain_id="parity-chain",
    )


@pytest.mark.parametrize(
    "module_name",
    (
        "src.agents",
        "tools.zeno_ledger_multidocker_scenario",
        "tools.zeno_ledger_make_public_testnet_bundle",
        "tools.zenoctl_testnet_local.fixtures",
        "tools.zenoctl_testnet_local.cli",
    ),
)
def test_current_operator_import_roots_do_not_load_retired_tau_bridge_modules(
    module_name: str,
) -> None:
    script = f"""\nimport importlib\nimport sys\nimportlib.import_module({module_name!r})\nfor forbidden in (\n    "src.integration.tau_net_client",\n    "src.integration.tau_testnet_dex_plugin",\n    "src.integration.perps_wallet_api",\n    "src.integration.zusd_tau_wallet_api",\n    "src.integration.zusd_monetary_wallet_api",\n):\n    if forbidden in sys.modules:\n        raise SystemExit(forbidden)\n"""

    result = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 0, result.stderr or result.stdout


@pytest.mark.parametrize(
    "broken_module",
    ("py_ecc.bls", "py_ecc.optimized_bls12_381"),
)
def test_bls_backend_initialization_fault_is_not_misclassified_as_optional_absence(
    broken_module: str,
) -> None:
    script = f"""
import builtins
import importlib
import types

real_import = builtins.__import__

def import_with_broken_bls(name, globals=None, locals=None, fromlist=(), level=0):
    if name == {broken_module!r}:
        raise RuntimeError("broken BLS backend")
    if name == "py_ecc.bls":
        return types.SimpleNamespace(G2Basic=object())
    return real_import(name, globals, locals, fromlist, level)

builtins.__import__ = import_with_broken_bls
try:
    importlib.import_module("src.integration.bls_intent_signing")
except RuntimeError as exc:
    if str(exc) != "broken BLS backend":
        raise
else:
    raise SystemExit("BLS backend fault was treated as an absent optional dependency")
"""

    result = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 0, result.stderr or result.stdout
