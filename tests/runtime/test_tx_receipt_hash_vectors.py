"""Cross-language vectors for the tx-envelope / receipt hashes (Phase F).

Proves the Rust `domain_json_hash` op reproduces the authoritative DEX intent
auth message hash (`src/core/dex_intent_auth_message.py`) and burn-receipt body
hash (`src/core/burn_receipts.py`), plus semantic sensitivity properties
(field/chain-id binding) of the authority itself.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.burn_receipts import burn_receipt_hash
from src.core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from tools.runtime import tx_receipt_hash_lib as lib


# --- Python authority: semantic sensitivity (no Rust) -------------------------


def test_chain_id_changes_intent_hash():
    intent = lib._intent()
    h1 = hash_dex_intent_auth_message_v1(intent, chain_id="zeno-testnet-1")
    h2 = hash_dex_intent_auth_message_v1(intent, chain_id="zeno-mainnet")
    assert h1 != h2  # chain_id binds via the domain-sep label


def test_field_change_changes_intent_hash():
    h1 = hash_dex_intent_auth_message_v1(lib._intent(), chain_id="c")
    h2 = hash_dex_intent_auth_message_v1(
        lib._intent(fields={"asset_in": "zUSD", "asset_out": "zDEX", "amount_in": 1001, "min_out": 5}),
        chain_id="c",
    )
    assert h1 != h2


def test_burn_body_tamper_changes_hash():
    h1 = burn_receipt_hash({"schema": "zenodex/burn_receipt/v1", "amount": 100})
    h2 = burn_receipt_hash({"schema": "zenodex/burn_receipt/v1", "amount": 101})
    assert h1 != h2


# --- Rust/Python differential -------------------------------------------------


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.TxHashShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    rust_results = lib.run_rust(rust_bin, [c["rust"] for c in cases])
    problems = lib.diff_cases(cases, rust_results)
    assert not problems, "Python/Rust tx/receipt hash mismatch:\n" + "\n".join(problems[:20])


def test_rust_matches_python_static(rust_bin):
    _assert_agrees(lib.static_cases(), rust_bin)


@pytest.mark.parametrize("seed", [1, 13, 20260529])
def test_rust_matches_python_randomized(rust_bin, seed):
    _assert_agrees(lib.random_cases(seed=seed, n=300), rust_bin)


def test_float_value_rejected_on_both(rust_bin):
    # A float in the hashed dict is rejected by canonical_json_bytes on both sides.
    bad = {"op": "domain_json_hash", "label": lib.BURN_LABEL, "version": 1,
           "value": {"schema": "zenodex/burn_receipt/v1", "amount": 1.5}}
    rs = lib.run_rust(rust_bin, [bad])
    assert not rs[0]["ok"] and rs[0]["code"] == "float_not_allowed"
    with pytest.raises((TypeError, ValueError)):
        burn_receipt_hash({"schema": "zenodex/burn_receipt/v1", "amount": 1.5})


def test_bad_domain_label_rejected(rust_bin):
    bad = {"op": "domain_json_hash", "label": "", "version": 1, "value": {"a": 1}}
    rs = lib.run_rust(rust_bin, [bad])
    assert not rs[0]["ok"] and rs[0]["code"] == "bad_domain_label"
