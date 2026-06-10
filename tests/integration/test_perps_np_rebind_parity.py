"""Parity + domain teeth for the production perps-NP deposit RebindFn.

The rebind is the client's gate-8/9 trust source; if it drifts from the guest's
canonical encoders the client rejects every honest proof. Two layers here:

1. GOLDEN parity vectors: hashes recorded from the REAL guest CLI execute path
   (`tau_state_transition_execute`, journal meta) at authoring time, asserted
   byte-for-byte. Provenance of every vector is in the comment above it.
2. LIVE parity (skipped when the CLI binary is not built): re-runs the guest
   execute for the same cases and asserts the mirror matches the guest TODAY,
   so encoder drift on either side fails loudly.

Plus the fail-closed domain teeth: anything outside the encoder domain returns
{} (which decide_admission turns into REFUSE_OPERATION_MISMATCH), never raises.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Mapping

import pytest

from src.integration.client_admission_decision import RequestedOperation
from src.integration.perps_np_rebind import perps_np_deposit_rebind

REPO = Path(__file__).resolve().parents[2]
CLI_BIN = REPO / "zk" / "state_proof_risc0" / "target" / "release" / "tau-state-proof-risc0-cli"

ZUSD_PT = "risc0.zenodex_zusd_transition.v1"


def _binding(seed: str = "11") -> dict[str, str]:
    return {
        "source_proof_type": ZUSD_PT,
        "source_state_hash": seed * 32,
        "balance_root_hash": "22" * 32,
        "balance_delta_hash": "33" * 32,
    }


def _fields(**overrides: Any) -> dict[str, Any]:
    base: dict[str, Any] = {
        "pubkey": "wallet-aa",
        "asset": "zUSD",
        "amount_e8": 500_000_000,
        "nonce": 1,
        "collateral_binding": _binding(),
    }
    base.update(overrides)
    return base


def _op(fields: Mapping[str, Any]) -> RequestedOperation:
    return RequestedOperation(surface="perps_np", operation="deposit_collateral", fields=fields)


# Golden vectors: recorded 2026-06-10 from the guest CLI execute path
# (four_wallet pre-state, deposit wallet-aa zUSD 5e8 nonce 1, binding 11/22/33).
GOLDEN_ZUSD_DEPOSIT = {
    "operation_hash": "13d147ac22a85397552f43093ce3786023113cca2256eeb4da77ed2abee2ebe5",
    "collateral_binding_hash": "1b1703c270bc172437862d1c34e39444d9d66bd07a7a333170b9050113f6624b",
    "oracle_binding_hash": "7f4e3be2e7dc9d39f6d83b2910b8afcd80f25af244a14c21627f2925ff185b53",
}


def test_golden_parity_zusd_deposit() -> None:
    result = perps_np_deposit_rebind(_op(_fields()))
    assert set(result.keys()) == set(GOLDEN_ZUSD_DEPOSIT.keys())
    for key, want in GOLDEN_ZUSD_DEPOSIT.items():
        assert result[key].hex() == want, f"{key} drifted from the guest encoder"


def test_rebind_is_deterministic_and_input_sensitive() -> None:
    base = perps_np_deposit_rebind(_op(_fields()))
    again = perps_np_deposit_rebind(_op(_fields()))
    assert base == again
    bumped = perps_np_deposit_rebind(_op(_fields(amount_e8=500_000_001)))
    assert bumped["operation_hash"] != base["operation_hash"]
    assert bumped["collateral_binding_hash"] != base["collateral_binding_hash"]
    # oracle bindings hash is action-independent for deposit-only lists
    assert bumped["oracle_binding_hash"] == base["oracle_binding_hash"]


@pytest.mark.parametrize(
    "fields",
    [
        _fields(amount_e8=True),  # bool is not an i128
        _fields(amount_e8="500000000"),
        _fields(amount_e8=1 << 127),  # above i128 max
        _fields(nonce=-1),
        _fields(nonce=1 << 64),
        _fields(nonce=True),
        _fields(pubkey=""),
        _fields(pubkey=b"wallet-aa"),
        _fields(asset=""),
        _fields(asset="zUSD", collateral_binding=None),  # zUSD REQUIRES a binding
        _fields(collateral_binding={**_binding(), "extra": "x"}),
        _fields(collateral_binding={**_binding(), "source_proof_type": "wrong.pt"}),
        _fields(collateral_binding={**_binding(), "source_state_hash": "zz" * 32}),
        _fields(collateral_binding={**_binding(), "balance_root_hash": "11" * 31}),
        _fields(extra_field=1),
        {k: v for k, v in _fields().items() if k != "nonce"},  # missing required
    ],
)
def test_rebind_fails_closed_outside_encoder_domain(fields: dict[str, Any]) -> None:
    assert perps_np_deposit_rebind(_op(fields)) == {}


def test_rebind_refuses_wrong_surface_or_operation() -> None:
    assert (
        perps_np_deposit_rebind(
            RequestedOperation(surface="zusd", operation="deposit_collateral", fields=_fields())
        )
        == {}
    )
    assert (
        perps_np_deposit_rebind(
            RequestedOperation(surface="perps_np", operation="withdraw_collateral", fields=_fields())
        )
        == {}
    )


def test_non_zusd_asset_without_binding_allowed_and_distinct() -> None:
    # Encoder-domain only: the guest additionally requires asset == the market
    # collateral asset, so this input can never carry a proof — but the encoder
    # is total over it and must stay deterministic + input-sensitive.
    fields = _fields(asset="wTAU", collateral_binding=None)
    result = perps_np_deposit_rebind(_op(fields))
    assert set(result.keys()) == set(GOLDEN_ZUSD_DEPOSIT.keys())
    assert result["operation_hash"].hex() != GOLDEN_ZUSD_DEPOSIT["operation_hash"]


# --------------------------------------------------------------------------- #
# Live parity vs the guest CLI (skips when the binary is not built)
# --------------------------------------------------------------------------- #
def _guest_execute_meta(fields: Mapping[str, Any]) -> Mapping[str, str]:
    if not CLI_BIN.is_file():
        pytest.skip(f"RISC0 CLI not built: {CLI_BIN}")
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "perps_np_smoke", REPO / "tools" / "zeno_ledger_perp_np_risc0_real_proof_smoke.py"
    )
    assert spec is not None and spec.loader is not None
    smoke = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(smoke)
    case_input = smoke._cases()["four_wallet"]["input"]
    pre_state = smoke._current_pre_state_from_input(case_input)
    pre_hash = smoke._current_snapshot_hash(pre_state)
    action = {"kind": "deposit_collateral", **{k: v for k, v in fields.items()}}
    request = {
        "schema": "tau_state_transition_execute",
        "schema_version": 1,
        "proof_type": "risc0.zenodex_perps_np_transition.v1",
        "state_hash": "ab" * 32,
        "chain_id": str(case_input["chain_id"]),
        "context": {
            "chain_id": str(case_input["chain_id"]),
            "app_hash_pre": pre_hash,
            "perps_state_pre": pre_state,
        },
        "pre_state": pre_state,
        "actions": [action],
    }
    proc = subprocess.run(
        [str(CLI_BIN)],
        input=json.dumps(request, separators=(",", ":")),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr[-300:]
    out = json.loads(proc.stdout)
    assert out.get("accepted") is True, out
    return out["meta"]


# The guest only accepts deposits in the market collateral asset (zUSD here)
# with a POSITIVE amount ("deposit collateral asset mismatch" / "deposit must be
# positive"), so live parity runs over guest-acceptable cases only. The encoder
# itself is total; rejected-by-guest inputs simply never have a journal to match.
@pytest.mark.parametrize(
    "fields",
    [
        _fields(),
        _fields(amount_e8=1, nonce=1),
        _fields(pubkey="wallet-cc", amount_e8=123_456_789, nonce=1),
        _fields(pubkey="wallet-zz", amount_e8=42, nonce=1),  # new-account join
        _fields(amount_e8=(1 << 100), nonce=1),  # huge but in-domain amount
    ],
)
def test_live_parity_against_guest_execute(fields: dict[str, Any]) -> None:
    meta = _guest_execute_meta(fields)
    result = perps_np_deposit_rebind(_op(fields))
    assert result, "rebind refused a guest-accepted deposit"
    assert result["operation_hash"].hex() == meta["operation_hash"]
    assert result["collateral_binding_hash"].hex() == meta["collateral_binding_hash"]
    assert result["oracle_binding_hash"].hex() == meta["oracle_binding_hash"]
