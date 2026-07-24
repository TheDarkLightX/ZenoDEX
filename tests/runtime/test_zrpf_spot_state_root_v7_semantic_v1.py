"""Independent fixed-width parity for the proof-neutral Spot V7 ABI."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

_ROOT = Path(__file__).resolve().parents[2]
_V5_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"
_V7_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v7_semantic_v1.json"


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _raw(value: str) -> bytes:
    assert value.startswith("0x")
    return bytes.fromhex(value[2:])


def _uint(value: int, width: int) -> bytes:
    return value.to_bytes(width, "big")


def _host_input_bytes(v5: Mapping[str, Any]) -> bytes:
    state = v5["post_state"]
    expected = v5["expected"]
    output = bytearray(_uint(1, 2))

    balances = sorted(
        state["balances"], key=lambda row: (_raw(row["pubkey"]), _raw(row["asset"]))
    )
    output += _uint(len(balances), 4)
    for row in balances:
        output += _raw(row["pubkey"])
        output += _raw(row["asset"])
        output += _uint(row["amount"], 16)

    pools = sorted(state["pools"], key=lambda row: _raw(row["pool_id"]))
    output += _uint(len(pools), 4)
    for row in pools:
        output += _raw(row["pool_id"])
        output += _raw(row["asset0"])
        output += _raw(row["asset1"])
        output += _uint(row["reserve0"], 16)
        output += _uint(row["reserve1"], 16)
        output += _uint(row["fee_bps"], 4)
        output += _uint(row["lp_supply"], 16)
        output += _uint(row["created_at"], 8)

    lp_balances = sorted(
        state["lp_balances"],
        key=lambda row: (_raw(row["pubkey"]), _raw(row["pool_id"])),
    )
    output += _uint(len(lp_balances), 4)
    for row in lp_balances:
        output += _raw(row["pubkey"])
        output += _raw(row["pool_id"])
        output += _uint(row["amount"], 16)

    output += _uint(state["fee_accumulator"]["dust"], 16)
    output += _raw(expected["pre_state_root_v5"])
    output += _raw(expected["post_state_root_v5"])
    return bytes(output)


def _journal_bytes(v5: Mapping[str, Any]) -> bytes:
    expected = v5["expected"]
    output = bytearray(_uint(1, 2))
    for field in (
        "compatibility_profile_id",
        "state_root_scheme_id",
        "source_pre_app_hash",
        "source_post_app_hash",
        "source_pre_nonce_root",
        "source_post_nonce_root",
        "pre_state_root_v5",
        "post_state_root_v5",
    ):
        output += _raw(expected[field])
    output += _raw(v5["sender_pubkey"])
    output += _uint(v5["ingress_nonce"], 4)
    return bytes(output)


def test_independent_python_host_abi_matches_fixed_rust_vector() -> None:
    v5 = _load(_V5_FIXTURE)
    v7 = _load(_V7_FIXTURE)
    encoded = _host_input_bytes(v5)
    assert len(encoded) == v7["host_input_bytes"]
    assert "0x" + encoded.hex() == v7["host_input_hex"]
    assert "0x" + hashlib.sha256(encoded).hexdigest() == v7["host_input_sha256"]
    assert v7["maximum_host_input_bytes"] == 5_701_726


def test_independent_python_journal_matches_exact_six_commitment_surface() -> None:
    v5 = _load(_V5_FIXTURE)
    v7 = _load(_V7_FIXTURE)
    encoded = _journal_bytes(v5)
    assert len(encoded) == v7["journal_bytes"] == 310
    assert "0x" + encoded.hex() == v7["journal_hex"]
    assert "0x" + hashlib.sha256(encoded).hexdigest() == v7["journal_sha256"]


def test_v7_vector_preserves_all_authority_nonclaims() -> None:
    boundary = _load(_V7_FIXTURE)["claim_boundary"]
    assert boundary == {
        "source_authentication_verified": False,
        "receipt_authority": False,
        "settlement_authority": False,
    }
