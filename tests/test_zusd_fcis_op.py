from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.core.zusd import ZUSD_STATE_FIELD_ORDER, init_state

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "runtime" / "zusd_fcis_op.py"


def request(kind: str, **args: object) -> bytes:
    state = init_state()
    state_doc = {
        name: getattr(state, name)
        for name in ZUSD_STATE_FIELD_ORDER
    }
    value = {
        "version": 1,
        "state": state_doc,
        "tx": {"kind": kind, **args},
        "require_oracle_authorization": False,
    }
    return json.dumps(value, separators=(",", ":")).encode("ascii") + b"\n"


def invoke(raw: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=ROOT,
        input=raw,
        capture_output=True,
        check=False,
        timeout=5,
    )


def test_python_mount_emits_canonical_complete_accept() -> None:
    result = invoke(request("deposit_collateral", amount_e8=100_000_000))
    assert result.returncode == 0, result.stderr.decode()
    assert result.stdout.endswith(b"\n") and b"\n" not in result.stdout[:-1]
    doc = json.loads(result.stdout)
    assert tuple(doc) == (
        "version", "kernel", "accept", "reject_reason", "receipt_hash",
        "receipt", "pre_state_root", "post_state_root", "post_state",
    )
    assert doc["accept"] is True
    assert doc["receipt"] == {"tag": "deposit_collateral"}
    assert doc["pre_state_root"] != doc["post_state_root"]


def test_python_mount_emits_unchanged_reject() -> None:
    result = invoke(request("mint_zusd", amount_e8=1))
    assert result.returncode == 0, result.stderr.decode()
    doc = json.loads(result.stdout)
    assert doc["accept"] is False
    assert doc["reject_reason"] == "mint_blocked_oracle"
    assert doc["pre_state_root"] == doc["post_state_root"]
    assert doc["receipt"] is None and doc["receipt_hash"] is None


def test_python_mount_rejects_noncanonical_or_duplicate_input() -> None:
    result = invoke(b'{"version":1,"version":1}\n')
    assert result.returncode == 2
    assert result.stdout == b""
