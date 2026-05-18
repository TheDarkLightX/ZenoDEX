from __future__ import annotations

import base64
import json
import subprocess
import sys
from pathlib import Path

import pytest


def _run_verifier(script_name: str, payload: dict) -> dict:
    repo_root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [sys.executable, str(repo_root / "tools" / "proof_verifiers" / script_name)],
        input=json.dumps(payload, sort_keys=True).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    assert proc.stderr == b""
    return json.loads(proc.stdout.decode("utf-8"))


@pytest.mark.parametrize(
    ("script_name", "scheme"),
    [
        ("recompute_batch_v1.py", "recompute_batch_v1"),
        ("recompute_batch_v2.py", "recompute_batch_v2"),
        ("recompute_batch_v3.py", "recompute_batch_v3"),
        ("recompute_batch_v4.py", "recompute_batch_v4"),
    ],
)
def test_recompute_verifiers_return_structured_error_for_non_object_proof(script_name: str, scheme: str) -> None:
    result = _run_verifier(
        script_name,
        {
            "schema": "zenodex_proof",
            "schema_version": 1,
            "proof": "not-object",
            "pre_state_commitment": "0x" + "00" * 32,
            "batch_commitment": "0x" + "11" * 32,
        },
    )

    assert result["ok"] is False
    assert "proof must be an object" in result["error"]


@pytest.mark.parametrize(
    ("script_name", "scheme"),
    [
        ("recompute_batch_v2.py", "recompute_batch_v2"),
        ("recompute_batch_v3.py", "recompute_batch_v3"),
        ("recompute_batch_v4.py", "recompute_batch_v4"),
    ],
)
def test_recompute_verifiers_return_structured_error_for_bad_zlib(script_name: str, scheme: str) -> None:
    result = _run_verifier(
        script_name,
        {
            "schema": "zenodex_proof",
            "schema_version": 1,
            "pre_state_commitment": "0x" + "00" * 32,
            "batch_commitment": "0x" + "11" * 32,
            "proof": {
                "scheme": scheme,
                "pre_state_commitment": "0x" + "00" * 32,
                "batch_commitment": "0x" + "11" * 32,
                "pre_state_snapshot": {},
                "operations_zlib_b64": base64.b64encode(b"not-zlib").decode("ascii"),
            },
        },
    )

    assert result["ok"] is False
    assert "operations invalid zlib" in result["error"]
