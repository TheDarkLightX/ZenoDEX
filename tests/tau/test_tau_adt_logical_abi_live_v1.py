"""Tau ADT logical ABI V1 - live replay against the exact pinned binary (opt-in).

Set ``ZENO_TAU_ADT_LIVE=1`` to execute. When requested, the pinned binary MUST
be present (``external/tau-lang-adt-logical-abi-v1/build-Release/tau`` or
``ZENO_TAU_ADT_BIN``); its absence is a failure with a typed reason, never a
skip. The fresh run must reproduce the committed receipt verdict-for-verdict.
When not requested the test is skipped with an explicit reason: the evidence
of record is the committed receipt, verified offline by
``test_tau_adt_logical_abi_replay_receipt_v1``. Research-only; authority NONE.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
RENDERER = ROOT / "experiments" / "tau_adt_abi" / "render_tau_adt_abi_v2.py"
RECEIPT = ROOT / "tests" / "data" / "tau_adt_logical_abi_replay_receipt_v1.json"
DEFAULT_BIN = ROOT / "external" / "tau-lang-adt-logical-abi-v1" / "build-Release" / "tau"


def test_tau_adt_logical_abi_live_v1(tmp_path: Path) -> None:
    if os.environ.get("ZENO_TAU_ADT_LIVE") != "1":
        pytest.skip("TAU_LIVE_NOT_REQUESTED: set ZENO_TAU_ADT_LIVE=1; the evidence of record is the committed receipt")
    binary = Path(os.environ.get("ZENO_TAU_ADT_BIN", str(DEFAULT_BIN)))
    if not binary.is_file():
        pytest.fail(f"TAU_PIN_UNAVAILABLE: no pinned Tau binary at {binary}")
    fresh = tmp_path / "receipt.json"
    proc = subprocess.run(
        [sys.executable, str(RENDERER), "--receipt", str(fresh)],
        cwd=ROOT, capture_output=True, text=True, timeout=3600,
        env={**os.environ, "ZENO_TAU_ADT_BIN": str(binary)},
    )
    assert proc.returncode == 0, proc.stderr[-4000:]
    live = json.loads(fresh.read_text(encoding="utf-8"))
    committed = json.loads(RECEIPT.read_text(encoding="utf-8"))
    assert live["ok"] is True
    assert live["tau_commit"] == committed["tau_commit"]
    assert live["tau_binary_sha256"] == committed["tau_binary_sha256"], "binary drift"
    assert live["renderer_sha256"] == committed["renderer_sha256"]
    assert live["spec_sha256"] == committed["spec_sha256"]
    assert live["selftest"] == committed["selftest"]
    assert live["capability_probes"] == committed["capability_probes"]
    assert [(r["vector"], r["python_code"], {k: p["verdict"] for k, p in r["programs"].items()}) for r in live["vectors"]] == [
        (r["vector"], r["python_code"], {k: p["verdict"] for k, p in r["programs"].items()}) for r in committed["vectors"]
    ]
