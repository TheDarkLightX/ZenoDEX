"""WS2 end-to-end: the refuse-by-default loop over a REAL RISC0 STARK.

Opt-in (a real prove takes minutes of CPU): ZENODEX_WS2_E2E=1 plus a built CLI.
This is the measured evidence that the production ports close the WS2 honesty
gap — every layer here is real: a real receipt is proven, the blessed binary is
sha256-pinned, receipt.verify runs cryptographically, the journal is decoded
from receipt-committed bytes, the rebind recomputes the operation hashes, and
the shell advances the head exactly once.

Honesty posture exercised BOTH ways:
  - the PRODUCTION pinset (admission allow-list EMPTY) REFUSES even this valid
    real proof with ADMISSION_NOT_PROOF_GATED — refuse-by-default is the truthful
    state until Stage 3 proof-gates a deployed admission path;
  - the DEMO-STAGE3 pinset (clearly labelled) exercises the full ACCEPT path.

The initial client head is the proof's pre-state hash, standing in for "a head
the client already trusts" (genesis/checkpoint). DA/ordering trust for that
initial head is out of scope here and stays on the WS2 residual list.
"""

from __future__ import annotations

import base64
import importlib.util
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any, Mapping

import pytest

from src.integration.client_admission_decision import RefuseCode
from src.integration.client_admission_loop import (
    ClientAdmissionLoop,
    MultiHostAdmissionClient,
)
from src.integration.client_pinned_registry import (
    load_consensus_contract,
    load_pinned_registry,
)
from src.integration.perps_np_rebind import perps_np_deposit_rebind
from src.integration.risc0_receipt_verifier_port import Risc0CliReceiptVerifierPort

REPO = Path(__file__).resolve().parents[2]
CLI_BIN = REPO / "zk" / "state_proof_risc0" / "target" / "release" / "tau-state-proof-risc0-cli"
PERPS_PT = "risc0.zenodex_perps_np_transition.v1"
SURFACE, OPERATION = "perps_np", "deposit_collateral"

pytestmark = pytest.mark.skipif(
    os.environ.get("ZENODEX_WS2_E2E") != "1" or not CLI_BIN.is_file(),
    reason="opt-in real-STARK e2e (set ZENODEX_WS2_E2E=1 with the CLI built)",
)


def _smoke_module():
    spec = importlib.util.spec_from_file_location(
        "perps_np_smoke", REPO / "tools" / "zeno_ledger_perp_np_risc0_real_proof_smoke.py"
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _run_cli(request: Mapping[str, Any], *, timeout: float) -> dict[str, Any]:
    proc = subprocess.run(
        [str(CLI_BIN)],
        input=json.dumps(request, separators=(",", ":")),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr[-400:]
    return json.loads(proc.stdout)


DEPOSIT_FIELDS: dict[str, Any] = {
    "pubkey": "wallet-aa",
    "asset": "zUSD",
    "amount_e8": 500_000_000,
    "nonce": 1,
    "collateral_binding": {
        "source_proof_type": "risc0.zenodex_zusd_transition.v1",
        "source_state_hash": "11" * 32,
        "balance_root_hash": "22" * 32,
        "balance_delta_hash": "33" * 32,
    },
}


@pytest.fixture(scope="module")
def real_proof() -> dict[str, Any]:
    """Prove ONE real deposit transition; reuse it across every scenario."""
    smoke = _smoke_module()
    case_input = smoke._cases()["four_wallet"]["input"]
    pre_state = smoke._current_pre_state_from_input(case_input)
    pre_hash = smoke._current_snapshot_hash(pre_state)
    chain_id = str(case_input["chain_id"])
    action = {"kind": "deposit_collateral", **DEPOSIT_FIELDS}
    base = {
        "proof_type": PERPS_PT,
        "state_hash": "ab" * 32,
        "chain_id": chain_id,
        "context": {
            "chain_id": chain_id,
            "app_hash_pre": pre_hash,
            "perps_state_pre": pre_state,
        },
        "pre_state": pre_state,
        "actions": [action],
    }
    executed = _run_cli(
        {"schema": "tau_state_transition_execute", "schema_version": 1, **base}, timeout=120
    )
    assert executed.get("accepted") is True, executed
    post_hash = executed["meta"]["post_app_hash"]

    started = time.monotonic()
    generated = _run_cli(
        {
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            **base,
            "expected_post_app_hash": post_hash,
            "tau_state": {"app_hash": post_hash},
        },
        timeout=3600,
    )
    prove_seconds = time.monotonic() - started
    receipt_bytes = base64.b64decode(generated["proof"])
    return {
        "receipt_bytes": receipt_bytes,
        "pre_head": bytes.fromhex(pre_hash),
        "post_head": bytes.fromhex(post_hash),
        "chain_id": chain_id,
        "prove_seconds": prove_seconds,
    }


def _pinset(tmp_path: Path, *, demo_stage3: bool, chain_id: str) -> Path:
    out = tmp_path / ("pinset_demo.json" if demo_stage3 else "pinset_prod.json")
    cmd = [
        "python3",
        str(REPO / "tools" / "gen_ws2_client_pinset_local.py"),
        "--out",
        str(out),
        "--chain-id",
        chain_id,
    ]
    if demo_stage3:
        cmd.append("--demo-stage3")
    subprocess.run(cmd, check=True, stdout=subprocess.PIPE, timeout=120)
    return out


def _loop(pinset_path: Path, initial_head: bytes) -> ClientAdmissionLoop:
    return ClientAdmissionLoop(
        SURFACE,
        initial_head,
        registry=load_pinned_registry(pinset_path),
        contract=load_consensus_contract(),
        verifier_by_operation={OPERATION: Risc0CliReceiptVerifierPort(PERPS_PT)},
        rebind_by_operation={OPERATION: perps_np_deposit_rebind},
    )


def test_production_pinset_refuses_valid_proof_admission_not_gated(
    real_proof: dict[str, Any], tmp_path: Path
) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=False, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )
    decision = loop.submit(OPERATION, {"zk_proof": real_proof["receipt_bytes"]}, DEPOSIT_FIELDS)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.ADMISSION_NOT_PROOF_GATED
    # The proof itself verified (gate 3 passed); the refusal is the HONEST one.
    assert decision.gate_results.get("g3_receipt_verify") is True
    assert loop.current_head() == real_proof["pre_head"]


def test_demo_stage3_full_accept_and_replay_refused(
    real_proof: dict[str, Any], tmp_path: Path
) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )
    host_response = {
        # Host-asserted fields are deliberately present: the tripwire must note
        # them and the decision must not read them.
        "ok": True,
        "proof_status": "verified",
        "production_security_claim": True,
        "zk_proof": real_proof["receipt_bytes"],
    }
    started = time.monotonic()
    decision = loop.submit(OPERATION, host_response, DEPOSIT_FIELDS)
    verify_seconds = time.monotonic() - started
    assert decision.accepted, decision
    assert decision.claim_level == "live_replay_authority_equivalent"
    assert decision.tripwire is not None
    assert loop.current_head() == real_proof["post_head"]

    replay = loop.submit(OPERATION, host_response, DEPOSIT_FIELDS)
    assert not replay.accepted
    assert replay.refuse_code == RefuseCode.PRESTATE_MISMATCH

    print(
        f"\n[ws2-e2e] prove={real_proof['prove_seconds']:.1f}s "
        f"verify+decide={verify_seconds:.2f}s receipt_bytes={len(real_proof['receipt_bytes'])}"
    )


def test_tampered_receipt_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )
    tampered = bytearray(real_proof["receipt_bytes"])
    tampered[len(tampered) // 2] ^= 0x01
    decision = loop.submit(OPERATION, {"zk_proof": bytes(tampered)}, DEPOSIT_FIELDS)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.RECEIPT_VERIFY_FAILED
    assert loop.current_head() == real_proof["pre_head"]


def test_fake_green_without_proof_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )
    decision = loop.submit(
        OPERATION,
        {"ok": True, "proof_status": "verified", "production_security_claim": True},
        DEPOSIT_FIELDS,
    )
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.NO_PROOF


def test_cheap_for_expensive_replay_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )
    requested = dict(DEPOSIT_FIELDS)
    requested["amount_e8"] = DEPOSIT_FIELDS["amount_e8"] + 1
    decision = loop.submit(OPERATION, {"zk_proof": real_proof["receipt_bytes"]}, requested)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.OPERATION_MISMATCH


def test_wrong_image_pin_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    pinset_path = _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"])
    data = json.loads(pinset_path.read_text())
    data["pins"][0]["risc0_image_id_words"][0] ^= 1
    pinset_path.write_text(json.dumps(data))
    loop = _loop(pinset_path, real_proof["pre_head"])
    decision = loop.submit(OPERATION, {"zk_proof": real_proof["receipt_bytes"]}, DEPOSIT_FIELDS)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.RECEIPT_VERIFY_FAILED


def test_tampered_blessed_binary_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    pinset_path = _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"])
    data = json.loads(pinset_path.read_text())
    impostor = tmp_path / "impostor-cli"
    impostor.write_bytes(CLI_BIN.read_bytes() + b"\x00")
    impostor.chmod(0o755)
    data["pins"][0]["blessed_verifier"]["binary_path"] = str(impostor)
    pinset_path.write_text(json.dumps(data))
    loop = _loop(pinset_path, real_proof["pre_head"])
    decision = loop.submit(OPERATION, {"zk_proof": real_proof["receipt_bytes"]}, DEPOSIT_FIELDS)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.RECEIPT_VERIFY_FAILED


def test_wrong_chain_pin_refused(real_proof: dict[str, Any], tmp_path: Path) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id="zenodex-mainnet-1"),
        real_proof["pre_head"],
    )
    decision = loop.submit(OPERATION, {"zk_proof": real_proof["receipt_bytes"]}, DEPOSIT_FIELDS)
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.CHAIN_ID_MISMATCH


def test_multiplicity_with_real_proof(real_proof: dict[str, Any], tmp_path: Path) -> None:
    loop = _loop(
        _pinset(tmp_path, demo_stage3=True, chain_id=real_proof["chain_id"]),
        real_proof["pre_head"],
    )

    def withholding(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        raise TimeoutError("withheld")

    def corrupting(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        return {"ok": True, "proof_status": "verified"}

    def honest(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        return {"zk_proof": real_proof["receipt_bytes"]}

    client = MultiHostAdmissionClient(
        loop, [("withholding", withholding), ("corrupting", corrupting), ("honest", honest)]
    )
    outcome = client.fetch_and_admit(OPERATION, DEPOSIT_FIELDS, {"op": OPERATION})
    assert outcome.accepted and outcome.served_by == "honest"
    assert outcome.attempts[1].refuse_code == RefuseCode.NO_PROOF
    assert loop.current_head() == real_proof["post_head"]
