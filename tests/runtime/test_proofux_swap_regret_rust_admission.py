from __future__ import annotations

import json
import subprocess
from pathlib import Path

from docs.research.zeno_ux_swap_regret_rust_replay import build_report
from src.integration.tau_export_acceptance_retrieval import (
    build_tau_export_acceptance_receipt_from_retrieval_v0,
    tau_state_proof_record_key_v0,
    tau_state_record_key_v0,
)
from src.state.jmt import encode_jmt_membership_proof
from tests.integration.test_proofux_swap_regret_admission import _quorum_fixture

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "src/kernels/rust/proofux_swap_regret_admission_v1/Cargo.toml"


def _rust_input() -> dict[str, object]:
    fx = _quorum_fixture()
    projection = fx["projection"]
    membership_proof = json.loads(
        encode_jmt_membership_proof(fx["membership_proof"]).decode("utf-8")
    )
    return {
        "schema": "zenodex.proofux.swap_regret_rust_admission_input.v1",
        "authority": "advisory_proofux",
        "request_snapshot": fx["request"],
        "quote_snapshot": fx["quote_snapshot"],
        "projection": {
            "certificate_hash": projection.certificate_hash,
            "reason": projection.reason,
            "tau_step": dict(projection.tau_step),
        },
        "binding_payload": fx["binding_payload"],
        "signer_registry": fx["registry"],
        "signature_envelopes": list(fx["envelopes"]),
        "post_state_root": fx["app_root"],
        "membership_proof": membership_proof,
        "tau_export_packet": fx["packet"],
        "checkpoint": fx["checkpoint"],
        "header": fx["header"],
    }


class _FakeTauRecordReader:
    def __init__(self, records: dict[str, object]) -> None:
        self.records = records

    def read_tau_record(self, key: str) -> object:
        if key not in self.records:
            raise KeyError(key)
        return self.records[key]


def _state_hash(label: str) -> str:
    if label == "base":
        return "0x" + ("dd" * 32)
    if label == "alternate":
        return "0x" + ("ee" * 32)
    return "0x" + ("cc" * 32)


def _rust_retrieved_acceptance_input(
    *,
    state_proof_meta: dict[str, object] | None = None,
) -> dict[str, object]:
    payload = _rust_input()
    tau_state_hash = _state_hash("base")
    tau_state = {"app_hash": payload["tau_export_packet"]["app_hash"]}
    state_proof = {
        "present": True,
        "state_hash": tau_state_hash[2:],
        "proof_type": "tau.adapter.acceptance.v1",
    }
    if state_proof_meta is not None:
        state_proof["meta"] = state_proof_meta
    records = {
        tau_state_record_key_v0(tau_state_hash): tau_state,
        tau_state_proof_record_key_v0(tau_state_hash): state_proof,
    }
    receipt, _retrieved = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=_FakeTauRecordReader(records),
        tau_state_hash=tau_state_hash,
        packet=payload["tau_export_packet"],
        checkpoint=payload["checkpoint"],
        header=payload["header"],
        body=_quorum_fixture()["body"],
        profile=_quorum_fixture()["profile"],
    )
    return {
        **payload,
        "schema": "zenodex.proofux.swap_regret_rust_retrieved_acceptance_input.v1",
        "tau_state_hash": tau_state_hash,
        "tau_records": records,
        "tau_acceptance_receipt": receipt,
    }


def _run_rust(tmp_path: Path, payload: dict[str, object]) -> dict[str, object]:
    path = tmp_path / "proofux_admission.json"
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    completed = subprocess.run(
        [
            "cargo",
            "run",
            "--quiet",
            "--manifest-path",
            str(MANIFEST),
            "--",
            "verify",
            str(path),
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=120,
    )
    assert completed.returncode == 0, completed.stderr
    return json.loads(completed.stdout)


def test_rust_proofux_admission_accepts_python_verified_bundle(tmp_path: Path) -> None:
    payload = _rust_input()
    out = _run_rust(tmp_path, payload)

    assert out["ok"] is True
    result = out["result"]
    assert result["settlement_authority"] is False
    assert result["binding_hash"] == payload["binding_payload"]["binding_hash"]
    assert result["post_state_root"] == payload["post_state_root"]
    assert result["packet_app_hash"] == payload["tau_export_packet"]["app_hash"]
    assert result["packet_app_hash"] != payload["post_state_root"]
    assert result["tau_state_hash"] is None
    assert result["tau_state_key"] is None
    assert result["state_proof_key"] is None
    assert result["tau_acceptance_receipt_hash"] is None


def test_rust_proofux_retrieved_acceptance_consumes_keyed_tau_records(tmp_path: Path) -> None:
    payload = _rust_retrieved_acceptance_input()
    out = _run_rust(tmp_path, payload)

    assert out["ok"] is True
    result = out["result"]
    assert result["settlement_authority"] is False
    assert result["tau_state_hash"] == payload["tau_state_hash"]
    assert result["tau_state_key"] == tau_state_record_key_v0(payload["tau_state_hash"])
    assert result["state_proof_key"] == tau_state_proof_record_key_v0(payload["tau_state_hash"])
    assert result["tau_acceptance_receipt_hash"] == payload["tau_acceptance_receipt"]["receipt_hash"]


def test_rust_proofux_retrieved_acceptance_binds_frontier_signature_root(
    tmp_path: Path,
) -> None:
    payload = _rust_retrieved_acceptance_input(
        state_proof_meta={
            "shared_pool_frontier_signature_certificate_count": 1,
            "shared_pool_frontier_signature_certificates_root": "aa" * 32,
        }
    )
    out = _run_rust(tmp_path, payload)

    assert out["ok"] is True
    assert (
        payload["tau_acceptance_receipt"][
            "shared_pool_frontier_signature_certificates_root"
        ]
        == "0x" + "aa" * 32
    )

    tampered_receipt = {
        **payload["tau_acceptance_receipt"],
        "shared_pool_frontier_signature_certificates_root": "0x" + "bb" * 32,
    }
    assert _run_rust(
        tmp_path,
        dict(payload, tau_acceptance_receipt=tampered_receipt),
    ) == {
        "ok": False,
        "error": "tau_acceptance_receipt_mismatch",
    }


def test_rust_proofux_retrieved_acceptance_rejects_key_mutations(tmp_path: Path) -> None:
    payload = _rust_retrieved_acceptance_input()
    state_key = tau_state_record_key_v0(payload["tau_state_hash"])
    proof_key = tau_state_proof_record_key_v0(payload["tau_state_hash"])

    missing_state = dict(
        payload,
        tau_records={proof_key: payload["tau_records"][proof_key]},
    )
    assert _run_rust(tmp_path, missing_state) == {
        "ok": False,
        "error": "tau_state_record_missing",
    }

    missing_proof = dict(
        payload,
        tau_records={state_key: payload["tau_records"][state_key]},
    )
    assert _run_rust(tmp_path, missing_proof) == {
        "ok": False,
        "error": "tau_state_proof_record_missing",
    }

    wrong_hash_records = dict(payload["tau_records"])
    wrong_hash_records[proof_key] = {
        **wrong_hash_records[proof_key],
        "state_hash": _state_hash("alternate")[2:],
    }
    assert _run_rust(tmp_path, dict(payload, tau_records=wrong_hash_records)) == {
        "ok": False,
        "error": "tau_state_proof_hash_mismatch",
    }

    wrong_app_records = dict(payload["tau_records"])
    wrong_app_records[state_key] = {"app_hash": "0x" + ("aa" * 32)}
    assert _run_rust(tmp_path, dict(payload, tau_records=wrong_app_records)) == {
        "ok": False,
        "error": "tau_state_app_hash_mismatch",
    }

    forged_receipt = {
        **payload["tau_acceptance_receipt"],
        "authorizes_settlement": True,
    }
    assert _run_rust(tmp_path, dict(payload, tau_acceptance_receipt=forged_receipt)) == {
        "ok": False,
        "error": "tau_settlement_authority_requested",
    }

    other_hash = _state_hash("alternate")
    other_key = tau_state_record_key_v0(other_hash)
    other_proof_key = tau_state_proof_record_key_v0(other_hash)
    other_records = {
        other_key: payload["tau_records"][state_key],
        other_proof_key: {
            **payload["tau_records"][proof_key],
            "state_hash": other_hash[2:],
        },
    }
    replayed_other_key = dict(
        payload,
        tau_state_hash=other_hash,
        tau_records=other_records,
    )
    assert _run_rust(tmp_path, replayed_other_key) == {
        "ok": False,
        "error": "tau_acceptance_receipt_mismatch",
    }


def test_rust_proofux_admission_rejects_authority_and_substitutions(tmp_path: Path) -> None:
    payload = _rust_input()

    settlement = dict(payload, authority="settlement_authority")
    assert _run_rust(tmp_path, settlement) == {
        "ok": False,
        "error": "authority_not_advisory",
    }

    one_signature = dict(payload, signature_envelopes=payload["signature_envelopes"][:1])
    assert _run_rust(tmp_path, one_signature) == {
        "ok": False,
        "error": "threshold_not_met",
    }

    tampered_request = dict(
        payload,
        request_snapshot={**payload["request_snapshot"], "amount_in": 10_001},
    )
    assert _run_rust(tmp_path, tampered_request) == {
        "ok": False,
        "error": "binding_payload_mismatch",
    }

    wrong_root = dict(
        payload,
        post_state_root="0x" + ("ff" * 32),
    )
    assert _run_rust(tmp_path, wrong_root) == {
        "ok": False,
        "error": "jmt_proof_mismatch",
    }

    wrong_packet_root = dict(
        payload,
        tau_export_packet={
            **payload["tau_export_packet"],
            "post_state_root": "0x" + ("ff" * 32),
        },
    )
    assert _run_rust(tmp_path, wrong_packet_root) == {
        "ok": False,
        "error": "packet_post_state_root_mismatch",
    }

    tampered_signature_rows = list(payload["signature_envelopes"])
    tampered_signature_rows[0] = {
        **tampered_signature_rows[0],
        "signature": "0x" + ("00" * 96),
    }
    tampered_signature = dict(payload, signature_envelopes=tampered_signature_rows)
    assert _run_rust(tmp_path, tampered_signature) == {
        "ok": False,
        "error": "bls_signature_invalid",
    }

    tampered_packet = dict(
        payload,
        tau_export_packet={**payload["tau_export_packet"], "app_hash": "0x" + ("ee" * 32)},
    )
    assert _run_rust(tmp_path, tampered_packet) == {
        "ok": False,
        "error": "packet_app_hash_mismatch",
    }


def test_rust_proofux_replay_pins_boundary_claims() -> None:
    report = build_report()

    assert report["boundary_claims"] == {
        "valid_bundle_accepts": True,
        "settlement_authority_false": True,
        "post_state_root_bound": True,
        "app_hash_is_derived": True,
        "settlement_authority_rejects": True,
        "one_signature_rejects": True,
        "tampered_request_rejects": True,
        "wrong_post_state_root_rejects": True,
        "wrong_packet_post_state_root_rejects": True,
        "tampered_signature_rejects": True,
        "tampered_app_hash_rejects": True,
    }
