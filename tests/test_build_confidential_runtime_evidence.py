from __future__ import annotations

import json
from pathlib import Path

from src.integration.confidential_runtime_receipts import (
    CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1,
    confidential_runtime_execution_receipt_hash_v1,
)
from src.integration.production_promotion_evidence import (
    attach_production_confidential_runtime_hash_v1,
    evaluate_production_confidential_runtime_evidence_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from tools import build_confidential_runtime_evidence as builder

NOW = 1747878000
NITRO_MEASUREMENT = "nitro:b" + "1" * 95
AZURE_MEASUREMENT = "azure-sevsnp:c" + "2" * 95


def _approved_hash() -> str:
    return hash_v0(
        "production_confidential_runtime_approved_measurements_v1",
        {"approved_measurements": sorted({NITRO_MEASUREMENT, AZURE_MEASUREMENT})},
    ).removeprefix("0x")


def _runtime_receipt_hash() -> str:
    body = {
        "schema": CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1,
        "attestation_receipt_hash": "0x" + "55" * 32,
        "extension_id": "confidential-ext-prod",
        "provider_id": "nitro-prod-1",
        "request_id": "req-1",
        "execution_id": "exec-1",
        "execution_kind": "redacted_compute",
        "result_code": "ok",
        "measurement_provider": "nitro",
        "operator_status_hash": "0x" + "22" * 32,
        "approved_measurements_hash": "0x" + _approved_hash(),
        "external_verifier_binding_hash": "0x" + "33" * 32,
        "attestation_epoch": 40,
        "current_epoch": 42,
        "units_charged": 7,
        "result_redacted": True,
        "public_effect_digest": "0x" + "44" * 32,
        "public_summary": {
            "execution_admitted": True,
            "policy_ok": True,
            "output_bound_ok": True,
            "request_bound": True,
        },
    }
    return confidential_runtime_execution_receipt_hash_v1(body).removeprefix("0x")


def _base_args(out: Path) -> list[str]:
    return [
        "--out",
        str(out),
        "--extension-id",
        "confidential-ext-prod",
        "--provider-id",
        "nitro-prod-1",
        "--tee-kind",
        "nitro",
        "--raw-attestation-hash",
        "aa" * 32,
        "--measurement",
        NITRO_MEASUREMENT,
        "--measurement-in-allowlist",
        "--platform-pubkey",
        "cc" * 32,
        "--attestation-signature",
        "dd" * 64,
        "--tee-verified-at",
        str(NOW - 60),
        "--operator-status-hash",
        "22" * 32,
        "--external-verifier-binding-hash",
        "33" * 32,
        "--runtime-receipt-hash",
        _runtime_receipt_hash(),
        "--attestation-receipt-hash",
        "55" * 32,
        "--request-id",
        "req-1",
        "--execution-id",
        "exec-1",
        "--execution-kind",
        "redacted_compute",
        "--result-code",
        "ok",
        "--result-redacted",
        "--attestation-epoch",
        "40",
        "--current-epoch",
        "42",
        "--units-charged",
        "7",
        "--public-effect-digest",
        "44" * 32,
        "--issued-at",
        str(NOW),
        "--check-now",
        str(NOW),
        "--approved-measurement",
        NITRO_MEASUREMENT,
        "--approved-measurement",
        AZURE_MEASUREMENT,
        "--expected-extension-id",
        "confidential-ext-prod",
    ]


def test_confidential_runtime_builder_writes_lane_ready_evidence(capsys, tmp_path: Path) -> None:
    out = tmp_path / "confidential_runtime.json"

    assert builder.main([*_base_args(out), "--check"]) == 0

    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    lane = evaluate_production_confidential_runtime_evidence_v1(
        evidence,
        approved_measurements=[NITRO_MEASUREMENT, AZURE_MEASUREMENT],
        operator_status_hash="22" * 32,
        external_verifier_binding_hash="33" * 32,
        expected_extension_id="confidential-ext-prod",
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []
    assert lane["bindings"]["tee_kind"] == "nitro"
    assert len(evidence["evidence_hash"]) == 64


def test_confidential_runtime_builder_derives_approved_measurements_hash(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)

    assert builder.main([*args, "--check"]) == 0

    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    assert evidence["approved_measurements_hash"] == _approved_hash()


def test_confidential_runtime_builder_check_rejects_allowlist_hash_drift(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = [
        *_base_args(out),
        "--approved-measurements-hash",
        "11" * 32,
    ]

    assert builder.main([*args, "--check"]) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "approved measurements hash does not match" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_rejects_runtime_receipt_hash_drift(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--runtime-receipt-hash") + 1] = "99" * 32

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "runtime receipt hash does not match" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_check_rejects_measurement_kind_mismatch(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--measurement") + 1] = AZURE_MEASUREMENT

    assert builder.main([*args, "--check"]) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "measurement prefix does not match" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_rejects_malformed_platform_pubkey(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--platform-pubkey") + 1] = "not-hex"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "platform pubkey" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_rejects_unsafe_execution_token_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--execution-id") + 1] = "exec bad"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "execution_id must be a safe token" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_rejects_non_ok_result_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--result-code") + 1] = "failed"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "result_code must be ok" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_evaluator_rejects_rehashed_non_ok_result(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"

    assert builder.main(_base_args(out)) == 0
    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["private_execution_receipt"]["result_code"] = "failed"
    tampered = attach_production_confidential_runtime_hash_v1(evidence)

    lane = evaluate_production_confidential_runtime_evidence_v1(
        tampered,
        approved_measurements=[NITRO_MEASUREMENT, AZURE_MEASUREMENT],
        operator_status_hash="22" * 32,
        external_verifier_binding_hash="33" * 32,
        expected_extension_id="confidential-ext-prod",
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "private_execution_receipt.result_code must be ok" in lane["gaps"]


def test_confidential_runtime_evaluator_rejects_rehashed_runtime_receipt_hash_drift(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"

    assert builder.main(_base_args(out)) == 0
    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["private_execution_receipt"]["runtime_receipt_hash"] = "88" * 32
    tampered = attach_production_confidential_runtime_hash_v1(evidence)

    lane = evaluate_production_confidential_runtime_evidence_v1(
        tampered,
        approved_measurements=[NITRO_MEASUREMENT, AZURE_MEASUREMENT],
        operator_status_hash="22" * 32,
        external_verifier_binding_hash="33" * 32,
        expected_extension_id="confidential-ext-prod",
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert (
        "private_execution_receipt.runtime_receipt_hash does not match canonical runtime receipt"
        in lane["gaps"]
    )


def test_confidential_runtime_builder_rejects_stale_tee_verification_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    args[args.index("--tee-verified-at") + 1] = str(NOW - 2 * 24 * 3600)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "TEE verification window" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_requires_approved_measurements_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    while "--approved-measurement" in args:
        index = args.index("--approved-measurement")
        del args[index : index + 2]

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "confidential_runtime_evidence_build_failed"
    assert "--approved-measurement is required" in payload["detail"]
    assert not out.exists()


def test_confidential_runtime_builder_check_rejects_stale_issued_at(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "confidential_runtime.json"
    args = _base_args(out)
    stale_issued = NOW - 31 * 24 * 3600
    args[args.index("--issued-at") + 1] = str(stale_issued)
    args[args.index("--tee-verified-at") + 1] = str(stale_issued - 60)

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("freshness" in gap for gap in err["gaps"])
    assert not out.exists()
