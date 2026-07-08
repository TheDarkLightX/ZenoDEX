"""Bounded subprocess adapter for the perps Tau source-admission Rust verifier."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from ..state.canonical import canonical_json_bytes

_CLI_INPUT_SCHEMA = "zenodex.perp_liquidation_tau_source_admission_envelope_rust_parity_input.v1"
_SELF_TEST_CONTRACT_SCHEMA = "zenodex.perp_source_admission_verifier_startup_contract.v1"
DEFAULT_AUTHORITY_POLICY_RECEIPT_VERIFIER_SELF_TEST_CONTRACT = (
    Path(__file__).resolve().parents[2]
    / "config"
    / "verifier_contracts"
    / "perp_source_admission_envelope_v1_startup_contract.json"
)
VerifierResult = dict[str, Any]


def build_tau_source_authority_policy_receipt_cli_verifier(
    *,
    verifier_path: str,
    timeout_s: float = 5.0,
    max_input_bytes: int = 256_000,
    max_stdout_bytes: int = 32_000,
    max_stderr_bytes: int = 8_000,
) -> Callable[[Mapping[str, Any]], VerifierResult]:
    """Return a fail-closed verifier callback for ``PerpEngineConfig``.

    The engine passes a runtime-check wrapper. The Rust CLI expects the same
    binding/context/receipt payload under its parity-input schema.
    """
    path = Path(verifier_path).expanduser()
    if not path.is_absolute():
        raise ValueError("TAU source authority policy verifier path must be absolute")
    if not path.is_file():
        raise ValueError("TAU source authority policy verifier path must name a file")
    if not os.access(path, os.X_OK):
        raise ValueError("TAU source authority policy verifier path must be executable")
    if timeout_s <= 0:
        raise ValueError("TAU source authority policy verifier timeout must be positive")
    if max_input_bytes <= 0 or max_stdout_bytes <= 0 or max_stderr_bytes <= 0:
        raise ValueError("TAU source authority policy verifier byte limits must be positive")

    def reject(error: str) -> VerifierResult:
        return {"status": "rejected", "error": error, "errors": [error]}

    def verify(payload: Mapping[str, Any]) -> VerifierResult:
        if not isinstance(payload, Mapping):
            return reject("verifier_payload_not_object")
        cli_payload: dict[str, Any] = {
            "schema": _CLI_INPUT_SCHEMA,
            "tau_source_binding": payload.get("tau_source_binding"),
            "authority_policy_context": payload.get("authority_policy_context"),
            "authority_policy_receipt": payload.get("authority_policy_receipt"),
        }
        oracle_receipt = payload.get("oracle_adapter_proof_receipt_hash")
        if oracle_receipt is not None:
            cli_payload["oracle_adapter_proof_receipt_hash"] = oracle_receipt
        raw = canonical_json_bytes(cli_payload)
        if len(raw) > max_input_bytes:
            return reject("verifier_input_too_large")

        with tempfile.NamedTemporaryFile(prefix="tau_source_policy_", suffix=".json") as tmp:
            tmp.write(raw)
            tmp.flush()
            try:
                proc = subprocess.run(
                    [str(path), "verify", tmp.name],
                    capture_output=True,
                    check=False,
                    timeout=float(timeout_s),
                )
            except subprocess.TimeoutExpired:
                return reject("verifier_timeout")
            except OSError as exc:
                return reject(f"verifier_exec_error:{exc.__class__.__name__}")

        if len(proc.stdout) > max_stdout_bytes:
            return reject("verifier_stdout_too_large")
        if len(proc.stderr) > max_stderr_bytes:
            return reject("verifier_stderr_too_large")
        try:
            out = json.loads(proc.stdout.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            return reject("verifier_invalid_json")
        if not isinstance(out, Mapping):
            return reject("verifier_output_not_object")
        if proc.returncode != 0:
            error = out.get("error") if isinstance(out.get("error"), str) else "verifier_nonzero_exit"
            return reject(error)
        if out.get("ok") is not True:
            error = out.get("error") if isinstance(out.get("error"), str) else "verifier_rejected"
            return reject(error)
        result = out.get("result")
        if not isinstance(result, Mapping):
            return reject("verifier_missing_result")
        return {"status": "accepted", **dict(result)}

    return verify


def self_test_tau_source_authority_policy_receipt_cli_verifier(
    *,
    verifier_path: str,
    contract_path: str | os.PathLike[str] | None = None,
    timeout_s: float = 5.0,
) -> list[str]:
    """Return startup-contract failures for the configured Rust verifier.

    This is a production-startup guard, not proof evidence. It catches a wrong
    binary, broken wiring, or a verifier that accepts a pinned mutation before
    the API advertises a strict source-admission profile.
    """
    path = (
        Path(contract_path)
        if contract_path is not None
        else DEFAULT_AUTHORITY_POLICY_RECEIPT_VERIFIER_SELF_TEST_CONTRACT
    )
    try:
        contract_obj = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return [f"self_test_contract_missing:{path}"]
    except json.JSONDecodeError as exc:
        return [f"self_test_contract_invalid_json:{exc.msg}"]
    if not isinstance(contract_obj, Mapping):
        return ["self_test_contract_not_object"]
    if contract_obj.get("schema") != _SELF_TEST_CONTRACT_SCHEMA:
        return [f"self_test_contract_bad_schema:{contract_obj.get('schema')!r}"]
    cases = contract_obj.get("cases")
    if not isinstance(cases, Sequence) or isinstance(cases, (str, bytes, bytearray)):
        return ["self_test_contract_cases_not_array"]
    try:
        verify = build_tau_source_authority_policy_receipt_cli_verifier(
            verifier_path=verifier_path,
            timeout_s=timeout_s,
        )
    except ValueError as exc:
        return [f"self_test_verifier_config_invalid:{exc}"]

    errors: list[str] = []
    seen_accept = False
    seen_reject = False
    for index, raw_case in enumerate(cases):
        if not isinstance(raw_case, Mapping):
            errors.append(f"case_{index}:not_object")
            continue
        name = str(raw_case.get("name") or f"case_{index}")
        payload = raw_case.get("payload")
        expected = raw_case.get("expected")
        if not isinstance(payload, Mapping):
            errors.append(f"{name}:payload_not_object")
            continue
        if not isinstance(expected, Mapping):
            errors.append(f"{name}:expected_not_object")
            continue
        result = verify(payload)
        expected_status = expected.get("status")
        if expected_status == "accepted":
            seen_accept = True
            if result.get("status") != "accepted":
                errors.append(f"{name}:expected_accepted_got_{result.get('error', result.get('status'))}")
                continue
            result_fields = expected.get("result_fields", {})
            if not isinstance(result_fields, Mapping):
                errors.append(f"{name}:result_fields_not_object")
                continue
            for key, expected_value in result_fields.items():
                if result.get(key) != expected_value:
                    errors.append(f"{name}:field_{key}_mismatch")
        elif expected_status == "rejected":
            seen_reject = True
            expected_error = expected.get("error")
            result_errors = result.get("errors")
            if not isinstance(result_errors, list):
                result_errors = [result.get("error")]
            if result.get("status") != "rejected" or expected_error not in result_errors:
                errors.append(f"{name}:expected_rejected_{expected_error}_got_{result.get('error', result.get('status'))}")
        else:
            errors.append(f"{name}:bad_expected_status:{expected_status!r}")
    if not seen_accept:
        errors.append("self_test_contract_missing_accept_case")
    if not seen_reject:
        errors.append("self_test_contract_missing_reject_case")
    return errors
