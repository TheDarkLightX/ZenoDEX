#!/usr/bin/env python3
"""Generate one bounded real Spot source receipt for the ZRPF V6 opening lane."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import Any

SOURCE_IMAGE_ID = "1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403"
SOURCE_CLI_SHA256 = "8836f22431e2ce241eec9e6503f741b92673e2fec054208b0c36dea4f1bcf146"
SOURCE_PROGRAM_SHA256 = "d1fd8915a3c1650b42527e6b878f203679cd447b506916c6a9a56008ed0951a8"
MAX_REQUEST_BYTES = 1 << 20
MAX_PROOF_BYTES = 16 << 20
MAX_STDERR_BYTES = 64 << 10


class SourceOpeningError(RuntimeError):
    """The bounded source-opening run failed closed."""


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1 << 20):
            hasher.update(chunk)
    return hasher.hexdigest()


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SourceOpeningError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _decode_exact_json(raw: bytes, *, maximum: int, label: str) -> dict[str, Any]:
    if not raw or len(raw) > maximum:
        raise SourceOpeningError(f"{label} byte length out of bounds")
    try:
        text = raw.decode("utf-8")
        value = json.loads(text, object_pairs_hook=_unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SourceOpeningError(f"{label} is not exact JSON: {exc}") from exc
    if type(value) is not dict:
        raise SourceOpeningError(f"{label} must be a JSON object")
    return value


def _run(
    argv: list[str],
    *,
    input_bytes: bytes | None,
    timeout_seconds: int,
    maximum_stdout: int,
    environment: dict[str, str] | None = None,
) -> bytes:
    completed = subprocess.run(
        argv,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=timeout_seconds,
        env=environment or {"PATH": "/usr/bin:/bin", "RUST_BACKTRACE": "0"},
    )
    if len(completed.stdout) > maximum_stdout:
        raise SourceOpeningError("subprocess stdout exceeds bound")
    if len(completed.stderr) > MAX_STDERR_BYTES:
        raise SourceOpeningError("subprocess stderr exceeds bound")
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace")[-4_096:]
        raise SourceOpeningError(
            f"subprocess failed with exit {completed.returncode}: {detail}"
        )
    if completed.stderr:
        raise SourceOpeningError("successful subprocess emitted stderr")
    return completed.stdout


def _require_request(value: dict[str, Any]) -> None:
    if value.get("schema") != "tau_state_proof_request":
        raise SourceOpeningError("request schema mismatch")
    if value.get("schema_version") != 1:
        raise SourceOpeningError("request schema version mismatch")
    if value.get("proof_type") != "risc0.zenodex_recursive_spot_leaf.v1":
        raise SourceOpeningError("request proof type mismatch")
    if value.get("receipt_kind") != "succinct":
        raise SourceOpeningError("request receipt kind mismatch")
    leaf = value.get("spot_recursive_leaf_input")
    if type(leaf) is not dict:
        raise SourceOpeningError("request Spot input missing")
    words = leaf.get("risc0_image_id")
    if type(words) is not list or len(words) != 8:
        raise SourceOpeningError("request image words malformed")
    spot_input = leaf.get("spot_input")
    if type(spot_input) is not dict:
        raise SourceOpeningError("request state input missing")
    if len(spot_input.get("txs", [])) != 1 or spot_input.get("tx_execution_order") != [0]:
        raise SourceOpeningError("request is not the singleton ordered Spot profile")
    if len(spot_input.get("tx_ingress", [])) != 1:
        raise SourceOpeningError("request ingress is not singleton")


def _require_proof(value: dict[str, Any]) -> None:
    if value.get("schema") != "tau_state_proof" or value.get("schema_version") != 1:
        raise SourceOpeningError("proof envelope schema mismatch")
    if value.get("proof_type") != "risc0.zenodex_recursive_spot_leaf.v1":
        raise SourceOpeningError("proof type mismatch")
    proof = value.get("proof")
    if not isinstance(proof, str) or not proof:
        raise SourceOpeningError("proof receipt missing")
    meta = value.get("meta")
    if type(meta) is not dict:
        raise SourceOpeningError("proof metadata missing")
    if meta.get("risc0_image_id") != SOURCE_IMAGE_ID:
        raise SourceOpeningError("proof image ID mismatch")
    if meta.get("receipt_kind") != "succinct":
        raise SourceOpeningError("proof receipt kind mismatch")


def _write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(descriptor)


def run(
    *,
    generator: Path,
    source_cli: Path,
    r0vm: Path,
    output_directory: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    if _sha256_file(source_cli) != SOURCE_CLI_SHA256:
        raise SourceOpeningError("source CLI digest mismatch")
    output_directory.mkdir(mode=0o700, parents=False, exist_ok=False)
    request_raw = _run(
        [str(generator), "spot-swap", SOURCE_IMAGE_ID],
        input_bytes=None,
        timeout_seconds=60,
        maximum_stdout=MAX_REQUEST_BYTES,
    )
    _require_request(_decode_exact_json(request_raw, maximum=MAX_REQUEST_BYTES, label="request"))
    proof_raw = _run(
        [str(source_cli)],
        input_bytes=request_raw,
        timeout_seconds=timeout_seconds,
        maximum_stdout=MAX_PROOF_BYTES,
        environment={
            "PATH": "/usr/bin:/bin",
            "RISC0_SERVER_PATH": str(r0vm),
            "RUST_BACKTRACE": "0",
            "TMPDIR": str(output_directory),
        },
    )
    _require_proof(_decode_exact_json(proof_raw, maximum=MAX_PROOF_BYTES, label="proof"))
    request_path = output_directory / "spot-swap-source.request.json"
    proof_path = output_directory / "spot-swap-source.receipt.json"
    _write_new(request_path, request_raw)
    _write_new(proof_path, proof_raw)
    report = {
        "schema": "zenodex/zrpf_spot_source_opening_run/v1",
        "ok": True,
        "source_image_id": SOURCE_IMAGE_ID,
        "source_program_sha256": SOURCE_PROGRAM_SHA256,
        "source_cli_sha256": SOURCE_CLI_SHA256,
        "generator_sha256": _sha256_file(generator),
        "r0vm_sha256": _sha256_file(r0vm),
        "request_bytes": len(request_raw),
        "request_sha256": _sha256_bytes(request_raw),
        "proof_bytes": len(proof_raw),
        "proof_sha256": _sha256_bytes(proof_raw),
        "receipt_kind": "succinct",
        "nonclaims": [
            "this run supplies one retained source receipt and no aggregate authority",
            "source proving alone grants no settlement, ledger, release, or production authority",
        ],
    }
    report_raw = (
        json.dumps(report, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
    ).encode("utf-8")
    _write_new(output_directory / "spot-swap-source.report.json", report_raw)
    return report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generator", type=Path, required=True)
    parser.add_argument("--source-cli", type=Path, required=True)
    parser.add_argument("--r0vm", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=3_600)
    arguments = parser.parse_args()
    report = run(
        generator=arguments.generator.resolve(strict=True),
        source_cli=arguments.source_cli.resolve(strict=True),
        r0vm=arguments.r0vm.resolve(strict=True),
        output_directory=arguments.output_directory,
        timeout_seconds=arguments.timeout_seconds,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
