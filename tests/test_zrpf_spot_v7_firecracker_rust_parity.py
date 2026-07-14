"""Cross-language vectors for the authority-neutral Spot V7 raw protocol."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from collections.abc import Callable
from pathlib import Path

from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1,
    SpotV7FirecrackerProtocolRejectV1,
    SpotV7FirecrackerRequestV1,
    build_data_only_committed_output_v1,
    decode_exact_request_v1,
    decode_structural_v7_verifier_payload_v1,
    validate_exact_committed_output_v1,
)

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT / "zk/spot_settlement_v7_risc0"
GOLDEN_PAYLOAD = (
    WORKSPACE / "verifier/tests/vectors/spot_settlement_v7_firecracker_output_v1.hex"
)
RUST_PACKAGE = "zenodex-zrpf-spot-v7-firecracker-runtime"
RUST_VECTOR_BINARY = "spot-v7-firecracker-protocol-vector-v1"
RUST_NEGATIVE_VECTOR_BINARY = "spot-v7-firecracker-negative-vector-v1"
EXPECTED_FIELDS = frozenset(
    {
        "output_sha256",
        "payload_sha256",
        "profile_sha256",
        "request_sha256",
    }
)


def test_rust_protocol_vector_matches_independent_python_codec(tmp_path: Path) -> None:
    rust_vector = _run_rust_vector(tmp_path)
    request = SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=bytes([1]) * 32,
        runtime_manifest_sha256=bytes([2]) * 32,
        machine_config_sha256=bytes([3]) * 32,
        input_drive_sha256=bytes([4]) * 32,
        settlement_intent_sha256=bytes([5]) * 32,
    )
    payload = _read_golden_payload()
    output = build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=bytes([4]) * 32,
        payload=payload,
    )
    python_vector = {
        "output_sha256": hashlib.sha256(output).hexdigest(),
        "payload_sha256": hashlib.sha256(payload).hexdigest(),
        "profile_sha256": hashlib.sha256(
            SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1
        ).hexdigest(),
        "request_sha256": request.sha256.hex(),
    }
    assert rust_vector == python_vector
    assert rust_vector == {
        "output_sha256": (
            "d5d88a069e65df2776ce440a148695998abe2ad0ee9185cdd4c9c4bd0eccc595"
        ),
        "payload_sha256": (
            "979b2e9cb4757de50ec935c55ca827c693ad5cb4e22ee8034bee9e7866de148c"
        ),
        "profile_sha256": (
            "c8cf02b22988315b667c8b37675b6c8d8cd56f5638b8aa176357a044a89fcdd6"
        ),
        "request_sha256": (
            "f5f7ce3112563ca79383d8c7502e36df1db78e2d3bc0f32df7b8d09e38ac2c23"
        ),
    }


def test_protocol_only_pid1_source_cannot_claim_runtime_authority() -> None:
    source = (
        WORKSPACE
        / "firecracker_runtime/src/bin/spot_v7_firecracker_protocol_init.rs"
    ).read_text(encoding="utf-8")
    assert "VerifiedReplayReport" not in source
    assert "receipt.verify" not in source
    assert "run_cli" not in source
    assert "precomputed, structurally valid V7 verifier-output" in source


def test_rust_and_python_reject_structure_preserving_mutations_identically(
    tmp_path: Path,
) -> None:
    request = SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=bytes([1]) * 32,
        runtime_manifest_sha256=bytes([2]) * 32,
        machine_config_sha256=bytes([3]) * 32,
        input_drive_sha256=bytes([4]) * 32,
        settlement_intent_sha256=bytes([5]) * 32,
    )
    payload = _read_golden_payload()
    output = build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=bytes([4]) * 32,
        payload=payload,
    )

    request_magic = bytearray(request.encode())
    request_magic[0] ^= 1
    output_commit = bytearray(output)
    output_commit[-1] ^= 1
    payload_magic = bytearray(payload)
    payload_magic[0] ^= 1
    plan_hash = bytearray(payload)
    plan_hash[-1] ^= 1

    python_codes = {
        "output_commit": _reject_code(
            lambda: validate_exact_committed_output_v1(bytes(output_commit), request)
        ),
        "request_magic": _reject_code(
            lambda: decode_exact_request_v1(bytes(request_magic))
        ),
        "v7_output_magic": _reject_code(
            lambda: decode_structural_v7_verifier_payload_v1(bytes(payload_magic))
        ),
        "v7_plan_bytes_sha256": _reject_code(
            lambda: decode_structural_v7_verifier_payload_v1(bytes(plan_hash))
        ),
    }
    rust_codes = _run_rust_binary(tmp_path, RUST_NEGATIVE_VECTOR_BINARY)

    assert rust_codes == python_codes == {
        "output_commit": "output_commit",
        "request_magic": "request_magic",
        "v7_output_magic": "v7_output_magic",
        "v7_plan_bytes_sha256": "v7_plan_bytes_sha256",
    }


def _run_rust_vector(tmp_path: Path) -> dict[str, str]:
    result = _run_rust_binary(tmp_path, RUST_VECTOR_BINARY)
    assert frozenset(result) == EXPECTED_FIELDS
    assert all(len(item) == 64 for item in result.values())
    return result


def _run_rust_binary(tmp_path: Path, binary: str) -> dict[str, str]:
    cargo = shutil.which("cargo")
    rustc = shutil.which("rustc")
    if cargo is None or rustc is None:
        raise AssertionError("cargo and rustc are required for the Rust parity vector")
    host_home = Path.home()
    isolated_home = tmp_path / "home"
    isolated_home.mkdir(mode=0o700)
    environment = {
        "CARGO_HOME": os.environ.get("CARGO_HOME", str(host_home / ".cargo")),
        "CARGO_NET_OFFLINE": "true",
        "CARGO_TARGET_DIR": str(tmp_path / "cargo-target"),
        "HOME": str(isolated_home),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": os.pathsep.join(
            (
                str(Path(cargo).parent),
                str(Path(rustc).parent),
                "/usr/bin",
                "/bin",
            )
        ),
        "RUSTC": rustc,
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", str(host_home / ".rustup")),
    }
    completed = subprocess.run(
        (
            cargo,
            "run",
            "--manifest-path",
            str(WORKSPACE / "Cargo.toml"),
            "--locked",
            "--offline",
            "--quiet",
            "-p",
            RUST_PACKAGE,
            "--bin",
            binary,
        ),
        cwd=ROOT,
        env=environment,
        capture_output=True,
        check=False,
        timeout=120,
    )
    assert completed.returncode == 0, completed.stderr.decode("utf-8", errors="replace")
    assert completed.stderr == b""
    line = completed.stdout.removesuffix(b"\n")
    assert b"\n" not in line
    parsed: object = json.loads(line)
    assert type(parsed) is dict
    canonical = json.dumps(parsed, sort_keys=True, separators=(",", ":")).encode("ascii")
    assert completed.stdout == canonical + b"\n"
    result: dict[str, str] = {}
    for key in sorted(parsed):
        item = parsed.get(key)
        assert type(key) is str and type(item) is str
        result[key] = item
    return result


def _reject_code(operation: Callable[[], object]) -> str:
    try:
        operation()
    except SpotV7FirecrackerProtocolRejectV1 as error:
        return error.code
    raise AssertionError("mutation unexpectedly accepted")


def _read_golden_payload() -> bytes:
    compact = "".join(
        line.split("//", maxsplit=1)[0].strip()
        for line in GOLDEN_PAYLOAD.read_text(encoding="ascii").splitlines()
    )
    return bytes.fromhex(compact)
