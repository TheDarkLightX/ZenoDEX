from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
from pathlib import Path

from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
    build_authority_input_manifest_v1,
    decode_exact_authority_input_manifest_v1,
)

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT / "zk/spot_settlement_v7_risc0"
PACKAGE = "zenodex-zrpf-spot-v7-firecracker-runtime"
BINARY = "spot-v7-firecracker-authority-input-vector-v1"

V7_IMAGE_ID = (
    0x01020304,
    0x11121314,
    0x21222324,
    0x31323334,
    0x41424344,
    0x51525354,
    0x61626364,
    0x71727374,
)
V6_IMAGE_ID = (
    0x81828384,
    0x91929394,
    0xA1A2A3A4,
    0xB1B2B3B4,
    0xC1C2C3C4,
    0xD1D2D3D4,
    0xE1E2E3E4,
    0xF1F2F3F4,
)


def test_authority_input_manifest_matches_rust_vector(tmp_path: Path) -> None:
    manifest = build_authority_input_manifest_v1(
        v7_image_id=V7_IMAGE_ID,
        v6_image_id=V6_IMAGE_ID,
        v7_receipt_bytes=b"canonical-v7-succinct-receipt\n",
        guest_input_bytes=b"exact-v7-guest-input\0with-binary",
        v6_receipt_bytes=b"canonical-v6-child-succinct-receipt\n",
    )
    decoded = decode_exact_authority_input_manifest_v1(manifest)
    rust = _run_rust_vector(tmp_path)

    assert decoded.encode() == manifest
    assert rust == {
        "manifest_hex": manifest.hex(),
        "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
        "profile_sha256": hashlib.sha256(
            SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
        ).hexdigest(),
    }
    assert bytes.fromhex(rust["profile_sha256"]) == (
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    )


def test_protocol_only_pid1_remains_receipt_verification_free() -> None:
    source = (
        WORKSPACE
        / "firecracker_runtime/src/bin/spot_v7_firecracker_protocol_init.rs"
    ).read_text(encoding="utf-8")
    assert "derive_governed_spot_v7_authority_payload_v1" not in source
    assert "spot-v7-authority-input.bin" not in source
    assert "precomputed, structurally valid V7 verifier-output" in source


def _run_rust_vector(tmp_path: Path) -> dict[str, str]:
    cargo = shutil.which("cargo")
    rustc = shutil.which("rustc")
    if cargo is None or rustc is None:
        raise AssertionError("cargo and rustc are required")
    home = tmp_path / "home"
    home.mkdir(mode=0o700)
    env = {
        "CARGO_HOME": os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")),
        "CARGO_NET_OFFLINE": "true",
        "CARGO_TARGET_DIR": str(tmp_path / "target"),
        "HOME": str(home),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": os.pathsep.join((str(Path(cargo).parent), str(Path(rustc).parent), "/usr/bin", "/bin")),
        "RISC0_SKIP_BUILD": "1",
        "RUSTC": rustc,
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", str(Path.home() / ".rustup")),
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
            PACKAGE,
            "--bin",
            BINARY,
        ),
        cwd=ROOT,
        env=env,
        capture_output=True,
        check=False,
        timeout=180,
    )
    assert completed.returncode == 0, completed.stderr.decode("utf-8", errors="replace")
    output: dict[str, str] = {}
    for line in completed.stdout.decode("ascii").splitlines():
        key, separator, value = line.partition("=")
        assert separator == "="
        output[key] = value
    assert set(output) == {"manifest_hex", "manifest_sha256", "profile_sha256"}
    return output
