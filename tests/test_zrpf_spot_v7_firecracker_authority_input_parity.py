from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
    SpotV7FirecrackerAuthorityInputRejectV1,
    build_authority_input_manifest_v1,
    decode_exact_authority_input_manifest_v1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
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
# Pairwise-distinct non-palindromic lengths make field order and endianness
# observable instead of allowing a symmetric fixture to pass by coincidence.
V7_RECEIPT_BYTES = 603
GUEST_INPUT_BYTES = 607
V6_RECEIPT_BYTES = 611
V7_RECEIPT = bytes(
    ((index + 8 - 1) % 251) + 1 for index in range(V7_RECEIPT_BYTES)
)
GUEST_INPUT = bytes(
    ((index + 30 - 1) % 251) + 1 for index in range(GUEST_INPUT_BYTES)
)
V6_RECEIPT = bytes(
    ((index + 54 - 1) % 251) + 1 for index in range(V6_RECEIPT_BYTES)
)
CANONICAL_MANIFEST_SHA256 = (
    "228938334def692fb13e58c69c80e632e7291144eec106f338744a842a6d8a39"
)


def test_authority_input_manifest_matches_rust_vector(tmp_path: Path) -> None:
    manifest = _manifest()
    decoded = decode_exact_authority_input_manifest_v1(manifest)
    rust = _run_rust_vector(tmp_path)

    assert decoded.encode() == manifest
    assert hashlib.sha256(manifest).hexdigest() == CANONICAL_MANIFEST_SHA256
    assert rust == {
        "manifest_hex": manifest.hex(),
        "manifest_sha256": CANONICAL_MANIFEST_SHA256,
        "profile_sha256": hashlib.sha256(
            SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
        ).hexdigest(),
    }
    assert bytes.fromhex(rust["profile_sha256"]) == (
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    )


def test_authority_manifest_layout_has_active_distinguishing_witnesses() -> None:
    manifest = _manifest()
    fields = (
        ("magic", 0, 8, b"ZSV7AIM1"),
        ("version", 8, 10, (1).to_bytes(2, "big")),
        ("manifest_bytes", 10, 12, (256).to_bytes(2, "big")),
        ("flags", 12, 16, bytes(4)),
        ("authority_profile", 16, 48, SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1),
        ("runtime_profile", 48, 80, SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1),
        ("v7_image_id", 80, 112, _image_id_bytes(V7_IMAGE_ID)),
        ("v6_image_id", 112, 144, _image_id_bytes(V6_IMAGE_ID)),
        ("v7_receipt_length", 144, 148, V7_RECEIPT_BYTES.to_bytes(4, "big")),
        ("v7_receipt_sha256", 148, 180, hashlib.sha256(V7_RECEIPT).digest()),
        ("guest_input_length", 180, 184, GUEST_INPUT_BYTES.to_bytes(4, "big")),
        ("guest_input_sha256", 184, 216, hashlib.sha256(GUEST_INPUT).digest()),
        ("v6_receipt_length", 216, 220, V6_RECEIPT_BYTES.to_bytes(4, "big")),
        ("v6_receipt_sha256", 220, 252, hashlib.sha256(V6_RECEIPT).digest()),
        ("reserved", 252, 256, bytes(4)),
    )

    cursor = 0
    for name, start, end, expected in fields:
        assert start == cursor, name
        assert manifest[start:end] == expected, name
        cursor = end
    assert cursor == SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1

    for artifact in (V7_RECEIPT, GUEST_INPUT, V6_RECEIPT):
        assert artifact != artifact[::-1]
    for image_id, start in ((V7_IMAGE_ID, 80), (V6_IMAGE_ID, 112)):
        for index, word in enumerate(image_id):
            raw_word = manifest[start + index * 4 : start + (index + 1) * 4]
            assert raw_word == word.to_bytes(4, "little")
            assert raw_word != raw_word[::-1]
    for start in (144, 180, 216):
        assert manifest[start : start + 4] != manifest[start : start + 4][::-1]


def test_every_guarded_header_and_flag_choice_rejects() -> None:
    manifest = _manifest()
    for start, end, code in (
        (0, 8, "authority_manifest_magic"),
        (8, 12, "authority_manifest_version"),
        (16, 48, "authority_manifest_profile"),
        (48, 80, "authority_manifest_runtime_profile"),
    ):
        for offset in range(start, end):
            _assert_reject(_xor_byte(manifest, offset), code)

    for bit in range(32):
        mutated = bytearray(manifest)
        mutated[12:16] = (1 << bit).to_bytes(4, "big")
        _assert_reject(bytes(mutated), "authority_manifest_flags")

    for bit in range(32):
        mutated = bytearray(manifest)
        mutated[252 + bit // 8] = 1 << (bit % 8)
        _assert_reject(bytes(mutated), "authority_manifest_reserved")


def test_every_bound_field_position_changes_identity_or_rejects() -> None:
    manifest = _manifest()
    original_sha256 = hashlib.sha256(manifest).digest()

    for start, end, image_field in (
        (80, 112, "v7_image_id"),
        (112, 144, "v6_image_id"),
    ):
        for offset in range(start, end):
            mutated = _xor_byte(manifest, offset)
            decoded = decode_exact_authority_input_manifest_v1(mutated)
            assert getattr(decoded, image_field) != (
                V7_IMAGE_ID if image_field == "v7_image_id" else V6_IMAGE_ID
            )
            assert hashlib.sha256(mutated).digest() != original_sha256

    for start, length_field, reject_code in (
        (144, "v7_receipt_length", "authority_v7_receipt_length"),
        (180, "guest_input_length", "authority_guest_input_length"),
        (216, "v6_receipt_length", "authority_v6_receipt_length"),
    ):
        for offset in range(start, start + 4):
            mutated = _xor_byte(manifest, offset)
            assert hashlib.sha256(mutated).digest() != original_sha256
            try:
                decoded = decode_exact_authority_input_manifest_v1(mutated)
            except SpotV7FirecrackerAuthorityInputRejectV1 as error:
                assert error.code == reject_code
                continue
            assert getattr(decoded, length_field) != int.from_bytes(
                manifest[start : start + 4], "big"
            )

    for start, end, digest_field in (
        (148, 180, "v7_receipt_sha256"),
        (184, 216, "guest_input_sha256"),
        (220, 252, "v6_receipt_sha256"),
    ):
        for offset in range(start, end):
            mutated = _xor_byte(manifest, offset)
            decoded = decode_exact_authority_input_manifest_v1(mutated)
            assert getattr(decoded, digest_field) != manifest[start:end]
            assert hashlib.sha256(mutated).digest() != original_sha256


def test_all_multibyte_fields_actively_distinguish_byte_order() -> None:
    manifest = _manifest()
    for start in (8, 10):
        _assert_reject(
            _reverse_field(manifest, start, 2), "authority_manifest_version"
        )
    for start, code in (
        (144, "authority_v7_receipt_length"),
        (180, "authority_guest_input_length"),
        (216, "authority_v6_receipt_length"),
    ):
        _assert_reject(_reverse_field(manifest, start, 4), code)

    for image_id, start, field_name in (
        (V7_IMAGE_ID, 80, "v7_image_id"),
        (V6_IMAGE_ID, 112, "v6_image_id"),
    ):
        for index, _word in enumerate(image_id):
            word_start = start + index * 4
            mutated = _reverse_field(manifest, word_start, 4)
            decoded = decode_exact_authority_input_manifest_v1(mutated)
            assert getattr(decoded, field_name) != image_id
            assert hashlib.sha256(mutated).hexdigest() != CANONICAL_MANIFEST_SHA256

    for start, end, field_name in (
        (148, 180, "v7_receipt_sha256"),
        (184, 216, "guest_input_sha256"),
        (220, 252, "v6_receipt_sha256"),
    ):
        mutated = bytearray(manifest)
        mutated[start:end] = mutated[start:end][::-1]
        decoded = decode_exact_authority_input_manifest_v1(bytes(mutated))
        assert getattr(decoded, field_name) == manifest[start:end][::-1]
        assert hashlib.sha256(mutated).hexdigest() != CANONICAL_MANIFEST_SHA256


def test_protocol_only_pid1_remains_receipt_verification_free() -> None:
    source = (
        WORKSPACE
        / "firecracker_runtime/src/bin/spot_v7_firecracker_protocol_init.rs"
    ).read_text(encoding="utf-8")
    assert "derive_governed_spot_v7_authority_payload_v1" not in source
    assert "spot-v7-authority-input.bin" not in source
    assert "precomputed, structurally valid V7 verifier-output" in source


def _manifest() -> bytes:
    return build_authority_input_manifest_v1(
        v7_image_id=V7_IMAGE_ID,
        v6_image_id=V6_IMAGE_ID,
        v7_receipt_bytes=V7_RECEIPT,
        guest_input_bytes=GUEST_INPUT,
        v6_receipt_bytes=V6_RECEIPT,
    )


def _image_id_bytes(image_id: tuple[int, ...]) -> bytes:
    return b"".join(word.to_bytes(4, "little") for word in image_id)


def _xor_byte(raw: bytes, offset: int) -> bytes:
    mutated = bytearray(raw)
    mutated[offset] ^= 1
    return bytes(mutated)


def _reverse_field(raw: bytes, start: int, length: int) -> bytes:
    mutated = bytearray(raw)
    mutated[start : start + length] = mutated[start : start + length][::-1]
    return bytes(mutated)


def _assert_reject(raw: bytes, code: str) -> None:
    with pytest.raises(SpotV7FirecrackerAuthorityInputRejectV1) as caught:
        decode_exact_authority_input_manifest_v1(raw)
    assert caught.value.code == code


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
        "PATH": os.pathsep.join(
            (str(Path(cargo).parent), str(Path(rustc).parent), "/usr/bin", "/bin")
        ),
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
