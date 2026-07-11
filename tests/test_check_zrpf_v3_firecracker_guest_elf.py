from __future__ import annotations

import hashlib
import os
import struct
import subprocess
from pathlib import Path

import pytest

from tools import check_zrpf_v3_firecracker_guest_elf as checker

_ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
_PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
_DYNAMIC_ENTRY = struct.Struct("<qQ")

_PT_LOAD = 1
_PT_DYNAMIC = 2
_PT_INTERP = 3
_PT_GNU_STACK = 0x6474E551
_PF_X = 1
_PF_W = 2
_PF_R = 4
_DT_NULL = 0
_DT_NEEDED = 1
_DT_TEXTREL = 22
_DT_FLAGS_1 = 0x6FFFFFFB
_DF_1_PIE = 0x08000000

_HEADER_OFFSET_TYPE = 16
_HEADER_OFFSET_MACHINE = 18
_HEADER_OFFSET_VERSION = 20
_HEADER_OFFSET_ENTRY = 24
_HEADER_OFFSET_PROGRAM_HEADERS = 32
_HEADER_OFFSET_FLAGS = 48
_HEADER_OFFSET_HEADER_SIZE = 52
_HEADER_OFFSET_PROGRAM_HEADER_SIZE = 54
_HEADER_OFFSET_PROGRAM_HEADER_COUNT = 56

REPO_ROOT = Path(__file__).resolve().parents[1]
IMAGE_BUILDER = REPO_ROOT / "tools/build_zrpf_v3_firecracker_guest_images.sh"


def test_valid_static_pie_profile_is_derived_without_authority(tmp_path: Path) -> None:
    raw = _valid_elf()
    validated = checker.validate_guest_elf_bytes(bytes(raw))
    guest = tmp_path / "zrpf-replay-init"
    guest.write_bytes(raw)

    report = checker.build_report(guest)

    assert validated.to_document() == report["profile"]
    assert report["ok"] is True
    assert report["errors"] == []
    assert report["profile"] == {
        "df_1_pie": True,
        "dt_needed_count": 0,
        "dynamic_entry_count": 2,
        "elf_class_bits": 64,
        "endianness": "little",
        "entry_point": 0x401310,
        "file_size_bytes": 0x500,
        "gnu_stack_executable": False,
        "load_segment_count": 3,
        "machine": "x86_64",
        "program_header_count": 5,
        "pt_interp_count": 0,
        "type": "et_dyn",
        "writable_executable_load_count": 0,
    }
    assert all(value is False for value in report["authority"].values())
    with pytest.raises(TypeError):
        checker.ValidatedGuestElfV1()


def test_image_builder_uses_hash_bound_native_checker_without_readelf() -> None:
    raw = IMAGE_BUILDER.read_text(encoding="ascii")

    assert "readelf" not in raw
    assert "check_zrpf_v3_firecracker_guest_elf.py" in raw
    assert _checker_source_sha256() in raw
    assert raw.count('"$guest_elf_checker_binary" --guest-elf') == 2
    assert raw.count("env -i -- LC_ALL=C TZ=UTC") == 2
    assert "--expected-guest-elf-checker-sha256" in raw
    assert "python3 -I" not in raw
    assert "command -v mksquashfs" not in raw
    assert "readonly MKSQUASHFS_BINARY=/usr/bin/mksquashfs" in raw
    assert raw.splitlines().count('  "$MKSQUASHFS_BINARY" \\') == 2


def test_image_builder_rejects_wrong_native_checker_identity_before_execution(
    tmp_path: Path,
) -> None:
    guest = tmp_path / "guest"
    guest.write_bytes(b"guest")
    receipts = tmp_path / "receipts"
    receipts.mkdir()
    native_checker = tmp_path / "native-checker"
    native_checker.write_bytes(b"#!/bin/sh\nexit 0\n")
    native_checker.chmod(0o755)

    completed = subprocess.run(
        [
            IMAGE_BUILDER.as_posix(),
            "--guest-binary",
            guest.as_posix(),
            "--receipt-dir",
            receipts.as_posix(),
            "--output-dir",
            (tmp_path / "output").as_posix(),
            "--expected-guest-sha256",
            hashlib.sha256(b"guest").hexdigest(),
            "--expected-receipt-set-sha256",
            "11" * 32,
            "--expected-mksquashfs-sha256",
            "22" * 32,
            "--guest-elf-checker-binary",
            native_checker.as_posix(),
            "--expected-guest-elf-checker-sha256",
            "00" * 32,
        ],
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin"},
        timeout=10,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: guest ELF checker binary identity mismatch\n"


def test_image_builder_rejects_path_searched_native_checker(tmp_path: Path) -> None:
    guest = tmp_path / "guest"
    guest.write_bytes(b"guest")
    receipts = tmp_path / "receipts"
    receipts.mkdir()
    native_checker = tmp_path / "true"
    native_checker.write_bytes(b"#!/bin/sh\nexit 77\n")
    native_checker.chmod(0o755)

    completed = subprocess.run(
        [
            IMAGE_BUILDER.as_posix(),
            "--guest-binary",
            guest.as_posix(),
            "--receipt-dir",
            receipts.as_posix(),
            "--output-dir",
            (tmp_path / "output").as_posix(),
            "--expected-guest-sha256",
            hashlib.sha256(b"guest").hexdigest(),
            "--expected-receipt-set-sha256",
            "11" * 32,
            "--expected-mksquashfs-sha256",
            "22" * 32,
            "--guest-elf-checker-binary",
            "true",
            "--expected-guest-elf-checker-sha256",
            hashlib.sha256(native_checker.read_bytes()).hexdigest(),
        ],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin"},
        timeout=10,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: guest ELF checker binary rejected\n"


@pytest.mark.parametrize(
    ("raw", "code"),
    [(b"", "guest_elf_input_size_invalid"), (b"\x7fELF", "guest_elf_header_truncated")],
)
def test_empty_and_truncated_input_reject(raw: bytes, code: str) -> None:
    _assert_rejects(raw, code)


@pytest.mark.parametrize(
    ("offset", "replacement", "code"),
    [
        (0, b"NOPE", "guest_elf_magic_invalid"),
        (4, b"\x01", "guest_elf_identity_unsupported"),
        (5, b"\x02", "guest_elf_identity_unsupported"),
        (6, b"\x00", "guest_elf_identity_unsupported"),
        (7, b"\x03", "guest_elf_identity_unsupported"),
    ],
)
def test_header_and_identity_reject(offset: int, replacement: bytes, code: str) -> None:
    raw = bytes(_mutate(_valid_elf(), offset, replacement))

    _assert_rejects(raw, code)


@pytest.mark.parametrize(
    ("offset", "encoding", "code"),
    [
        (_HEADER_OFFSET_TYPE, struct.pack("<H", 2), "guest_elf_machine_profile_invalid"),
        (_HEADER_OFFSET_MACHINE, struct.pack("<H", 3), "guest_elf_machine_profile_invalid"),
        (_HEADER_OFFSET_VERSION, struct.pack("<I", 2), "guest_elf_machine_profile_invalid"),
        (_HEADER_OFFSET_FLAGS, struct.pack("<I", 1), "guest_elf_machine_profile_invalid"),
        (_HEADER_OFFSET_HEADER_SIZE, struct.pack("<H", 63), "guest_elf_header_geometry_invalid"),
        (
            _HEADER_OFFSET_PROGRAM_HEADER_SIZE,
            struct.pack("<H", 64),
            "guest_elf_program_header_size_invalid",
        ),
        (
            _HEADER_OFFSET_PROGRAM_HEADER_COUNT,
            struct.pack("<H", 0),
            "guest_elf_program_header_count_invalid",
        ),
        (
            _HEADER_OFFSET_PROGRAM_HEADER_COUNT,
            struct.pack("<H", 0xFFFF),
            "guest_elf_program_header_count_invalid",
        ),
        (
            _HEADER_OFFSET_PROGRAM_HEADER_COUNT,
            struct.pack("<H", checker.MAX_PROGRAM_HEADERS + 1),
            "guest_elf_program_header_count_invalid",
        ),
        (
            _HEADER_OFFSET_PROGRAM_HEADERS,
            struct.pack("<Q", 0x4F8),
            "guest_elf_program_header_table_invalid",
        ),
    ],
)
def test_header_geometry_rejects(offset: int, encoding: bytes, code: str) -> None:
    _assert_rejects(bytes(_mutate(_valid_elf(), offset, encoding)), code)


def test_segment_outside_file_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 1, _PT_LOAD, _PF_R | _PF_X, 0x4F0, 0x4014F0, 0x20, 0x20, 1)

    _assert_rejects(bytes(raw), "guest_elf_segment_file_range_invalid")


def test_oversized_regular_file_rejects_before_read(tmp_path: Path) -> None:
    guest = tmp_path / "oversized-guest"
    with guest.open("wb") as output:
        output.truncate(checker.MAX_GUEST_ELF_BYTES + 1)

    assert checker.build_report(guest)["errors"] == ["guest_elf_input_rejected"]


def test_invalid_segment_alignment_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 1, _PT_LOAD, _PF_R | _PF_X, 0x300, 0x401300, 0x100, 0x100, 3)

    _assert_rejects(bytes(raw), "guest_elf_segment_alignment_invalid")


def test_load_file_size_larger_than_memory_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 1, _PT_LOAD, _PF_R | _PF_X, 0x300, 0x401300, 0x100, 0x80, 0x100)

    _assert_rejects(bytes(raw), "guest_elf_load_geometry_invalid")


def test_writable_executable_load_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(
        raw,
        1,
        _PT_LOAD,
        _PF_R | _PF_W | _PF_X,
        0x300,
        0x401300,
        0x100,
        0x100,
        0x100,
    )

    _assert_rejects(bytes(raw), "guest_elf_writable_executable_load")


def test_missing_load_segment_rejects() -> None:
    raw = _valid_elf()
    for index in range(3):
        _write_program_header(raw, index, 0, 0, 0, 0, 0, 0, 1)

    _assert_rejects(bytes(raw), "guest_elf_load_segment_missing")


def test_interpreter_segment_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 4, _PT_INTERP, _PF_R, 0x480, 0x402480, 8, 8, 1)

    _assert_rejects(bytes(raw), "guest_elf_interpreter_present")


def test_entrypoint_outside_rx_load_rejects() -> None:
    raw = _valid_elf()
    struct.pack_into("<Q", raw, _HEADER_OFFSET_ENTRY, 0x500000)

    _assert_rejects(bytes(raw), "guest_elf_entrypoint_invalid")


@pytest.mark.parametrize("replacement_type", [0, _PT_LOAD])
def test_missing_dynamic_segment_rejects(replacement_type: int) -> None:
    raw = _valid_elf()
    _write_program_header(raw, 3, replacement_type, _PF_R, 0, 0, 0, 0, 1)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_count_invalid")


def test_duplicate_dynamic_segment_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 4, _PT_DYNAMIC, _PF_R, 0x400, 0x402400, 32, 32, 8)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_count_invalid")


@pytest.mark.parametrize(
    ("offset", "virtual_address", "size"),
    [(0x401, 0x402400, 32), (0x400, 0x402401, 32), (0x400, 0x402400, 24)],
)
def test_dynamic_segment_alignment_rejects(
    offset: int,
    virtual_address: int,
    size: int,
) -> None:
    raw = _valid_elf()
    _write_program_header(
        raw,
        3,
        _PT_DYNAMIC,
        _PF_R | _PF_W,
        offset,
        virtual_address,
        size,
        size,
        8,
    )

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_geometry_invalid")


def test_dynamic_segment_must_be_mapped_by_readable_load() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 3, _PT_DYNAMIC, _PF_R, 0x480, 0x403480, 32, 32, 8)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_mapping_invalid")


def test_dynamic_segment_file_and_virtual_translation_must_match() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 3, _PT_DYNAMIC, _PF_R | _PF_W, 0x480, 0x4024A0, 32, 32, 8)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_mapping_invalid")


def test_dynamic_segment_mapping_must_be_unambiguous() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 0, _PT_LOAD, _PF_R, 0, 0x402000, 0x500, 0x500, 0x1000)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_mapping_invalid")


def test_later_load_cannot_alias_dynamic_virtual_pages() -> None:
    raw = _valid_elf()
    raw.extend(bytes(0x100))
    raw[_HEADER_OFFSET_PROGRAM_HEADER_COUNT : _HEADER_OFFSET_PROGRAM_HEADER_COUNT + 2] = (
        6
    ).to_bytes(2, "little")
    _write_program_header(
        raw,
        5,
        _PT_LOAD,
        _PF_R,
        0x500,
        0x402400,
        0x100,
        0x100,
        0x100,
    )
    _DYNAMIC_ENTRY.pack_into(raw, 0x500, _DT_NEEDED, 1)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_segment_mapping_invalid")


def test_dt_needed_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 0, _DT_NEEDED, 1)

    _assert_rejects(bytes(raw), "guest_elf_needed_dependency_present")


def test_text_relocation_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 0, _DT_TEXTREL, 0)

    _assert_rejects(bytes(raw), "guest_elf_text_relocation_present")


def test_page_level_writable_executable_alias_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(
        raw,
        2,
        _PT_LOAD,
        _PF_R | _PF_W,
        0x400,
        0x401400,
        0x100,
        0x100,
        0x100,
    )

    _assert_rejects(bytes(raw), "guest_elf_executable_writable_page_overlap")


def test_page_rounding_overflow_rejects() -> None:
    raw = _valid_elf()
    raw[_HEADER_OFFSET_PROGRAM_HEADER_COUNT : _HEADER_OFFSET_PROGRAM_HEADER_COUNT + 2] = (
        6
    ).to_bytes(2, "little")
    _write_program_header(
        raw,
        5,
        _PT_LOAD,
        _PF_R | _PF_W,
        0,
        0xFFFFFFFFFFFFF000,
        0,
        0xFFF,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_geometry_invalid")


def test_missing_dt_null_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 1, _DT_FLAGS_1, _DF_1_PIE)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


def test_dt_null_with_nonzero_value_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 1, _DT_NULL, 1)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


def test_nonzero_data_after_dt_null_rejects() -> None:
    raw = _valid_elf(dynamic_entry_count=3)
    _write_dynamic_entry(raw, 2, _DT_FLAGS_1, _DF_1_PIE)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


@pytest.mark.parametrize("flags", [0, 1])
def test_missing_df_1_pie_rejects(flags: int) -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 0, _DT_FLAGS_1, flags)

    _assert_rejects(bytes(raw), "guest_elf_df_1_pie_missing")


def test_duplicate_dt_flags_1_rejects() -> None:
    raw = _valid_elf(dynamic_entry_count=3)
    _write_dynamic_entry(raw, 0, _DT_FLAGS_1, _DF_1_PIE)
    _write_dynamic_entry(raw, 1, _DT_FLAGS_1, _DF_1_PIE)
    _write_dynamic_entry(raw, 2, _DT_NULL, 0)

    _assert_rejects(bytes(raw), "guest_elf_df_1_pie_missing")


@pytest.mark.parametrize("flags", [_PF_R | _PF_X, _PF_R | _PF_W | _PF_X])
def test_executable_gnu_stack_rejects(flags: int) -> None:
    raw = _valid_elf()
    _write_program_header(raw, 4, _PT_GNU_STACK, flags, 0, 0, 0, 0, 1)

    _assert_rejects(bytes(raw), "guest_elf_gnu_stack_invalid")


def test_missing_gnu_stack_rejects() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 4, 0, 0, 0, 0, 0, 0, 1)

    _assert_rejects(bytes(raw), "guest_elf_gnu_stack_invalid")


def test_duplicate_gnu_stack_rejects() -> None:
    raw = _valid_elf()
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 6)
    _write_program_header(raw, 5, _PT_GNU_STACK, _PF_R | _PF_W, 0, 0, 0, 0, 1)

    _assert_rejects(bytes(raw), "guest_elf_gnu_stack_invalid")


def test_safe_reader_rejects_symlink_and_hardlink(tmp_path: Path) -> None:
    guest = tmp_path / "guest"
    guest.write_bytes(_valid_elf())
    symlink = tmp_path / "guest-link"
    symlink.symlink_to(guest)

    assert checker.build_report(symlink)["errors"] == ["guest_elf_input_rejected"]

    hardlink = tmp_path / "guest-hardlink"
    os.link(guest, hardlink)
    assert checker.build_report(guest)["errors"] == ["guest_elf_input_rejected"]


def _valid_elf(*, dynamic_entry_count: int = 2) -> bytearray:
    raw = bytearray(0x500)
    identity = b"\x7fELF\x02\x01\x01" + b"\x00" * 9
    _ELF_HEADER.pack_into(
        raw,
        0,
        identity,
        3,
        62,
        1,
        0x401310,
        _ELF_HEADER.size,
        0,
        0,
        _ELF_HEADER.size,
        _PROGRAM_HEADER.size,
        5,
        0,
        0,
        0,
    )
    _write_program_header(raw, 0, _PT_LOAD, _PF_R, 0, 0x400000, 0x300, 0x300, 0x1000)
    _write_program_header(
        raw,
        1,
        _PT_LOAD,
        _PF_R | _PF_X,
        0x300,
        0x401300,
        0x100,
        0x100,
        0x100,
    )
    _write_program_header(
        raw,
        2,
        _PT_LOAD,
        _PF_R | _PF_W,
        0x400,
        0x402400,
        0x100,
        0x100,
        0x100,
    )
    dynamic_size = dynamic_entry_count * _DYNAMIC_ENTRY.size
    _write_program_header(
        raw,
        3,
        _PT_DYNAMIC,
        _PF_R | _PF_W,
        0x400,
        0x402400,
        dynamic_size,
        dynamic_size,
        8,
    )
    _write_program_header(raw, 4, _PT_GNU_STACK, _PF_R | _PF_W, 0, 0, 0, 0, 1)
    _write_dynamic_entry(raw, 0, _DT_FLAGS_1, _DF_1_PIE)
    _write_dynamic_entry(raw, 1, _DT_NULL, 0)
    for index in range(2, dynamic_entry_count):
        _write_dynamic_entry(raw, index, _DT_NULL, 0)
    return raw


def _write_program_header(
    raw: bytearray,
    index: int,
    segment_type: int,
    flags: int,
    file_offset: int,
    virtual_address: int,
    file_size: int,
    memory_size: int,
    alignment: int,
) -> None:
    _PROGRAM_HEADER.pack_into(
        raw,
        _ELF_HEADER.size + index * _PROGRAM_HEADER.size,
        segment_type,
        flags,
        file_offset,
        virtual_address,
        virtual_address,
        file_size,
        memory_size,
        alignment,
    )


def _write_dynamic_entry(raw: bytearray, index: int, tag: int, value: int) -> None:
    _DYNAMIC_ENTRY.pack_into(raw, 0x400 + index * _DYNAMIC_ENTRY.size, tag, value)


def _mutate(raw: bytearray, offset: int, replacement: bytes) -> bytearray:
    raw[offset : offset + len(replacement)] = replacement
    return raw


def _assert_rejects(raw: bytes, code: str) -> None:
    with pytest.raises(checker.GuestElfError) as error:
        checker.validate_guest_elf_bytes(raw)
    assert error.value.code == code


def _checker_source_sha256() -> str:
    return hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest()
