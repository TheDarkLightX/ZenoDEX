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
_RELA_ENTRY = struct.Struct("<QQq")

_PT_LOAD = 1
_PT_DYNAMIC = 2
_PT_INTERP = 3
_PT_PHDR = 6
_PT_GNU_STACK = 0x6474E551
_PF_X = 1
_PF_W = 2
_PF_R = 4
_DT_NULL = 0
_DT_NEEDED = 1
_DT_SYMTAB = 6
_DT_RELA = 7
_DT_RELASZ = 8
_DT_RELAENT = 9
_DT_SYMENT = 11
_DT_REL = 17
_DT_TEXTREL = 22
_DT_FLAGS_1 = 0x6FFFFFFB
_DT_RELACOUNT = 0x6FFFFFF9
_DT_VERSYM = 0x6FFFFFF0
_DF_1_PIE = 0x08000000
_R_X86_64_RELATIVE = 8
_R_X86_64_IRELATIVE = 37

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
        "dynamic_entry_count": 8,
        "elf_class_bits": 64,
        "endianness": "little",
        "entry_point": 0x401310,
        "file_size_bytes": 0x500,
        "gnu_stack_executable": False,
        "load_segment_count": 3,
        "machine": "x86_64",
        "program_header_count": 7,
        "pt_interp_count": 0,
        "rela_entry_count": 2,
        "relative_relocation_count": 1,
        "irelative_relocation_count": 1,
        "type": "et_dyn",
        "writable_executable_load_count": 0,
    }
    assert all(value is False for value in report["authority"].values())
    assert report["validation_scope"] == "bounded_elf64_pt_load_and_relocation_metadata"
    assert report["authority"]["complete_elf_loader_semantics_verified"] is False
    assert report["authority"]["guest_boot_verified"] is False
    with pytest.raises(TypeError):
        checker.ValidatedGuestElfV1()


def test_image_builder_uses_hash_bound_native_checker_without_readelf() -> None:
    raw = IMAGE_BUILDER.read_text(encoding="ascii")

    assert "readelf" not in raw
    assert "check_zrpf_v3_firecracker_guest_elf.py" in raw
    assert _checker_source_sha256() in raw
    assert raw.count('"$captured_checker" --guest-elf "$captured_guest"') == 2
    assert raw.count("env -i -- LC_ALL=C TZ=UTC") == 2
    assert "--expected-guest-elf-checker-sha256" in raw
    assert "python3 -I" not in raw
    assert "command -v mksquashfs" not in raw
    assert "readonly MKSQUASHFS_BINARY=/usr/bin/mksquashfs" in raw
    assert raw.splitlines().count('  "$MKSQUASHFS_BINARY" \\') == 2
    assert raw.startswith("#!/bin/bash -p\n")
    assert "error: privileged bash mode required" in raw
    assert '"captured_guest_sha256=$expected_guest_sha256"' in raw
    assert '"captured_receipt_set_sha256=$after_receipt_set"' in raw
    assert '"guest_sha256=$expected_guest_sha256"' not in raw


@pytest.mark.parametrize(
    "arguments",
    [
        ["--guest-binary"],
        ["--guest-binary", "/tmp/a", "--guest-binary", "/tmp/b"],
        ["--unknown", "value"],
    ],
)
def test_image_builder_rejects_noncanonical_cli(arguments: list[str]) -> None:
    completed = subprocess.run(
        [IMAGE_BUILDER.as_posix(), *arguments],
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin"},
        timeout=10,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: unknown, duplicate, or incomplete argument\n"


def test_image_builder_rejects_bash_invocation_without_privileged_mode() -> None:
    completed = subprocess.run(
        ["/bin/bash", IMAGE_BUILDER.as_posix()],
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin"},
        timeout=10,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: privileged bash mode required\n"


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
            _mksquashfs_sha256(),
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
    assert completed.stderr == b"error: guest ELF checker identity mismatch\n"


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


def test_image_builder_rejects_find_expression_receipt_path_without_side_effects(
    tmp_path: Path,
) -> None:
    guest = tmp_path / "guest"
    guest.write_bytes(b"guest")
    native_checker = tmp_path / "native-checker"
    native_checker.write_bytes(b"#!/bin/sh\nexit 0\n")
    native_checker.chmod(0o755)
    hostile_directory = tmp_path / "-delete"
    hostile_directory.mkdir()
    sentinel = tmp_path / "sentinel"
    sentinel.write_bytes(b"must survive")

    completed = subprocess.run(
        [
            IMAGE_BUILDER.as_posix(),
            "--guest-binary",
            guest.as_posix(),
            "--receipt-dir",
            hostile_directory.name,
            "--output-dir",
            (tmp_path / "output").as_posix(),
            "--expected-guest-sha256",
            hashlib.sha256(b"guest").hexdigest(),
            "--expected-receipt-set-sha256",
            "11" * 32,
            "--expected-mksquashfs-sha256",
            _mksquashfs_sha256(),
            "--guest-elf-checker-binary",
            native_checker.as_posix(),
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
    assert completed.stderr == b"error: receipt directory rejected\n"
    assert sentinel.read_bytes() == b"must survive"
    assert hostile_directory.is_dir()
    assert not (tmp_path / "output").exists()


@pytest.mark.parametrize(
    "variable",
    ["BASH_ENV", "LD_AUDIT", "LD_LIBRARY_PATH", "LD_PRELOAD", "SOURCE_DATE_EPOCH"],
)
def test_image_builder_rejects_hostile_build_environment(variable: str) -> None:
    completed = subprocess.run(
        [IMAGE_BUILDER.as_posix()],
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin", variable: "hostile"},
        timeout=10,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr.endswith(b"error: hostile build environment rejected\n")


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


def test_load_alignment_is_exactly_one_governed_page() -> None:
    raw = _valid_elf()
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
        0x1000,
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


def test_entrypoint_must_be_file_backed_rx() -> None:
    raw = _valid_elf()
    struct.pack_into("<Q", raw, _HEADER_OFFSET_ENTRY, 0x401390)
    _write_program_header(
        raw,
        1,
        _PT_LOAD,
        _PF_R | _PF_X,
        0x300,
        0x401300,
        0x80,
        0x100,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_entrypoint_invalid")


def test_program_header_table_must_be_mapped_by_zero_based_load() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 0, _PT_LOAD, _PF_R, 0, 0, 0x100, 0x100, 0x1000)

    _assert_rejects(bytes(raw), "guest_elf_program_headers_unmapped")


def test_program_header_segment_must_be_present() -> None:
    raw = _valid_elf()
    _write_program_header(raw, 5, 0, 0, 0, 0, 0, 0, 0)

    _assert_rejects(bytes(raw), "guest_elf_program_header_segment_invalid")


def test_program_header_segment_must_be_unique() -> None:
    raw = _valid_elf()
    table_size = 7 * _PROGRAM_HEADER.size
    _write_program_header(
        raw,
        6,
        _PT_PHDR,
        _PF_R,
        _ELF_HEADER.size,
        _ELF_HEADER.size,
        table_size,
        table_size,
        8,
    )

    _assert_rejects(bytes(raw), "guest_elf_program_header_segment_invalid")


def test_program_header_segment_must_be_canonical() -> None:
    raw = _valid_elf()
    table_size = 7 * _PROGRAM_HEADER.size
    _write_program_header(
        raw,
        5,
        _PT_PHDR,
        _PF_R,
        _ELF_HEADER.size,
        _ELF_HEADER.size,
        table_size,
        table_size,
        16,
    )

    _assert_rejects(bytes(raw), "guest_elf_program_header_segment_invalid")


@pytest.mark.parametrize("replacement_type", [0, 4])
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

    _assert_rejects(bytes(raw), "guest_elf_load_bias_invalid")


def test_later_load_cannot_alias_dynamic_virtual_pages() -> None:
    raw = _valid_elf()
    raw.extend(bytes(0x100))
    raw[_HEADER_OFFSET_PROGRAM_HEADER_COUNT : _HEADER_OFFSET_PROGRAM_HEADER_COUNT + 2] = (
        7
    ).to_bytes(2, "little")
    _write_program_header(
        raw,
        6,
        _PT_LOAD,
        _PF_R,
        0x500,
        0x402500,
        0x100,
        0x100,
        0x1000,
    )
    _DYNAMIC_ENTRY.pack_into(raw, 0x500, _DT_NEEDED, 1)

    _assert_rejects(bytes(raw), "guest_elf_load_mapping_invalid")


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
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_executable_writable_page_overlap")


def test_page_rounding_overflow_rejects() -> None:
    raw = _valid_elf()
    raw[_HEADER_OFFSET_PROGRAM_HEADER_COUNT : _HEADER_OFFSET_PROGRAM_HEADER_COUNT + 2] = (
        7
    ).to_bytes(2, "little")
    _write_program_header(
        raw,
        6,
        _PT_LOAD,
        _PF_R | _PF_W,
        0,
        0xFFFFFFFFFFFFF000,
        0,
        0xFFF,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_geometry_invalid")


def test_read_only_page_rounding_overflow_rejects() -> None:
    raw = _valid_elf()
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 7)
    _write_program_header(
        raw,
        6,
        _PT_LOAD,
        _PF_R,
        0,
        0xFFFFFFFFFFFFF000,
        0,
        0x1000,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_geometry_invalid")


def test_load_segments_must_be_in_ascending_virtual_page_order() -> None:
    raw = _valid_elf()
    _write_program_header(
        raw,
        2,
        _PT_LOAD,
        _PF_R | _PF_W,
        0x400,
        0x300400,
        0x100,
        0x100,
        0x1000,
    )
    _write_program_header(
        raw,
        3,
        _PT_DYNAMIC,
        _PF_R | _PF_W,
        0x400,
        0x300400,
        8 * _DYNAMIC_ENTRY.size,
        8 * _DYNAMIC_ENTRY.size,
        8,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_mapping_invalid")


def test_read_only_load_cannot_alias_executable_virtual_page() -> None:
    raw = _valid_elf()
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 7)
    _write_program_header(
        raw,
        6,
        _PT_LOAD,
        _PF_R,
        0x300,
        0x401300,
        0x100,
        0x1000,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_mapping_invalid")


def test_load_virtual_end_above_governed_profile_rejects() -> None:
    raw = _valid_elf()
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 7)
    _write_program_header(
        raw,
        6,
        _PT_LOAD,
        _PF_R,
        0,
        checker.MAX_LOAD_VIRTUAL_END,
        0,
        0x1000,
        0x1000,
    )

    _assert_rejects(bytes(raw), "guest_elf_load_geometry_invalid")


def test_load_bias_source_is_unique_first_and_zero_based() -> None:
    raw = _valid_elf()
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 7)
    _write_program_header(raw, 6, _PT_LOAD, _PF_R, 0, 0x500000, 1, 1, 0x1000)

    _assert_rejects(bytes(raw), "guest_elf_load_bias_invalid")


def test_relocation_table_virtual_pointer_must_map_to_file_bytes() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 1, _DT_RELA, 0x500000)

    _assert_rejects(bytes(raw), "guest_elf_relocation_table_mapping_invalid")


def test_relocation_table_must_be_read_only_file_backed_memory() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 1, _DT_RELA, 0x402400)

    _assert_rejects(bytes(raw), "guest_elf_relocation_table_mapping_invalid")


@pytest.mark.parametrize("tag", [_DT_REL, _DT_VERSYM])
def test_alternate_relocation_and_version_tables_reject(tag: int) -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 6, tag, 0x200)

    _assert_rejects(bytes(raw), "guest_elf_unsupported_relocation_table")


def test_relocation_target_must_be_unique_aligned_writable_memory() -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 0, 0x401310, _R_X86_64_RELATIVE, 0x401310)

    _assert_rejects(bytes(raw), "guest_elf_relocation_target_invalid")


def test_relocation_target_cannot_overlap_dynamic_table() -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 0, 0x402400, _R_X86_64_RELATIVE, 0x401310)

    _assert_rejects(bytes(raw), "guest_elf_relocation_target_invalid")


@pytest.mark.parametrize(
    ("info", "code"),
    [
        (1, "guest_elf_relocation_type_unsupported"),
        ((1 << 32) | _R_X86_64_RELATIVE, "guest_elf_relocation_symbol_invalid"),
    ],
)
def test_relocation_type_and_symbol_index_are_governed(info: int, code: str) -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 0, 0x402480, info, 0x401310)

    _assert_rejects(bytes(raw), code)


@pytest.mark.parametrize(
    ("index", "relocation_type"),
    [(0, _R_X86_64_IRELATIVE), (1, _R_X86_64_RELATIVE)],
)
def test_relocation_types_must_follow_relacount_order(
    index: int,
    relocation_type: int,
) -> None:
    raw = _valid_elf()
    target = 0x402480 + index * 8
    addend = 0x401310 + index * 0x10
    _write_rela_entry(raw, index, target, relocation_type, addend)

    _assert_rejects(bytes(raw), "guest_elf_relocation_order_invalid")


def test_relative_relocation_addend_must_resolve_inside_image() -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 0, 0x402480, _R_X86_64_RELATIVE, 0x500000)

    _assert_rejects(bytes(raw), "guest_elf_relative_addend_invalid")


def test_irelative_resolver_must_be_executable_image_memory() -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 1, 0x402488, _R_X86_64_IRELATIVE, 0x402400)

    _assert_rejects(bytes(raw), "guest_elf_irelative_resolver_invalid")


def test_relocation_targets_must_be_unique() -> None:
    raw = _valid_elf()
    _write_rela_entry(raw, 1, 0x402480, _R_X86_64_IRELATIVE, 0x401320)

    _assert_rejects(bytes(raw), "guest_elf_relocation_target_duplicate")


def test_relocation_metadata_is_complete_and_unique() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 2, _DT_RELA, 0x200)

    _assert_rejects(bytes(raw), "guest_elf_relocation_metadata_invalid")


def test_symbol_zero_must_be_canonical_and_read_only_file_backed() -> None:
    raw = _valid_elf()
    raw[0x1D0] = 1

    _assert_rejects(bytes(raw), "guest_elf_symbol_zero_invalid")


def test_symbol_zero_table_must_be_read_only_file_backed() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 5, _DT_SYMTAB, 0x402400)

    _assert_rejects(bytes(raw), "guest_elf_symbol_table_mapping_invalid")


def test_missing_dt_null_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 7, _DT_FLAGS_1, _DF_1_PIE)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


def test_dt_null_with_nonzero_value_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 7, _DT_NULL, 1)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


def test_nonzero_data_after_dt_null_rejects() -> None:
    raw = _valid_elf(dynamic_entry_count=9)
    _write_dynamic_entry(raw, 8, _DT_FLAGS_1, _DF_1_PIE)

    _assert_rejects(bytes(raw), "guest_elf_dynamic_terminator_invalid")


@pytest.mark.parametrize("flags", [0, 1])
def test_missing_df_1_pie_rejects(flags: int) -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 0, _DT_FLAGS_1, flags)

    _assert_rejects(bytes(raw), "guest_elf_df_1_pie_missing")


def test_duplicate_dt_flags_1_rejects() -> None:
    raw = _valid_elf()
    _write_dynamic_entry(raw, 1, _DT_FLAGS_1, _DF_1_PIE)

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
    struct.pack_into("<H", raw, _HEADER_OFFSET_PROGRAM_HEADER_COUNT, 7)
    _write_program_header(raw, 6, _PT_GNU_STACK, _PF_R | _PF_W, 0, 0, 0, 0, 1)

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


def _valid_elf(*, dynamic_entry_count: int = 8) -> bytearray:
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
        7,
        0,
        0,
        0,
    )
    _write_program_header(raw, 0, _PT_LOAD, _PF_R, 0, 0, 0x300, 0x300, 0x1000)
    _write_program_header(
        raw,
        1,
        _PT_LOAD,
        _PF_R | _PF_X,
        0x300,
        0x401300,
        0x100,
        0x100,
        0x1000,
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
        0x1000,
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
    program_header_table_size = 7 * _PROGRAM_HEADER.size
    _write_program_header(
        raw,
        5,
        _PT_PHDR,
        _PF_R,
        _ELF_HEADER.size,
        _ELF_HEADER.size,
        program_header_table_size,
        program_header_table_size,
        8,
    )
    _write_program_header(raw, 6, 0, 0, 0, 0, 0, 0, 0)
    _write_dynamic_entry(raw, 0, _DT_FLAGS_1, _DF_1_PIE)
    _write_dynamic_entry(raw, 1, _DT_RELA, 0x200)
    _write_dynamic_entry(raw, 2, _DT_RELASZ, 2 * _RELA_ENTRY.size)
    _write_dynamic_entry(raw, 3, _DT_RELAENT, _RELA_ENTRY.size)
    _write_dynamic_entry(raw, 4, _DT_RELACOUNT, 1)
    _write_dynamic_entry(raw, 5, _DT_SYMTAB, 0x1D0)
    _write_dynamic_entry(raw, 6, _DT_SYMENT, 24)
    _write_dynamic_entry(raw, 7, _DT_NULL, 0)
    for index in range(8, dynamic_entry_count):
        _write_dynamic_entry(raw, index, _DT_NULL, 0)
    _write_rela_entry(raw, 0, 0x402480, _R_X86_64_RELATIVE, 0x401310)
    _write_rela_entry(raw, 1, 0x402488, _R_X86_64_IRELATIVE, 0x401320)
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


def _write_rela_entry(
    raw: bytearray,
    index: int,
    target: int,
    info: int,
    addend: int,
) -> None:
    _RELA_ENTRY.pack_into(raw, 0x200 + index * _RELA_ENTRY.size, target, info, addend)


def _mutate(raw: bytearray, offset: int, replacement: bytes) -> bytearray:
    raw[offset : offset + len(replacement)] = replacement
    return raw


def _assert_rejects(raw: bytes, code: str) -> None:
    with pytest.raises(checker.GuestElfError) as error:
        checker.validate_guest_elf_bytes(raw)
    assert error.value.code == code


def _checker_source_sha256() -> str:
    return hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest()


def _mksquashfs_sha256() -> str:
    return hashlib.sha256(Path("/usr/bin/mksquashfs").read_bytes()).hexdigest()
