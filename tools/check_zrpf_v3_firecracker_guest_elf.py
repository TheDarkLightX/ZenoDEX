#!/usr/bin/env python3
"""Validate the bounded ELF metadata required by the ZRPF guest profile."""

from __future__ import annotations

import argparse
import importlib
import json
import struct
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""

runtime = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")

MAX_GUEST_ELF_BYTES = 16 * 1024 * 1024
MAX_PROGRAM_HEADERS = 128
MAX_DYNAMIC_ENTRIES = 4_096
REPORT_SCHEMA = "zenodex/zrpf_firecracker_guest_elf_check/v1"

_ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
_PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
_DYNAMIC_ENTRY = struct.Struct("<qQ")

_ET_DYN = 3
_EM_X86_64 = 62
_PN_XNUM = 0xFFFF

_PT_LOAD = 1
_PT_DYNAMIC = 2
_PT_INTERP = 3
_PT_GNU_STACK = 0x6474E551

_PF_X = 1
_PF_W = 2
_PF_R = 4

_DT_NULL = 0
_DT_NEEDED = 1
_DT_FLAGS_1 = 0x6FFFFFFB
_DF_1_PIE = 0x08000000


class GuestElfError(ValueError):
    """Stable fail-closed error at the guest ELF metadata boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True, init=False)
class ValidatedGuestElfV1:
    """Metadata derived only after the complete bounded ELF check succeeds."""

    dynamic_entry_count: int
    entry_point: int
    file_size_bytes: int
    load_segment_count: int
    program_header_count: int

    def __init__(self) -> None:
        raise TypeError("validated guest ELF values require parser construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        dynamic_entry_count: int,
        entry_point: int,
        file_size_bytes: int,
        load_segment_count: int,
        program_header_count: int,
    ) -> ValidatedGuestElfV1:
        value = object.__new__(cls)
        object.__setattr__(value, "dynamic_entry_count", dynamic_entry_count)
        object.__setattr__(value, "entry_point", entry_point)
        object.__setattr__(value, "file_size_bytes", file_size_bytes)
        object.__setattr__(value, "load_segment_count", load_segment_count)
        object.__setattr__(value, "program_header_count", program_header_count)
        return value

    def to_document(self) -> dict[str, Any]:
        return {
            "df_1_pie": True,
            "dt_needed_count": 0,
            "dynamic_entry_count": self.dynamic_entry_count,
            "elf_class_bits": 64,
            "endianness": "little",
            "entry_point": self.entry_point,
            "file_size_bytes": self.file_size_bytes,
            "gnu_stack_executable": False,
            "load_segment_count": self.load_segment_count,
            "machine": "x86_64",
            "program_header_count": self.program_header_count,
            "pt_interp_count": 0,
            "type": "et_dyn",
            "writable_executable_load_count": 0,
        }


@dataclass(frozen=True, slots=True)
class _ProgramHeaderV1:
    segment_type: int
    flags: int
    file_offset: int
    virtual_address: int
    file_size: int
    memory_size: int
    alignment: int


def validate_guest_elf_bytes(raw: bytes) -> ValidatedGuestElfV1:
    """Validate one exact ELF64 static-PIE metadata profile."""

    if type(raw) is not bytes or not 0 < len(raw) <= MAX_GUEST_ELF_BYTES:
        raise GuestElfError("guest_elf_input_size_invalid")
    header = _parse_header(raw)
    entry_point = header[4]
    program_header_offset = header[5]
    program_header_size = header[9]
    program_header_count = header[10]
    _validate_header_geometry(
        raw,
        program_header_offset=program_header_offset,
        program_header_size=program_header_size,
        program_header_count=program_header_count,
    )
    program_headers = _parse_program_headers(
        raw,
        table_offset=program_header_offset,
        count=program_header_count,
    )
    load_segments = _validate_segments(raw, program_headers)
    _validate_entry_point(entry_point, load_segments)
    dynamic_segment = _require_single_segment(program_headers, _PT_DYNAMIC)
    _validate_dynamic_mapping(dynamic_segment, load_segments)
    dynamic_entry_count = _validate_dynamic_entries(raw, dynamic_segment)
    _validate_gnu_stack(program_headers)
    return ValidatedGuestElfV1._from_validated(
        dynamic_entry_count=dynamic_entry_count,
        entry_point=entry_point,
        file_size_bytes=len(raw),
        load_segment_count=len(load_segments),
        program_header_count=program_header_count,
    )


def load_guest_elf(path: Path) -> ValidatedGuestElfV1:
    """Read one stable regular file and validate its ELF metadata."""

    try:
        raw = runtime.read_bounded_regular(path, maximum=MAX_GUEST_ELF_BYTES)
    except (OSError, ValueError) as exc:
        raise GuestElfError("guest_elf_input_rejected") from exc
    return validate_guest_elf_bytes(raw)


def build_report(path: Path) -> dict[str, Any]:
    errors: list[str] = []
    profile: dict[str, Any] | None = None
    try:
        profile = load_guest_elf(path).to_document()
    except GuestElfError as exc:
        errors.append(exc.code)
    return {
        "authority": {
            "complete_build_input_closure_verified": False,
            "guest_source_to_binary_verified": False,
            "production_authority": False,
            "release_authority": False,
        },
        "errors": errors,
        "ok": not errors,
        "profile": profile,
        "schema": REPORT_SCHEMA,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--guest-elf", type=Path, required=True)
    arguments = parser.parse_args(argv)
    report = build_report(arguments.guest_elf)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _parse_header(raw: bytes) -> tuple[Any, ...]:
    if len(raw) < _ELF_HEADER.size:
        raise GuestElfError("guest_elf_header_truncated")
    header = _ELF_HEADER.unpack_from(raw)
    identity = header[0]
    if identity[:4] != b"\x7fELF":
        raise GuestElfError("guest_elf_magic_invalid")
    if (
        identity[4] != 2
        or identity[5] != 1
        or identity[6] != 1
        or identity[7] != 0
        or identity[8] != 0
        or any(identity[9:])
    ):
        raise GuestElfError("guest_elf_identity_unsupported")
    elf_type, machine, version = header[1:4]
    if elf_type != _ET_DYN or machine != _EM_X86_64 or version != 1 or header[7] != 0:
        raise GuestElfError("guest_elf_machine_profile_invalid")
    if header[8] != _ELF_HEADER.size:
        raise GuestElfError("guest_elf_header_geometry_invalid")
    return header


def _validate_header_geometry(
    raw: bytes,
    *,
    program_header_offset: int,
    program_header_size: int,
    program_header_count: int,
) -> None:
    if program_header_size != _PROGRAM_HEADER.size:
        raise GuestElfError("guest_elf_program_header_size_invalid")
    if (
        program_header_count == 0
        or program_header_count == _PN_XNUM
        or program_header_count > MAX_PROGRAM_HEADERS
    ):
        raise GuestElfError("guest_elf_program_header_count_invalid")
    table_size = program_header_size * program_header_count
    if (
        program_header_offset < _ELF_HEADER.size
        or program_header_offset % 8 != 0
        or not _range_within(program_header_offset, table_size, len(raw))
    ):
        raise GuestElfError("guest_elf_program_header_table_invalid")


def _parse_program_headers(
    raw: bytes,
    *,
    table_offset: int,
    count: int,
) -> tuple[_ProgramHeaderV1, ...]:
    output: list[_ProgramHeaderV1] = []
    for index in range(count):
        values = _PROGRAM_HEADER.unpack_from(raw, table_offset + index * _PROGRAM_HEADER.size)
        output.append(
            _ProgramHeaderV1(
                segment_type=values[0],
                flags=values[1],
                file_offset=values[2],
                virtual_address=values[3],
                file_size=values[5],
                memory_size=values[6],
                alignment=values[7],
            )
        )
    return tuple(output)


def _validate_segments(
    raw: bytes,
    program_headers: tuple[_ProgramHeaderV1, ...],
) -> tuple[_ProgramHeaderV1, ...]:
    load_segments: list[_ProgramHeaderV1] = []
    for segment in program_headers:
        if segment.file_size and not _range_within(
            segment.file_offset,
            segment.file_size,
            len(raw),
        ):
            raise GuestElfError("guest_elf_segment_file_range_invalid")
        if segment.alignment not in (0, 1) and not _is_power_of_two(segment.alignment):
            raise GuestElfError("guest_elf_segment_alignment_invalid")
        if segment.segment_type == _PT_INTERP:
            raise GuestElfError("guest_elf_interpreter_present")
        if segment.segment_type != _PT_LOAD:
            continue
        if segment.file_size > segment.memory_size:
            raise GuestElfError("guest_elf_load_geometry_invalid")
        if segment.alignment > 1 and (
            segment.file_offset % segment.alignment != segment.virtual_address % segment.alignment
        ):
            raise GuestElfError("guest_elf_load_geometry_invalid")
        if segment.flags & _PF_W and segment.flags & _PF_X:
            raise GuestElfError("guest_elf_writable_executable_load")
        load_segments.append(segment)
    if not load_segments:
        raise GuestElfError("guest_elf_load_segment_missing")
    return tuple(load_segments)


def _validate_entry_point(
    entry_point: int,
    load_segments: tuple[_ProgramHeaderV1, ...],
) -> None:
    for segment in load_segments:
        if segment.flags & (_PF_R | _PF_X) != (_PF_R | _PF_X):
            continue
        if _address_within(entry_point, segment.virtual_address, segment.memory_size):
            return
    raise GuestElfError("guest_elf_entrypoint_invalid")


def _require_single_segment(
    program_headers: tuple[_ProgramHeaderV1, ...],
    segment_type: int,
) -> _ProgramHeaderV1:
    matches = tuple(segment for segment in program_headers if segment.segment_type == segment_type)
    if len(matches) != 1:
        raise GuestElfError("guest_elf_dynamic_segment_count_invalid")
    return matches[0]


def _validate_dynamic_mapping(
    dynamic: _ProgramHeaderV1,
    load_segments: tuple[_ProgramHeaderV1, ...],
) -> None:
    if (
        dynamic.file_size == 0
        or dynamic.file_size > MAX_DYNAMIC_ENTRIES * _DYNAMIC_ENTRY.size
        or dynamic.file_size % _DYNAMIC_ENTRY.size != 0
        or dynamic.file_offset % 8 != 0
        or dynamic.virtual_address % 8 != 0
        or dynamic.file_size > dynamic.memory_size
    ):
        raise GuestElfError("guest_elf_dynamic_segment_geometry_invalid")
    for load in load_segments:
        if not load.flags & _PF_R:
            continue
        if _contained_file_range(dynamic, load) and _contained_memory_range(dynamic, load):
            return
    raise GuestElfError("guest_elf_dynamic_segment_mapping_invalid")


def _validate_dynamic_entries(raw: bytes, dynamic: _ProgramHeaderV1) -> int:
    entry_count = dynamic.file_size // _DYNAMIC_ENTRY.size
    saw_null = False
    flags_1_values: list[int] = []
    for index in range(entry_count):
        tag, value = _DYNAMIC_ENTRY.unpack_from(
            raw,
            dynamic.file_offset + index * _DYNAMIC_ENTRY.size,
        )
        if tag == _DT_NEEDED:
            raise GuestElfError("guest_elf_needed_dependency_present")
        if saw_null:
            if tag != _DT_NULL or value != 0:
                raise GuestElfError("guest_elf_dynamic_terminator_invalid")
            continue
        if tag == _DT_NULL:
            if value != 0:
                raise GuestElfError("guest_elf_dynamic_terminator_invalid")
            saw_null = True
        elif tag == _DT_FLAGS_1:
            flags_1_values.append(value)
    if not saw_null:
        raise GuestElfError("guest_elf_dynamic_terminator_invalid")
    if len(flags_1_values) != 1 or not flags_1_values[0] & _DF_1_PIE:
        raise GuestElfError("guest_elf_df_1_pie_missing")
    return entry_count


def _validate_gnu_stack(program_headers: tuple[_ProgramHeaderV1, ...]) -> None:
    stacks = tuple(segment for segment in program_headers if segment.segment_type == _PT_GNU_STACK)
    if len(stacks) != 1 or stacks[0].flags & _PF_X:
        raise GuestElfError("guest_elf_gnu_stack_invalid")


def _range_within(offset: int, size: int, total: int) -> bool:
    return offset <= total and size <= total - offset


def _address_within(address: int, start: int, size: int) -> bool:
    return size > 0 and address >= start and address - start < size


def _contained_file_range(inner: _ProgramHeaderV1, outer: _ProgramHeaderV1) -> bool:
    return (
        inner.file_offset >= outer.file_offset
        and inner.file_offset - outer.file_offset <= outer.file_size
        and inner.file_size <= outer.file_size - (inner.file_offset - outer.file_offset)
    )


def _contained_memory_range(inner: _ProgramHeaderV1, outer: _ProgramHeaderV1) -> bool:
    return (
        inner.virtual_address >= outer.virtual_address
        and inner.virtual_address - outer.virtual_address <= outer.memory_size
        and inner.memory_size <= outer.memory_size - (inner.virtual_address - outer.virtual_address)
    )


def _is_power_of_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


if __name__ == "__main__":
    raise SystemExit(main())
