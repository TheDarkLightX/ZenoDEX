#!/usr/bin/env python3
"""Validate the bounded ELF metadata required by the ZRPF guest profile."""

from __future__ import annotations

import argparse
import json
import os
import stat
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Any

MAX_GUEST_ELF_BYTES = 16 * 1024 * 1024
MAX_PROGRAM_HEADERS = 128
MAX_DYNAMIC_ENTRIES = 4_096
MAX_RELOCATION_ENTRIES = 65_536
MAX_LOAD_MEMORY_BYTES = 64 * 1024 * 1024
MAX_TOTAL_LOAD_MEMORY_BYTES = 256 * 1024 * 1024
MAX_LOAD_VIRTUAL_END = 1 << 32
REPORT_SCHEMA = "zenodex/zrpf_firecracker_guest_elf_check/v2"

_ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
_PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
_DYNAMIC_ENTRY = struct.Struct("<qQ")
_RELA_ENTRY = struct.Struct("<QQq")
_SYMBOL_ENTRY = struct.Struct("<IBBHQQ")

_ET_DYN = 3
_EM_X86_64 = 62
_PN_XNUM = 0xFFFF

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
_DT_PLTRELSZ = 2
_DT_SYMTAB = 6
_DT_RELA = 7
_DT_RELASZ = 8
_DT_RELAENT = 9
_DT_SYMENT = 11
_DT_REL = 17
_DT_RELSZ = 18
_DT_RELENT = 19
_DT_PLTREL = 20
_DT_JMPREL = 23
_DT_TEXTREL = 22
_DT_FLAGS = 30
_DT_RELRSZ = 35
_DT_RELR = 36
_DT_RELRENT = 37
_DT_FLAGS_1 = 0x6FFFFFFB
_DT_RELACOUNT = 0x6FFFFFF9
_DT_RELCOUNT = 0x6FFFFFFA
_DT_VERSYM = 0x6FFFFFF0
_DT_VERDEF = 0x6FFFFFFC
_DT_VERDEFNUM = 0x6FFFFFFD
_DT_VERNEED = 0x6FFFFFFE
_DT_VERNEEDNUM = 0x6FFFFFFF
_DF_TEXTREL = 0x4
_DF_1_PIE = 0x08000000
_R_X86_64_RELATIVE = 8
_R_X86_64_IRELATIVE = 37
_MEMORY_PAGE_BYTES = 4_096
_U64_MAX = (1 << 64) - 1

_UNSUPPORTED_RELOCATION_TAGS = frozenset(
    (
        _DT_PLTRELSZ,
        _DT_REL,
        _DT_RELSZ,
        _DT_RELENT,
        _DT_PLTREL,
        _DT_JMPREL,
        _DT_RELRSZ,
        _DT_RELR,
        _DT_RELRENT,
        _DT_RELCOUNT,
        _DT_VERSYM,
        _DT_VERDEF,
        _DT_VERDEFNUM,
        _DT_VERNEED,
        _DT_VERNEEDNUM,
    )
)


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
    irelative_relocation_count: int
    load_segment_count: int
    program_header_count: int
    rela_entry_count: int
    relative_relocation_count: int

    def __init__(self) -> None:
        raise TypeError("validated guest ELF values require parser construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        dynamic_entry_count: int,
        entry_point: int,
        file_size_bytes: int,
        irelative_relocation_count: int,
        load_segment_count: int,
        program_header_count: int,
        rela_entry_count: int,
        relative_relocation_count: int,
    ) -> ValidatedGuestElfV1:
        value = object.__new__(cls)
        object.__setattr__(value, "dynamic_entry_count", dynamic_entry_count)
        object.__setattr__(value, "entry_point", entry_point)
        object.__setattr__(value, "file_size_bytes", file_size_bytes)
        object.__setattr__(value, "irelative_relocation_count", irelative_relocation_count)
        object.__setattr__(value, "load_segment_count", load_segment_count)
        object.__setattr__(value, "program_header_count", program_header_count)
        object.__setattr__(value, "rela_entry_count", rela_entry_count)
        object.__setattr__(value, "relative_relocation_count", relative_relocation_count)
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
            "irelative_relocation_count": self.irelative_relocation_count,
            "load_segment_count": self.load_segment_count,
            "machine": "x86_64",
            "program_header_count": self.program_header_count,
            "pt_interp_count": 0,
            "rela_entry_count": self.rela_entry_count,
            "relative_relocation_count": self.relative_relocation_count,
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


@dataclass(frozen=True, slots=True)
class _RelocationMetadataV1:
    rela_address: int
    rela_size: int
    relative_count: int
    symbol_table_address: int


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
    load_segments = _validate_segments(
        raw,
        program_headers,
        program_header_offset=program_header_offset,
        program_header_table_size=program_header_size * program_header_count,
    )
    _validate_entry_point(entry_point, load_segments)
    dynamic_segment = _require_single_segment(program_headers, _PT_DYNAMIC)
    _validate_dynamic_mapping(dynamic_segment, load_segments)
    dynamic_entry_count, relocation_metadata = _validate_dynamic_entries(raw, dynamic_segment)
    _validate_relocations(raw, relocation_metadata, load_segments, dynamic_segment)
    rela_entry_count = relocation_metadata.rela_size // _RELA_ENTRY.size
    _validate_gnu_stack(program_headers)
    return ValidatedGuestElfV1._from_validated(
        dynamic_entry_count=dynamic_entry_count,
        entry_point=entry_point,
        file_size_bytes=len(raw),
        irelative_relocation_count=rela_entry_count - relocation_metadata.relative_count,
        load_segment_count=len(load_segments),
        program_header_count=program_header_count,
        rela_entry_count=rela_entry_count,
        relative_relocation_count=relocation_metadata.relative_count,
    )


def load_guest_elf(path: Path) -> ValidatedGuestElfV1:
    """Read one stable regular file and validate its ELF metadata."""

    try:
        raw = _read_bounded_regular(path)
    except (OSError, ValueError) as exc:
        raise GuestElfError("guest_elf_input_rejected") from exc
    return validate_guest_elf_bytes(raw)


def _read_bounded_regular(path: Path) -> bytes:
    """Read one immutable identity snapshot without following a final symlink."""

    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or not 0 < before.st_size <= MAX_GUEST_ELF_BYTES
            or before.st_nlink != 1
        ):
            raise ValueError("guest ELF is not a bounded single-link regular file")
        output = bytearray()
        while len(output) < before.st_size:
            chunk = os.read(descriptor, min(65_536, before.st_size - len(output)))
            if not chunk:
                raise ValueError("guest ELF changed while reading")
            output.extend(chunk)
        if os.read(descriptor, 1):
            raise ValueError("guest ELF changed while reading")
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if _file_identity(before) != _file_identity(after):
        raise ValueError("guest ELF changed while reading")
    return bytes(output)


def _file_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def build_report(path: Path) -> dict[str, Any]:
    errors: list[str] = []
    profile: dict[str, Any] | None = None
    try:
        profile = load_guest_elf(path).to_document()
    except GuestElfError as exc:
        errors.append(exc.code)
    return {
        "authority": {
            "complete_elf_loader_semantics_verified": False,
            "complete_build_input_closure_verified": False,
            "guest_boot_verified": False,
            "guest_source_to_binary_verified": False,
            "production_authority": False,
            "release_authority": False,
        },
        "errors": errors,
        "ok": not errors,
        "profile": profile,
        "schema": REPORT_SCHEMA,
        "validation_scope": "bounded_elf64_pt_load_and_relocation_metadata",
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
    *,
    program_header_offset: int,
    program_header_table_size: int,
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
        if segment.alignment != _MEMORY_PAGE_BYTES or segment.file_size > segment.memory_size:
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
    _validate_executable_writable_page_separation(load_segments)
    _validate_load_map(
        load_segments,
        program_headers=program_headers,
        program_header_offset=program_header_offset,
        program_header_table_size=program_header_table_size,
    )
    return tuple(load_segments)


def _validate_executable_writable_page_separation(
    load_segments: list[_ProgramHeaderV1],
) -> None:
    executable = (segment for segment in load_segments if segment.flags & _PF_X)
    writable = tuple(segment for segment in load_segments if segment.flags & _PF_W)
    for executable_segment in executable:
        for writable_segment in writable:
            if _page_ranges_overlap(executable_segment, writable_segment):
                raise GuestElfError("guest_elf_executable_writable_page_overlap")


def _validate_load_map(
    load_segments: list[_ProgramHeaderV1],
    *,
    program_headers: tuple[_ProgramHeaderV1, ...],
    program_header_offset: int,
    program_header_table_size: int,
) -> None:
    load_bias_sources = tuple(
        segment
        for segment in load_segments
        if segment.file_size > 0 and segment.file_offset == 0
    )
    if (
        len(load_bias_sources) != 1
        or load_bias_sources[0] is not load_segments[0]
        or load_bias_sources[0].virtual_address != 0
        or load_bias_sources[0].flags != _PF_R
    ):
        raise GuestElfError("guest_elf_load_bias_invalid")
    first_load = load_segments[0]
    if not _range_within(
        program_header_offset,
        program_header_table_size,
        first_load.file_size,
    ):
        raise GuestElfError("guest_elf_program_headers_unmapped")
    _validate_program_header_segment(
        load_segments=load_segments,
        program_headers=program_headers,
        program_header_offset=program_header_offset,
        program_header_table_size=program_header_table_size,
    )
    previous_page_end: int | None = None
    total_memory = 0
    for segment in load_segments:
        address_end = segment.virtual_address + segment.memory_size
        if (
            segment.memory_size == 0
            or segment.memory_size > MAX_LOAD_MEMORY_BYTES
            or address_end > MAX_LOAD_VIRTUAL_END
            or segment.flags & ~(_PF_R | _PF_W | _PF_X)
            or not segment.flags & _PF_R
        ):
            raise GuestElfError("guest_elf_load_geometry_invalid")
        total_memory += segment.memory_size
        if total_memory > MAX_TOTAL_LOAD_MEMORY_BYTES:
            raise GuestElfError("guest_elf_load_geometry_invalid")
        page_start = segment.virtual_address // _MEMORY_PAGE_BYTES
        page_end = _page_end(segment.virtual_address, segment.memory_size)
        if previous_page_end is not None and page_start < previous_page_end:
            raise GuestElfError("guest_elf_load_mapping_invalid")
        previous_page_end = page_end


def _validate_program_header_segment(
    *,
    load_segments: list[_ProgramHeaderV1],
    program_headers: tuple[_ProgramHeaderV1, ...],
    program_header_offset: int,
    program_header_table_size: int,
) -> None:
    matches = tuple(
        segment for segment in program_headers if segment.segment_type == _PT_PHDR
    )
    first_load = load_segments[0]
    if len(matches) != 1:
        raise GuestElfError("guest_elf_program_header_segment_invalid")
    segment = matches[0]
    if not (
        segment.flags == _PF_R
        and segment.file_offset == program_header_offset
        and segment.virtual_address == program_header_offset
        and segment.file_size == program_header_table_size
        and segment.memory_size == program_header_table_size
        and segment.alignment == 8
        and _contained_file_range(segment, first_load)
        and _contained_memory_range(segment, first_load)
    ):
        raise GuestElfError("guest_elf_program_header_segment_invalid")


def _validate_entry_point(
    entry_point: int,
    load_segments: tuple[_ProgramHeaderV1, ...],
) -> None:
    for segment in load_segments:
        if segment.flags & (_PF_R | _PF_X) != (_PF_R | _PF_X):
            continue
        if _address_within(entry_point, segment.virtual_address, segment.file_size):
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
    overlapping_loads = tuple(
        load
        for load in load_segments
        if _page_ranges_overlap(dynamic, load)
    )
    if len(overlapping_loads) != 1:
        raise GuestElfError("guest_elf_dynamic_segment_mapping_invalid")
    load = overlapping_loads[0]
    if not (
        load.flags & _PF_R
        and _contained_file_range(dynamic, load)
        and _contained_memory_range(dynamic, load)
        and dynamic.file_offset - load.file_offset
        == dynamic.virtual_address - load.virtual_address
    ):
        raise GuestElfError("guest_elf_dynamic_segment_mapping_invalid")


def _validate_dynamic_entries(
    raw: bytes,
    dynamic: _ProgramHeaderV1,
) -> tuple[int, _RelocationMetadataV1]:
    entry_count = dynamic.file_size // _DYNAMIC_ENTRY.size
    saw_null = False
    flags_1_values: list[int] = []
    relocation_values: dict[int, list[int]] = {
        _DT_SYMTAB: [],
        _DT_RELA: [],
        _DT_RELASZ: [],
        _DT_RELAENT: [],
        _DT_SYMENT: [],
        _DT_RELACOUNT: [],
    }
    for index in range(entry_count):
        tag, value = _DYNAMIC_ENTRY.unpack_from(
            raw,
            dynamic.file_offset + index * _DYNAMIC_ENTRY.size,
        )
        if tag == _DT_NEEDED:
            raise GuestElfError("guest_elf_needed_dependency_present")
        if tag in _UNSUPPORTED_RELOCATION_TAGS:
            raise GuestElfError("guest_elf_unsupported_relocation_table")
        if tag == _DT_TEXTREL or (tag == _DT_FLAGS and value & _DF_TEXTREL):
            raise GuestElfError("guest_elf_text_relocation_present")
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
        elif tag in relocation_values:
            relocation_values[tag].append(value)
    if not saw_null:
        raise GuestElfError("guest_elf_dynamic_terminator_invalid")
    if len(flags_1_values) != 1 or not flags_1_values[0] & _DF_1_PIE:
        raise GuestElfError("guest_elf_df_1_pie_missing")
    return entry_count, _validate_relocation_metadata(relocation_values)


def _validate_relocation_metadata(
    values: dict[int, list[int]],
) -> _RelocationMetadataV1:
    if any(len(items) != 1 for items in values.values()):
        raise GuestElfError("guest_elf_relocation_metadata_invalid")
    rela_address = values[_DT_RELA][0]
    rela_size = values[_DT_RELASZ][0]
    rela_entry_size = values[_DT_RELAENT][0]
    relative_count = values[_DT_RELACOUNT][0]
    symbol_table_address = values[_DT_SYMTAB][0]
    symbol_entry_size = values[_DT_SYMENT][0]
    if (
        rela_address == 0
        or rela_address % 8 != 0
        or symbol_table_address % 8 != 0
        or rela_size == 0
        or rela_entry_size != _RELA_ENTRY.size
        or symbol_entry_size != _SYMBOL_ENTRY.size
        or rela_size % _RELA_ENTRY.size != 0
        or rela_size // _RELA_ENTRY.size > MAX_RELOCATION_ENTRIES
        or relative_count > rela_size // _RELA_ENTRY.size
    ):
        raise GuestElfError("guest_elf_relocation_metadata_invalid")
    return _RelocationMetadataV1(
        rela_address=rela_address,
        rela_size=rela_size,
        relative_count=relative_count,
        symbol_table_address=symbol_table_address,
    )


def _validate_relocations(
    raw: bytes,
    metadata: _RelocationMetadataV1,
    load_segments: tuple[_ProgramHeaderV1, ...],
    dynamic: _ProgramHeaderV1,
) -> None:
    table_offset = _map_virtual_file_range(
        metadata.rela_address,
        metadata.rela_size,
        load_segments,
        required_flags=_PF_R,
        forbidden_flags=_PF_W,
    )
    try:
        symbol_zero_offset = _map_virtual_file_range(
            metadata.symbol_table_address,
            _SYMBOL_ENTRY.size,
            load_segments,
            required_flags=_PF_R,
            forbidden_flags=_PF_W,
        )
    except GuestElfError as exc:
        raise GuestElfError("guest_elf_symbol_table_mapping_invalid") from exc
    if raw[symbol_zero_offset : symbol_zero_offset + _SYMBOL_ENTRY.size] != bytes(
        _SYMBOL_ENTRY.size
    ):
        raise GuestElfError("guest_elf_symbol_zero_invalid")
    relocation_count = metadata.rela_size // _RELA_ENTRY.size
    seen_targets: set[int] = set()
    for index in range(relocation_count):
        target, info, addend = _RELA_ENTRY.unpack_from(
            raw,
            table_offset + index * _RELA_ENTRY.size,
        )
        symbol_index = info >> 32
        relocation_type = info & 0xFFFFFFFF
        expected_type = (
            _R_X86_64_RELATIVE
            if index < metadata.relative_count
            else _R_X86_64_IRELATIVE
        )
        if symbol_index != 0:
            raise GuestElfError("guest_elf_relocation_symbol_invalid")
        if relocation_type not in (_R_X86_64_RELATIVE, _R_X86_64_IRELATIVE):
            raise GuestElfError("guest_elf_relocation_type_unsupported")
        if relocation_type != expected_type:
            raise GuestElfError("guest_elf_relocation_order_invalid")
        if (
            target % 8 != 0
            or not _memory_range_in_single_load(target, 8, load_segments, _PF_W)
            or _address_ranges_overlap(
                target,
                8,
                dynamic.virtual_address,
                dynamic.memory_size,
            )
        ):
            raise GuestElfError("guest_elf_relocation_target_invalid")
        if target in seen_targets:
            raise GuestElfError("guest_elf_relocation_target_duplicate")
        seen_targets.add(target)
        required_flags = _PF_R | _PF_X if expected_type == _R_X86_64_IRELATIVE else 0
        addend_valid = addend >= 0 and (
            _file_range_in_single_load(
                addend,
                1,
                load_segments,
                required_flags=required_flags,
            )
            if expected_type == _R_X86_64_IRELATIVE
            else _memory_range_in_single_load(addend, 1, load_segments, required_flags=0)
        )
        if not addend_valid:
            code = (
                "guest_elf_irelative_resolver_invalid"
                if expected_type == _R_X86_64_IRELATIVE
                else "guest_elf_relative_addend_invalid"
            )
            raise GuestElfError(code)


def _map_virtual_file_range(
    address: int,
    size: int,
    load_segments: tuple[_ProgramHeaderV1, ...],
    *,
    required_flags: int,
    forbidden_flags: int = 0,
) -> int:
    matches: list[int] = []
    for segment in load_segments:
        if (
            segment.flags & required_flags != required_flags
            or segment.flags & forbidden_flags
            or address < segment.virtual_address
        ):
            continue
        delta = address - segment.virtual_address
        if delta <= segment.file_size and size <= segment.file_size - delta:
            matches.append(segment.file_offset + delta)
    if len(matches) != 1:
        raise GuestElfError("guest_elf_relocation_table_mapping_invalid")
    return matches[0]


def _file_range_in_single_load(
    address: int,
    size: int,
    load_segments: tuple[_ProgramHeaderV1, ...],
    *,
    required_flags: int,
) -> bool:
    try:
        _map_virtual_file_range(
            address,
            size,
            load_segments,
            required_flags=required_flags,
        )
    except GuestElfError:
        return False
    return True


def _memory_range_in_single_load(
    address: int,
    size: int,
    load_segments: tuple[_ProgramHeaderV1, ...],
    required_flags: int,
) -> bool:
    matches = 0
    for segment in load_segments:
        if segment.flags & required_flags != required_flags or address < segment.virtual_address:
            continue
        delta = address - segment.virtual_address
        if delta <= segment.memory_size and size <= segment.memory_size - delta:
            matches += 1
    return matches == 1


def _address_ranges_overlap(
    left: int,
    left_size: int,
    right: int,
    right_size: int,
) -> bool:
    return left < right + right_size and right < left + left_size


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


def _page_ranges_overlap(left: _ProgramHeaderV1, right: _ProgramHeaderV1) -> bool:
    left_start = left.virtual_address // _MEMORY_PAGE_BYTES
    right_start = right.virtual_address // _MEMORY_PAGE_BYTES
    left_end = _page_end(left.virtual_address, left.memory_size)
    right_end = _page_end(right.virtual_address, right.memory_size)
    return left_start < right_end and right_start < left_end


def _page_end(start: int, size: int) -> int:
    end = start + size
    if end > _U64_MAX - (_MEMORY_PAGE_BYTES - 1):
        raise GuestElfError("guest_elf_load_geometry_invalid")
    return (end + _MEMORY_PAGE_BYTES - 1) // _MEMORY_PAGE_BYTES


def _is_power_of_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


if __name__ == "__main__":
    raise SystemExit(main())
