//! Bounded native validator for the ZRPF Firecracker guest ELF profile.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::{File, Metadata};
use std::io::{Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;

use rustix::fs::{Mode, OFlags};

const MAX_GUEST_ELF_BYTES: u64 = 16 * 1024 * 1024;
const MAX_PROGRAM_HEADERS: u16 = 128;
const MAX_DYNAMIC_ENTRIES: u64 = 4_096;
const MAX_RELOCATION_ENTRIES: u64 = 65_536;
const MAX_LOAD_MEMORY_BYTES: u64 = 64 * 1024 * 1024;
const MAX_TOTAL_LOAD_MEMORY_BYTES: u64 = 256 * 1024 * 1024;
const MAX_LOAD_VIRTUAL_END: u64 = 1_u64 << 32;
const ELF_HEADER_BYTES: u16 = 64;
const PROGRAM_HEADER_BYTES: u16 = 56;
const DYNAMIC_ENTRY_BYTES: u64 = 16;
#[cfg(test)]
const DYNAMIC_ENTRY_BYTES_USIZE: usize = 16;
const RELA_ENTRY_BYTES: u64 = 24;
#[cfg(test)]
const RELA_ENTRY_BYTES_USIZE: usize = 24;
const SYMBOL_ENTRY_BYTES: u64 = 24;
const SYMBOL_ENTRY_BYTES_USIZE: usize = 24;

const ET_DYN: u16 = 3;
const EM_X86_64: u16 = 62;
const PN_XNUM: u16 = 0xffff;

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;
const PT_PHDR: u32 = 6;
const PT_GNU_STACK: u32 = 0x6474_e551;

const PF_X: u32 = 1;
const PF_W: u32 = 2;
const PF_R: u32 = 4;

const DT_NULL: i64 = 0;
const DT_NEEDED: i64 = 1;
const DT_PLTRELSZ: i64 = 2;
const DT_SYMTAB: i64 = 6;
const DT_RELA: i64 = 7;
const DT_RELASZ: i64 = 8;
const DT_RELAENT: i64 = 9;
const DT_SYMENT: i64 = 11;
const DT_REL: i64 = 17;
const DT_RELSZ: i64 = 18;
const DT_RELENT: i64 = 19;
const DT_PLTREL: i64 = 20;
const DT_JMPREL: i64 = 23;
const DT_TEXTREL: i64 = 22;
const DT_FLAGS: i64 = 30;
const DT_RELRSZ: i64 = 35;
const DT_RELR: i64 = 36;
const DT_RELRENT: i64 = 37;
const DT_FLAGS_1: i64 = 0x6fff_fffb;
const DT_RELACOUNT: i64 = 0x6fff_fff9;
const DT_RELCOUNT: i64 = 0x6fff_fffa;
const DT_VERSYM: i64 = 0x6fff_fff0;
const DT_VERDEF: i64 = 0x6fff_fffc;
const DT_VERDEFNUM: i64 = 0x6fff_fffd;
const DT_VERNEED: i64 = 0x6fff_fffe;
const DT_VERNEEDNUM: i64 = 0x6fff_ffff;
const DF_TEXTREL: u64 = 0x4;
const DF_1_PIE: u64 = 0x0800_0000;
const R_X86_64_RELATIVE: u32 = 8;
const R_X86_64_IRELATIVE: u32 = 37;
const MEMORY_PAGE_BYTES: u64 = 4_096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GuestElfError(&'static str);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProgramHeader {
    segment_type: u32,
    flags: u32,
    file_offset: u64,
    virtual_address: u64,
    file_size: u64,
    memory_size: u64,
    alignment: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RelocationMetadata {
    rela_address: u64,
    rela_size: u64,
    relative_count: u64,
    symbol_table_address: u64,
}

fn main() {
    if let Err(error) = run() {
        let _ = writeln!(std::io::stderr().lock(), "error: {}", error.0);
        std::process::exit(2);
    }
}

fn run() -> Result<(), GuestElfError> {
    let mut arguments = std::env::args_os().skip(1);
    let option = arguments.next().ok_or(GuestElfError("guest_elf_usage"))?;
    let path = arguments.next().ok_or(GuestElfError("guest_elf_usage"))?;
    if option != OsStr::new("--guest-elf") || arguments.next().is_some() {
        return Err(GuestElfError("guest_elf_usage"));
    }
    let raw = read_bounded_regular(Path::new(&path))?;
    validate_guest_elf_bytes(&raw)
}

fn read_bounded_regular(path: &Path) -> Result<Vec<u8>, GuestElfError> {
    let descriptor = rustix::fs::open(
        path,
        OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK,
        Mode::empty(),
    )
    .map_err(|_| GuestElfError("guest_elf_input_rejected"))?;
    let mut file = File::from(descriptor);
    let before = file
        .metadata()
        .map_err(|_| GuestElfError("guest_elf_input_rejected"))?;
    if !before.is_file()
        || before.nlink() != 1
        || before.len() == 0
        || before.len() > MAX_GUEST_ELF_BYTES
    {
        return Err(GuestElfError("guest_elf_input_rejected"));
    }
    let size =
        usize::try_from(before.len()).map_err(|_| GuestElfError("guest_elf_input_rejected"))?;
    let mut raw = vec![0_u8; size];
    file.read_exact(&mut raw)
        .map_err(|_| GuestElfError("guest_elf_input_rejected"))?;
    let mut extra = [0_u8; 1];
    if file
        .read(&mut extra)
        .map_err(|_| GuestElfError("guest_elf_input_rejected"))?
        != 0
    {
        return Err(GuestElfError("guest_elf_input_rejected"));
    }
    let after = file
        .metadata()
        .map_err(|_| GuestElfError("guest_elf_input_rejected"))?;
    if file_identity(&before) != file_identity(&after) {
        return Err(GuestElfError("guest_elf_input_rejected"));
    }
    Ok(raw)
}

fn file_identity(metadata: &Metadata) -> (u64, u64, u32, u64, u64, i64, i64, i64, i64) {
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.nlink(),
        metadata.size(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

fn validate_guest_elf_bytes(raw: &[u8]) -> Result<(), GuestElfError> {
    if raw.is_empty() || raw.len() > MAX_GUEST_ELF_BYTES as usize {
        return Err(GuestElfError("guest_elf_input_size_invalid"));
    }
    validate_identity_and_header(raw)?;
    let entry_point = read_u64(raw, 24)?;
    let program_header_offset = read_u64(raw, 32)?;
    let program_header_size = read_u16(raw, 54)?;
    let program_header_count = read_u16(raw, 56)?;
    validate_program_header_geometry(
        raw,
        program_header_offset,
        program_header_size,
        program_header_count,
    )?;
    let program_headers = parse_program_headers(raw, program_header_offset, program_header_count)?;
    let program_header_table_size = u64::from(program_header_size)
        .checked_mul(u64::from(program_header_count))
        .ok_or(GuestElfError("guest_elf_program_header_table_invalid"))?;
    let load_segments = validate_segments(
        raw,
        &program_headers,
        program_header_offset,
        program_header_table_size,
    )?;
    validate_entry_point(entry_point, &load_segments)?;
    let dynamic = require_single_dynamic_segment(&program_headers)?;
    validate_dynamic_mapping(dynamic, &load_segments)?;
    let relocation_metadata = validate_dynamic_entries(raw, dynamic)?;
    validate_relocations(raw, relocation_metadata, &load_segments, dynamic)?;
    validate_gnu_stack(&program_headers)
}

fn validate_identity_and_header(raw: &[u8]) -> Result<(), GuestElfError> {
    if raw.len() < usize::from(ELF_HEADER_BYTES) {
        return Err(GuestElfError("guest_elf_header_truncated"));
    }
    let identity = raw
        .get(0..16)
        .ok_or(GuestElfError("guest_elf_header_truncated"))?;
    if identity.get(0..4) != Some(b"\x7fELF") {
        return Err(GuestElfError("guest_elf_magic_invalid"));
    }
    if identity.get(4) != Some(&2)
        || identity.get(5) != Some(&1)
        || identity.get(6) != Some(&1)
        || identity.get(7) != Some(&0)
        || identity.get(8) != Some(&0)
        || identity
            .get(9..)
            .is_none_or(|tail| tail.iter().any(|value| *value != 0))
    {
        return Err(GuestElfError("guest_elf_identity_unsupported"));
    }
    if read_u16(raw, 16)? != ET_DYN
        || read_u16(raw, 18)? != EM_X86_64
        || read_u32(raw, 20)? != 1
        || read_u32(raw, 48)? != 0
    {
        return Err(GuestElfError("guest_elf_machine_profile_invalid"));
    }
    if read_u16(raw, 52)? != ELF_HEADER_BYTES {
        return Err(GuestElfError("guest_elf_header_geometry_invalid"));
    }
    Ok(())
}

fn validate_program_header_geometry(
    raw: &[u8],
    table_offset: u64,
    entry_size: u16,
    entry_count: u16,
) -> Result<(), GuestElfError> {
    if entry_size != PROGRAM_HEADER_BYTES {
        return Err(GuestElfError("guest_elf_program_header_size_invalid"));
    }
    if entry_count == 0 || entry_count == PN_XNUM || entry_count > MAX_PROGRAM_HEADERS {
        return Err(GuestElfError("guest_elf_program_header_count_invalid"));
    }
    let table_size = u64::from(entry_size)
        .checked_mul(u64::from(entry_count))
        .ok_or(GuestElfError("guest_elf_program_header_table_invalid"))?;
    let raw_size = u64::try_from(raw.len())
        .map_err(|_| GuestElfError("guest_elf_program_header_table_invalid"))?;
    if table_offset < u64::from(ELF_HEADER_BYTES)
        || !table_offset.is_multiple_of(8)
        || !range_within(table_offset, table_size, raw_size)
    {
        return Err(GuestElfError("guest_elf_program_header_table_invalid"));
    }
    Ok(())
}

fn parse_program_headers(
    raw: &[u8],
    table_offset: u64,
    count: u16,
) -> Result<Vec<ProgramHeader>, GuestElfError> {
    let mut output = Vec::with_capacity(usize::from(count));
    for index in 0..count {
        let offset = table_offset
            .checked_add(u64::from(index) * u64::from(PROGRAM_HEADER_BYTES))
            .ok_or(GuestElfError("guest_elf_program_header_table_invalid"))?;
        let offset = usize::try_from(offset)
            .map_err(|_| GuestElfError("guest_elf_program_header_table_invalid"))?;
        output.push(ProgramHeader {
            segment_type: read_u32(raw, offset)?,
            flags: read_u32(raw, offset + 4)?,
            file_offset: read_u64(raw, offset + 8)?,
            virtual_address: read_u64(raw, offset + 16)?,
            file_size: read_u64(raw, offset + 32)?,
            memory_size: read_u64(raw, offset + 40)?,
            alignment: read_u64(raw, offset + 48)?,
        });
    }
    Ok(output)
}

fn validate_segments(
    raw: &[u8],
    program_headers: &[ProgramHeader],
    program_header_offset: u64,
    program_header_table_size: u64,
) -> Result<Vec<ProgramHeader>, GuestElfError> {
    let mut load_segments = Vec::new();
    let raw_size = u64::try_from(raw.len())
        .map_err(|_| GuestElfError("guest_elf_segment_file_range_invalid"))?;
    for segment in program_headers {
        if segment.file_size != 0 && !range_within(segment.file_offset, segment.file_size, raw_size)
        {
            return Err(GuestElfError("guest_elf_segment_file_range_invalid"));
        }
        if segment.alignment > 1 && !segment.alignment.is_power_of_two() {
            return Err(GuestElfError("guest_elf_segment_alignment_invalid"));
        }
        if segment.segment_type == PT_INTERP {
            return Err(GuestElfError("guest_elf_interpreter_present"));
        }
        if segment.segment_type != PT_LOAD {
            continue;
        }
        if segment.alignment != MEMORY_PAGE_BYTES
            || segment.file_size > segment.memory_size
            || segment.file_offset % segment.alignment
                != segment.virtual_address % segment.alignment
        {
            return Err(GuestElfError("guest_elf_load_geometry_invalid"));
        }
        if segment.flags & PF_W != 0 && segment.flags & PF_X != 0 {
            return Err(GuestElfError("guest_elf_writable_executable_load"));
        }
        load_segments.push(*segment);
    }
    if load_segments.is_empty() {
        return Err(GuestElfError("guest_elf_load_segment_missing"));
    }
    validate_executable_writable_page_separation(&load_segments)?;
    validate_load_map(
        &load_segments,
        program_headers,
        program_header_offset,
        program_header_table_size,
    )?;
    Ok(load_segments)
}

fn validate_executable_writable_page_separation(
    load_segments: &[ProgramHeader],
) -> Result<(), GuestElfError> {
    for executable in load_segments
        .iter()
        .filter(|segment| segment.flags & PF_X != 0)
    {
        for writable in load_segments
            .iter()
            .filter(|segment| segment.flags & PF_W != 0)
        {
            if page_ranges_overlap(executable, writable)? {
                return Err(GuestElfError("guest_elf_executable_writable_page_overlap"));
            }
        }
    }
    Ok(())
}

fn validate_load_map(
    load_segments: &[ProgramHeader],
    program_headers: &[ProgramHeader],
    program_header_offset: u64,
    program_header_table_size: u64,
) -> Result<(), GuestElfError> {
    let load_bias_sources = load_segments
        .iter()
        .filter(|segment| segment.file_size > 0 && segment.file_offset == 0)
        .collect::<Vec<_>>();
    if load_bias_sources.len() != 1
        || load_bias_sources[0] != &load_segments[0]
        || load_bias_sources[0].virtual_address != 0
        || load_bias_sources[0].flags != PF_R
    {
        return Err(GuestElfError("guest_elf_load_bias_invalid"));
    }
    if !range_within(
        program_header_offset,
        program_header_table_size,
        load_segments[0].file_size,
    ) {
        return Err(GuestElfError("guest_elf_program_headers_unmapped"));
    }
    validate_program_header_segment(
        program_headers,
        load_segments[0],
        program_header_offset,
        program_header_table_size,
    )?;
    let mut previous_page_end = None;
    let mut total_memory = 0_u64;
    for segment in load_segments {
        let address_end = segment
            .virtual_address
            .checked_add(segment.memory_size)
            .ok_or(GuestElfError("guest_elf_load_geometry_invalid"))?;
        total_memory = total_memory
            .checked_add(segment.memory_size)
            .ok_or(GuestElfError("guest_elf_load_geometry_invalid"))?;
        if segment.memory_size == 0
            || segment.memory_size > MAX_LOAD_MEMORY_BYTES
            || address_end > MAX_LOAD_VIRTUAL_END
            || total_memory > MAX_TOTAL_LOAD_MEMORY_BYTES
            || segment.flags & !(PF_R | PF_W | PF_X) != 0
            || segment.flags & PF_R == 0
        {
            return Err(GuestElfError("guest_elf_load_geometry_invalid"));
        }
        let page_start = segment.virtual_address / MEMORY_PAGE_BYTES;
        let current_page_end = page_end(segment.virtual_address, segment.memory_size)?;
        if previous_page_end.is_some_and(|end| page_start < end) {
            return Err(GuestElfError("guest_elf_load_mapping_invalid"));
        }
        previous_page_end = Some(current_page_end);
    }
    Ok(())
}

fn validate_program_header_segment(
    program_headers: &[ProgramHeader],
    first_load: ProgramHeader,
    table_offset: u64,
    table_size: u64,
) -> Result<(), GuestElfError> {
    let mut phdr = None;
    for segment in program_headers {
        if segment.segment_type != PT_PHDR {
            continue;
        }
        if phdr.replace(*segment).is_some() {
            return Err(GuestElfError("guest_elf_program_header_segment_invalid"));
        }
    }
    let phdr = phdr.ok_or(GuestElfError("guest_elf_program_header_segment_invalid"))?;
    if phdr.flags != PF_R
        || phdr.file_offset != table_offset
        || phdr.virtual_address != table_offset
        || phdr.file_size != table_size
        || phdr.memory_size != table_size
        || phdr.alignment != 8
        || !contained_range(
            phdr.file_offset,
            phdr.file_size,
            first_load.file_offset,
            first_load.file_size,
        )
        || !contained_range(
            phdr.virtual_address,
            phdr.memory_size,
            first_load.virtual_address,
            first_load.memory_size,
        )
    {
        return Err(GuestElfError("guest_elf_program_header_segment_invalid"));
    }
    Ok(())
}

fn validate_entry_point(
    entry_point: u64,
    load_segments: &[ProgramHeader],
) -> Result<(), GuestElfError> {
    if load_segments.iter().any(|segment| {
        segment.flags & (PF_R | PF_X) == (PF_R | PF_X)
            && address_within(entry_point, segment.virtual_address, segment.file_size)
    }) {
        Ok(())
    } else {
        Err(GuestElfError("guest_elf_entrypoint_invalid"))
    }
}

fn require_single_dynamic_segment(
    program_headers: &[ProgramHeader],
) -> Result<ProgramHeader, GuestElfError> {
    let mut dynamic = None;
    for segment in program_headers {
        if segment.segment_type == PT_DYNAMIC {
            if dynamic.is_some() {
                return Err(GuestElfError("guest_elf_dynamic_segment_count_invalid"));
            }
            dynamic = Some(*segment);
        }
    }
    dynamic.ok_or(GuestElfError("guest_elf_dynamic_segment_count_invalid"))
}

fn validate_dynamic_mapping(
    dynamic: ProgramHeader,
    load_segments: &[ProgramHeader],
) -> Result<(), GuestElfError> {
    if dynamic.file_size == 0
        || dynamic.file_size > MAX_DYNAMIC_ENTRIES * DYNAMIC_ENTRY_BYTES
        || !dynamic.file_size.is_multiple_of(DYNAMIC_ENTRY_BYTES)
        || !dynamic.file_offset.is_multiple_of(8)
        || !dynamic.virtual_address.is_multiple_of(8)
        || dynamic.file_size > dynamic.memory_size
    {
        return Err(GuestElfError("guest_elf_dynamic_segment_geometry_invalid"));
    }
    let mut mapped_load = None;
    for load in load_segments {
        if page_ranges_overlap(&dynamic, load)? {
            if mapped_load.is_some() {
                return Err(GuestElfError("guest_elf_dynamic_segment_mapping_invalid"));
            }
            mapped_load = Some(load);
        }
    }
    let load = mapped_load.ok_or(GuestElfError("guest_elf_dynamic_segment_mapping_invalid"))?;
    if load.flags & PF_R == 0
        || !contained_range(
            dynamic.file_offset,
            dynamic.file_size,
            load.file_offset,
            load.file_size,
        )
        || !contained_range(
            dynamic.virtual_address,
            dynamic.memory_size,
            load.virtual_address,
            load.memory_size,
        )
        || dynamic.file_offset - load.file_offset != dynamic.virtual_address - load.virtual_address
    {
        return Err(GuestElfError("guest_elf_dynamic_segment_mapping_invalid"));
    }
    Ok(())
}

fn validate_dynamic_entries(
    raw: &[u8],
    dynamic: ProgramHeader,
) -> Result<RelocationMetadata, GuestElfError> {
    let entry_count = dynamic.file_size / DYNAMIC_ENTRY_BYTES;
    let mut saw_null = false;
    let mut flags_1_count = 0_u64;
    let mut flags_1_value = 0_u64;
    let mut rela_address = None;
    let mut rela_size = None;
    let mut rela_entry_size = None;
    let mut relative_count = None;
    let mut symbol_table_address = None;
    let mut symbol_entry_size = None;
    let mut relocation_metadata_duplicate = false;
    for index in 0..entry_count {
        let offset = dynamic
            .file_offset
            .checked_add(index * DYNAMIC_ENTRY_BYTES)
            .ok_or(GuestElfError("guest_elf_dynamic_segment_geometry_invalid"))?;
        let offset = usize::try_from(offset)
            .map_err(|_| GuestElfError("guest_elf_dynamic_segment_geometry_invalid"))?;
        let tag = read_i64(raw, offset)?;
        let value = read_u64(raw, offset + 8)?;
        if tag == DT_NEEDED {
            return Err(GuestElfError("guest_elf_needed_dependency_present"));
        }
        if matches!(
            tag,
            DT_PLTRELSZ
                | DT_REL
                | DT_RELSZ
                | DT_RELENT
                | DT_PLTREL
                | DT_JMPREL
                | DT_RELRSZ
                | DT_RELR
                | DT_RELRENT
                | DT_RELCOUNT
                | DT_VERSYM
                | DT_VERDEF
                | DT_VERDEFNUM
                | DT_VERNEED
                | DT_VERNEEDNUM
        ) {
            return Err(GuestElfError("guest_elf_unsupported_relocation_table"));
        }
        if tag == DT_TEXTREL || (tag == DT_FLAGS && value & DF_TEXTREL != 0) {
            return Err(GuestElfError("guest_elf_text_relocation_present"));
        }
        if saw_null {
            if tag != DT_NULL || value != 0 {
                return Err(GuestElfError("guest_elf_dynamic_terminator_invalid"));
            }
        } else if tag == DT_NULL {
            if value != 0 {
                return Err(GuestElfError("guest_elf_dynamic_terminator_invalid"));
            }
            saw_null = true;
        } else if tag == DT_FLAGS_1 {
            flags_1_count += 1;
            flags_1_value = value;
        } else if tag == DT_RELA {
            relocation_metadata_duplicate |= set_dynamic_value(&mut rela_address, value);
        } else if tag == DT_RELASZ {
            relocation_metadata_duplicate |= set_dynamic_value(&mut rela_size, value);
        } else if tag == DT_RELAENT {
            relocation_metadata_duplicate |= set_dynamic_value(&mut rela_entry_size, value);
        } else if tag == DT_RELACOUNT {
            relocation_metadata_duplicate |= set_dynamic_value(&mut relative_count, value);
        } else if tag == DT_SYMTAB {
            relocation_metadata_duplicate |= set_dynamic_value(&mut symbol_table_address, value);
        } else if tag == DT_SYMENT {
            relocation_metadata_duplicate |= set_dynamic_value(&mut symbol_entry_size, value);
        }
    }
    if !saw_null {
        return Err(GuestElfError("guest_elf_dynamic_terminator_invalid"));
    }
    if flags_1_count != 1 || flags_1_value & DF_1_PIE == 0 {
        return Err(GuestElfError("guest_elf_df_1_pie_missing"));
    }
    if relocation_metadata_duplicate {
        return Err(GuestElfError("guest_elf_relocation_metadata_invalid"));
    }
    validate_relocation_metadata(
        rela_address,
        rela_size,
        rela_entry_size,
        relative_count,
        symbol_table_address,
        symbol_entry_size,
    )
}

fn set_dynamic_value(slot: &mut Option<u64>, value: u64) -> bool {
    slot.replace(value).is_some()
}

fn validate_relocation_metadata(
    rela_address: Option<u64>,
    rela_size: Option<u64>,
    rela_entry_size: Option<u64>,
    relative_count: Option<u64>,
    symbol_table_address: Option<u64>,
    symbol_entry_size: Option<u64>,
) -> Result<RelocationMetadata, GuestElfError> {
    let metadata = RelocationMetadata {
        rela_address: rela_address.ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?,
        rela_size: rela_size.ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?,
        relative_count: relative_count
            .ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?,
        symbol_table_address: symbol_table_address
            .ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?,
    };
    let entry_size =
        rela_entry_size.ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?;
    let symbol_size =
        symbol_entry_size.ok_or(GuestElfError("guest_elf_relocation_metadata_invalid"))?;
    if metadata.rela_address == 0
        || !metadata.rela_address.is_multiple_of(8)
        || !metadata.symbol_table_address.is_multiple_of(8)
        || metadata.rela_size == 0
        || entry_size != RELA_ENTRY_BYTES
        || symbol_size != SYMBOL_ENTRY_BYTES
        || !metadata.rela_size.is_multiple_of(RELA_ENTRY_BYTES)
        || metadata.rela_size / RELA_ENTRY_BYTES > MAX_RELOCATION_ENTRIES
        || metadata.relative_count > metadata.rela_size / RELA_ENTRY_BYTES
    {
        return Err(GuestElfError("guest_elf_relocation_metadata_invalid"));
    }
    Ok(metadata)
}

fn validate_relocations(
    raw: &[u8],
    metadata: RelocationMetadata,
    load_segments: &[ProgramHeader],
    dynamic: ProgramHeader,
) -> Result<(), GuestElfError> {
    let table_offset = map_virtual_file_range(
        metadata.rela_address,
        metadata.rela_size,
        load_segments,
        PF_R,
        PF_W,
    )?;
    let symbol_zero_offset = map_virtual_file_range(
        metadata.symbol_table_address,
        SYMBOL_ENTRY_BYTES,
        load_segments,
        PF_R,
        PF_W,
    )
    .map_err(|_| GuestElfError("guest_elf_symbol_table_mapping_invalid"))?;
    let symbol_zero_offset = usize::try_from(symbol_zero_offset)
        .map_err(|_| GuestElfError("guest_elf_relocation_table_mapping_invalid"))?;
    let symbol_zero_end = symbol_zero_offset
        .checked_add(SYMBOL_ENTRY_BYTES_USIZE)
        .ok_or(GuestElfError("guest_elf_relocation_table_mapping_invalid"))?;
    if raw
        .get(symbol_zero_offset..symbol_zero_end)
        .is_none_or(|symbol| symbol.iter().any(|byte| *byte != 0))
    {
        return Err(GuestElfError("guest_elf_symbol_zero_invalid"));
    }
    let relocation_count = metadata.rela_size / RELA_ENTRY_BYTES;
    let mut seen_targets = BTreeSet::new();
    for index in 0..relocation_count {
        let entry_offset = index
            .checked_mul(RELA_ENTRY_BYTES)
            .and_then(|delta| table_offset.checked_add(delta))
            .ok_or(GuestElfError("guest_elf_relocation_table_mapping_invalid"))?;
        let entry_offset = usize::try_from(entry_offset)
            .map_err(|_| GuestElfError("guest_elf_relocation_table_mapping_invalid"))?;
        let target = read_u64(raw, entry_offset)?;
        let info = read_u64(raw, entry_offset + 8)?;
        let addend = read_i64(raw, entry_offset + 16)?;
        let symbol_index = info >> 32;
        let relocation_type = u32::try_from(info & u64::from(u32::MAX))
            .map_err(|_| GuestElfError("guest_elf_relocation_type_unsupported"))?;
        let expected_type = if index < metadata.relative_count {
            R_X86_64_RELATIVE
        } else {
            R_X86_64_IRELATIVE
        };
        if symbol_index != 0 {
            return Err(GuestElfError("guest_elf_relocation_symbol_invalid"));
        }
        if relocation_type != R_X86_64_RELATIVE && relocation_type != R_X86_64_IRELATIVE {
            return Err(GuestElfError("guest_elf_relocation_type_unsupported"));
        }
        if relocation_type != expected_type {
            return Err(GuestElfError("guest_elf_relocation_order_invalid"));
        }
        if !target.is_multiple_of(8)
            || !memory_range_in_single_load(target, 8, load_segments, PF_W)
            || address_ranges_overlap(target, 8, dynamic.virtual_address, dynamic.memory_size)?
        {
            return Err(GuestElfError("guest_elf_relocation_target_invalid"));
        }
        if !seen_targets.insert(target) {
            return Err(GuestElfError("guest_elf_relocation_target_duplicate"));
        }
        let addend = u64::try_from(addend).map_err(|_| relocation_addend_error(expected_type))?;
        let addend_valid = if expected_type == R_X86_64_IRELATIVE {
            file_range_in_single_load(addend, 1, load_segments, PF_R | PF_X)
        } else {
            memory_range_in_single_load(addend, 1, load_segments, 0)
        };
        if !addend_valid {
            return Err(relocation_addend_error(expected_type));
        }
    }
    Ok(())
}

fn relocation_addend_error(relocation_type: u32) -> GuestElfError {
    if relocation_type == R_X86_64_IRELATIVE {
        GuestElfError("guest_elf_irelative_resolver_invalid")
    } else {
        GuestElfError("guest_elf_relative_addend_invalid")
    }
}

fn map_virtual_file_range(
    address: u64,
    size: u64,
    load_segments: &[ProgramHeader],
    required_flags: u32,
    forbidden_flags: u32,
) -> Result<u64, GuestElfError> {
    let mut mapped_offset = None;
    for segment in load_segments {
        if segment.flags & required_flags != required_flags
            || segment.flags & forbidden_flags != 0
            || address < segment.virtual_address
        {
            continue;
        }
        let delta = address - segment.virtual_address;
        if delta <= segment.file_size && size <= segment.file_size - delta {
            let offset = segment
                .file_offset
                .checked_add(delta)
                .ok_or(GuestElfError("guest_elf_relocation_table_mapping_invalid"))?;
            if mapped_offset.replace(offset).is_some() {
                return Err(GuestElfError("guest_elf_relocation_table_mapping_invalid"));
            }
        }
    }
    mapped_offset.ok_or(GuestElfError("guest_elf_relocation_table_mapping_invalid"))
}

fn file_range_in_single_load(
    address: u64,
    size: u64,
    load_segments: &[ProgramHeader],
    required_flags: u32,
) -> bool {
    map_virtual_file_range(address, size, load_segments, required_flags, 0).is_ok()
}

fn memory_range_in_single_load(
    address: u64,
    size: u64,
    load_segments: &[ProgramHeader],
    required_flags: u32,
) -> bool {
    let mut matches = 0_u32;
    for segment in load_segments {
        if segment.flags & required_flags != required_flags || address < segment.virtual_address {
            continue;
        }
        let delta = address - segment.virtual_address;
        if delta <= segment.memory_size && size <= segment.memory_size - delta {
            matches += 1;
        }
    }
    matches == 1
}

fn address_ranges_overlap(
    left: u64,
    left_size: u64,
    right: u64,
    right_size: u64,
) -> Result<bool, GuestElfError> {
    let left_end = left
        .checked_add(left_size)
        .ok_or(GuestElfError("guest_elf_relocation_target_invalid"))?;
    let right_end = right
        .checked_add(right_size)
        .ok_or(GuestElfError("guest_elf_relocation_target_invalid"))?;
    Ok(left < right_end && right < left_end)
}

fn validate_gnu_stack(program_headers: &[ProgramHeader]) -> Result<(), GuestElfError> {
    let mut stack_count = 0_u32;
    let mut executable = false;
    for segment in program_headers {
        if segment.segment_type == PT_GNU_STACK {
            stack_count += 1;
            executable |= segment.flags & PF_X != 0;
        }
    }
    if stack_count != 1 || executable {
        Err(GuestElfError("guest_elf_gnu_stack_invalid"))
    } else {
        Ok(())
    }
}

fn range_within(offset: u64, size: u64, total: u64) -> bool {
    offset <= total && size <= total - offset
}

fn address_within(address: u64, start: u64, size: u64) -> bool {
    size > 0 && address >= start && address - start < size
}

fn contained_range(inner: u64, inner_size: u64, outer: u64, outer_size: u64) -> bool {
    inner >= outer && inner - outer <= outer_size && inner_size <= outer_size - (inner - outer)
}

fn page_ranges_overlap(left: &ProgramHeader, right: &ProgramHeader) -> Result<bool, GuestElfError> {
    let left_start = left.virtual_address / MEMORY_PAGE_BYTES;
    let right_start = right.virtual_address / MEMORY_PAGE_BYTES;
    let left_end = page_end(left.virtual_address, left.memory_size)?;
    let right_end = page_end(right.virtual_address, right.memory_size)?;
    Ok(left_start < right_end && right_start < left_end)
}

fn page_end(start: u64, size: u64) -> Result<u64, GuestElfError> {
    let end = start
        .checked_add(size)
        .ok_or(GuestElfError("guest_elf_load_geometry_invalid"))?;
    end.checked_add(MEMORY_PAGE_BYTES - 1)
        .map(|value| value / MEMORY_PAGE_BYTES)
        .ok_or(GuestElfError("guest_elf_load_geometry_invalid"))
}

fn read_u16(raw: &[u8], offset: usize) -> Result<u16, GuestElfError> {
    let bytes = read_array::<2>(raw, offset)?;
    Ok(u16::from_le_bytes(bytes))
}

fn read_u32(raw: &[u8], offset: usize) -> Result<u32, GuestElfError> {
    let bytes = read_array::<4>(raw, offset)?;
    Ok(u32::from_le_bytes(bytes))
}

fn read_u64(raw: &[u8], offset: usize) -> Result<u64, GuestElfError> {
    let bytes = read_array::<8>(raw, offset)?;
    Ok(u64::from_le_bytes(bytes))
}

fn read_i64(raw: &[u8], offset: usize) -> Result<i64, GuestElfError> {
    let bytes = read_array::<8>(raw, offset)?;
    Ok(i64::from_le_bytes(bytes))
}

fn read_array<const N: usize>(raw: &[u8], offset: usize) -> Result<[u8; N], GuestElfError> {
    let end = offset
        .checked_add(N)
        .ok_or(GuestElfError("guest_elf_structure_truncated"))?;
    let source = raw
        .get(offset..end)
        .ok_or(GuestElfError("guest_elf_structure_truncated"))?;
    let mut output = [0_u8; N];
    output.copy_from_slice(source);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_static_pie_profile_accepts() {
        assert_eq!(validate_guest_elf_bytes(&valid_elf()), Ok(()));
    }

    #[test]
    fn interpreter_and_needed_dependency_reject() {
        let mut interpreter = valid_elf();
        write_u32(&mut interpreter, 64 + 3 * 56, PT_INTERP);
        assert_eq!(
            validate_guest_elf_bytes(&interpreter),
            Err(GuestElfError("guest_elf_interpreter_present"))
        );

        let mut needed = valid_elf();
        write_i64(&mut needed, 0x400, DT_NEEDED);
        assert_eq!(
            validate_guest_elf_bytes(&needed),
            Err(GuestElfError("guest_elf_needed_dependency_present"))
        );
    }

    #[test]
    fn text_relocations_and_page_level_writable_executable_aliases_reject() {
        let mut textrel = valid_elf();
        write_i64(&mut textrel, 0x400, DT_TEXTREL);
        assert_eq!(
            validate_guest_elf_bytes(&textrel),
            Err(GuestElfError("guest_elf_text_relocation_present"))
        );

        let mut overlap = valid_elf();
        write_u64(&mut overlap, 64 + 2 * 56 + 16, 0x401400);
        assert_eq!(
            validate_guest_elf_bytes(&overlap),
            Err(GuestElfError("guest_elf_executable_writable_page_overlap"))
        );
    }

    #[test]
    fn dynamic_file_and_virtual_translation_must_be_unique_and_equal() {
        let mut mismatched = valid_elf();
        write_u64(&mut mismatched, 64 + 3 * 56 + 16, 0x4024a0);
        assert_eq!(
            validate_guest_elf_bytes(&mismatched),
            Err(GuestElfError("guest_elf_dynamic_segment_mapping_invalid"))
        );

        let mut ambiguous = valid_elf();
        write_u64(&mut ambiguous, 64 + 16, 0x402000);
        write_u64(&mut ambiguous, 64 + 32, 0x400);
        write_u64(&mut ambiguous, 64 + 40, 0x400);
        assert_eq!(
            validate_guest_elf_bytes(&ambiguous),
            Err(GuestElfError("guest_elf_load_bias_invalid"))
        );
    }

    #[test]
    fn entrypoint_and_program_headers_must_be_file_backed() {
        let mut bss_entrypoint = valid_elf();
        write_u64(&mut bss_entrypoint, 24, 0x401390);
        write_u64(&mut bss_entrypoint, 64 + 56 + 32, 0x80);
        assert_eq!(
            validate_guest_elf_bytes(&bss_entrypoint),
            Err(GuestElfError("guest_elf_entrypoint_invalid"))
        );

        let mut unmapped_headers = valid_elf();
        write_u64(&mut unmapped_headers, 64 + 32, 0x100);
        write_u64(&mut unmapped_headers, 64 + 40, 0x100);
        assert_eq!(
            validate_guest_elf_bytes(&unmapped_headers),
            Err(GuestElfError("guest_elf_program_headers_unmapped"))
        );
    }

    #[test]
    fn program_header_segment_must_be_unique_and_canonical() {
        let mut missing = valid_elf();
        write_program_header(&mut missing, 5, 0, 0, 0, 0, 0, 0, 0);
        assert_eq!(
            validate_guest_elf_bytes(&missing),
            Err(GuestElfError("guest_elf_program_header_segment_invalid"))
        );

        let mut duplicate = valid_elf();
        let table_size = 7 * u64::from(PROGRAM_HEADER_BYTES);
        write_program_header(
            &mut duplicate,
            6,
            PT_PHDR,
            PF_R,
            u64::from(ELF_HEADER_BYTES),
            u64::from(ELF_HEADER_BYTES),
            table_size,
            table_size,
            8,
        );
        assert_eq!(
            validate_guest_elf_bytes(&duplicate),
            Err(GuestElfError("guest_elf_program_header_segment_invalid"))
        );

        let mut malformed = valid_elf();
        write_u64(&mut malformed, 64 + 5 * 56 + 48, 16);
        assert_eq!(
            validate_guest_elf_bytes(&malformed),
            Err(GuestElfError("guest_elf_program_header_segment_invalid"))
        );
    }

    #[test]
    fn later_load_cannot_alias_dynamic_virtual_pages() {
        let mut aliased = valid_elf();
        aliased.resize(0x600, 0);
        write_program_header(
            &mut aliased,
            6,
            PT_LOAD,
            PF_R,
            0x500,
            0x402500,
            0x100,
            0x100,
            0x1000,
        );
        write_i64(&mut aliased, 0x400, DT_NEEDED);
        assert_eq!(
            validate_guest_elf_bytes(&aliased),
            Err(GuestElfError("guest_elf_load_mapping_invalid"))
        );
    }

    #[test]
    fn page_rounding_overflow_rejects() {
        let mut overflow = valid_elf();
        write_program_header(
            &mut overflow,
            6,
            PT_LOAD,
            PF_R | PF_W,
            0,
            0xffff_ffff_ffff_f000,
            0,
            0xfff,
            0x1000,
        );
        assert_eq!(
            validate_guest_elf_bytes(&overflow),
            Err(GuestElfError("guest_elf_load_geometry_invalid"))
        );
    }

    #[test]
    fn read_only_overflow_alias_and_bad_load_bias_reject() {
        let mut bad_alignment = valid_elf();
        write_u64(&mut bad_alignment, 64 + 56 + 48, 0x100);
        assert_eq!(
            validate_guest_elf_bytes(&bad_alignment),
            Err(GuestElfError("guest_elf_load_geometry_invalid"))
        );

        let mut overflow = valid_elf();
        write_program_header(
            &mut overflow,
            6,
            PT_LOAD,
            PF_R,
            0,
            0xffff_ffff_ffff_f000,
            0,
            0x1000,
            0x1000,
        );
        assert_eq!(
            validate_guest_elf_bytes(&overflow),
            Err(GuestElfError("guest_elf_load_geometry_invalid"))
        );

        let mut alias = valid_elf();
        write_program_header(
            &mut alias, 6, PT_LOAD, PF_R, 0x300, 0x401300, 0x100, 0x1000, 0x1000,
        );
        assert_eq!(
            validate_guest_elf_bytes(&alias),
            Err(GuestElfError("guest_elf_load_mapping_invalid"))
        );

        let mut duplicate_bias = valid_elf();
        write_program_header(
            &mut duplicate_bias,
            6,
            PT_LOAD,
            PF_R,
            0,
            0x500000,
            1,
            1,
            0x1000,
        );
        assert_eq!(
            validate_guest_elf_bytes(&duplicate_bias),
            Err(GuestElfError("guest_elf_load_bias_invalid"))
        );
    }

    #[test]
    fn governed_relocation_metadata_targets_and_resolvers_reject_mutations() {
        let mut bad_pointer = valid_elf();
        write_u64(&mut bad_pointer, 0x418, 0x500000);
        assert_eq!(
            validate_guest_elf_bytes(&bad_pointer),
            Err(GuestElfError("guest_elf_relocation_table_mapping_invalid"))
        );

        let mut rx_target = valid_elf();
        write_u64(&mut rx_target, 0x200, 0x401310);
        assert_eq!(
            validate_guest_elf_bytes(&rx_target),
            Err(GuestElfError("guest_elf_relocation_target_invalid"))
        );

        let mut dynamic_target = valid_elf();
        write_u64(&mut dynamic_target, 0x200, 0x402400);
        assert_eq!(
            validate_guest_elf_bytes(&dynamic_target),
            Err(GuestElfError("guest_elf_relocation_target_invalid"))
        );

        let mut bad_symbol = valid_elf();
        write_u64(
            &mut bad_symbol,
            0x208,
            (1_u64 << 32) | u64::from(R_X86_64_RELATIVE),
        );
        assert_eq!(
            validate_guest_elf_bytes(&bad_symbol),
            Err(GuestElfError("guest_elf_relocation_symbol_invalid"))
        );

        let mut bad_resolver = valid_elf();
        write_i64(&mut bad_resolver, 0x200 + 24 + 16, 0x402400);
        assert_eq!(
            validate_guest_elf_bytes(&bad_resolver),
            Err(GuestElfError("guest_elf_irelative_resolver_invalid"))
        );

        let mut bad_symbol_zero = valid_elf();
        bad_symbol_zero[0x1d0] = 1;
        assert_eq!(
            validate_guest_elf_bytes(&bad_symbol_zero),
            Err(GuestElfError("guest_elf_symbol_zero_invalid"))
        );
    }

    #[test]
    fn every_truncated_prefix_rejects_without_panic() {
        let raw = valid_elf();
        for length in 0..raw.len() {
            assert!(validate_guest_elf_bytes(&raw[..length]).is_err());
        }
    }

    fn valid_elf() -> Vec<u8> {
        let mut raw = vec![0_u8; 0x500];
        raw[0..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        write_u16(&mut raw, 16, ET_DYN);
        write_u16(&mut raw, 18, EM_X86_64);
        write_u32(&mut raw, 20, 1);
        write_u64(&mut raw, 24, 0x401310);
        write_u64(&mut raw, 32, 64);
        write_u16(&mut raw, 52, ELF_HEADER_BYTES);
        write_u16(&mut raw, 54, PROGRAM_HEADER_BYTES);
        write_u16(&mut raw, 56, 7);
        write_program_header(&mut raw, 0, PT_LOAD, PF_R, 0, 0, 0x300, 0x300, 0x1000);
        write_program_header(
            &mut raw,
            1,
            PT_LOAD,
            PF_R | PF_X,
            0x300,
            0x401300,
            0x100,
            0x100,
            0x1000,
        );
        write_program_header(
            &mut raw,
            2,
            PT_LOAD,
            PF_R | PF_W,
            0x400,
            0x402400,
            0x100,
            0x100,
            0x1000,
        );
        write_program_header(
            &mut raw,
            3,
            PT_DYNAMIC,
            PF_R | PF_W,
            0x400,
            0x402400,
            0x80,
            0x80,
            8,
        );
        write_program_header(&mut raw, 4, PT_GNU_STACK, PF_R | PF_W, 0, 0, 0, 0, 16);
        let program_header_table_size = 7 * u64::from(PROGRAM_HEADER_BYTES);
        write_program_header(
            &mut raw,
            5,
            PT_PHDR,
            PF_R,
            u64::from(ELF_HEADER_BYTES),
            u64::from(ELF_HEADER_BYTES),
            program_header_table_size,
            program_header_table_size,
            8,
        );
        write_program_header(&mut raw, 6, 0, 0, 0, 0, 0, 0, 0);
        write_dynamic_entry(&mut raw, 0, DT_FLAGS_1, DF_1_PIE);
        write_dynamic_entry(&mut raw, 1, DT_RELA, 0x200);
        write_dynamic_entry(&mut raw, 2, DT_RELASZ, 2 * RELA_ENTRY_BYTES);
        write_dynamic_entry(&mut raw, 3, DT_RELAENT, RELA_ENTRY_BYTES);
        write_dynamic_entry(&mut raw, 4, DT_RELACOUNT, 1);
        write_dynamic_entry(&mut raw, 5, DT_SYMTAB, 0x1d0);
        write_dynamic_entry(&mut raw, 6, DT_SYMENT, SYMBOL_ENTRY_BYTES);
        write_dynamic_entry(&mut raw, 7, DT_NULL, 0);
        write_rela_entry(
            &mut raw,
            0,
            0x402480,
            u64::from(R_X86_64_RELATIVE),
            0x401310,
        );
        write_rela_entry(
            &mut raw,
            1,
            0x402488,
            u64::from(R_X86_64_IRELATIVE),
            0x401320,
        );
        raw
    }

    fn write_dynamic_entry(raw: &mut [u8], index: usize, tag: i64, value: u64) {
        let offset = 0x400 + index * DYNAMIC_ENTRY_BYTES_USIZE;
        write_i64(raw, offset, tag);
        write_u64(raw, offset + 8, value);
    }

    fn write_rela_entry(raw: &mut [u8], index: usize, target: u64, info: u64, addend: i64) {
        let offset = 0x200 + index * RELA_ENTRY_BYTES_USIZE;
        write_u64(raw, offset, target);
        write_u64(raw, offset + 8, info);
        write_i64(raw, offset + 16, addend);
    }

    #[allow(clippy::too_many_arguments)]
    fn write_program_header(
        raw: &mut [u8],
        index: usize,
        segment_type: u32,
        flags: u32,
        file_offset: u64,
        virtual_address: u64,
        file_size: u64,
        memory_size: u64,
        alignment: u64,
    ) {
        let offset = 64 + index * 56;
        write_u32(raw, offset, segment_type);
        write_u32(raw, offset + 4, flags);
        write_u64(raw, offset + 8, file_offset);
        write_u64(raw, offset + 16, virtual_address);
        write_u64(raw, offset + 32, file_size);
        write_u64(raw, offset + 40, memory_size);
        write_u64(raw, offset + 48, alignment);
    }

    fn write_u16(raw: &mut [u8], offset: usize, value: u16) {
        raw[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
    }

    fn write_u32(raw: &mut [u8], offset: usize, value: u32) {
        raw[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    fn write_u64(raw: &mut [u8], offset: usize, value: u64) {
        raw[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }

    fn write_i64(raw: &mut [u8], offset: usize, value: i64) {
        raw[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }
}
