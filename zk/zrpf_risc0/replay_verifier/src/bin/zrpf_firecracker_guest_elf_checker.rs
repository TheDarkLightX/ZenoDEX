//! Bounded native validator for the ZRPF Firecracker guest ELF profile.

use std::ffi::OsStr;
use std::fs::{File, Metadata};
use std::io::{Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;

use rustix::fs::{Mode, OFlags};

const MAX_GUEST_ELF_BYTES: u64 = 16 * 1024 * 1024;
const MAX_PROGRAM_HEADERS: u16 = 128;
const MAX_DYNAMIC_ENTRIES: u64 = 4_096;
const ELF_HEADER_BYTES: u16 = 64;
const PROGRAM_HEADER_BYTES: u16 = 56;
const DYNAMIC_ENTRY_BYTES: u64 = 16;

const ET_DYN: u16 = 3;
const EM_X86_64: u16 = 62;
const PN_XNUM: u16 = 0xffff;

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;
const PT_GNU_STACK: u32 = 0x6474_e551;

const PF_X: u32 = 1;
const PF_W: u32 = 2;
const PF_R: u32 = 4;

const DT_NULL: i64 = 0;
const DT_NEEDED: i64 = 1;
const DT_TEXTREL: i64 = 22;
const DT_FLAGS: i64 = 30;
const DT_FLAGS_1: i64 = 0x6fff_fffb;
const DF_TEXTREL: u64 = 0x4;
const DF_1_PIE: u64 = 0x0800_0000;
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
    let load_segments = validate_segments(raw, &program_headers)?;
    validate_entry_point(entry_point, &load_segments)?;
    let dynamic = require_single_dynamic_segment(&program_headers)?;
    validate_dynamic_mapping(dynamic, &load_segments)?;
    validate_dynamic_entries(raw, dynamic)?;
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
    if table_offset < u64::from(ELF_HEADER_BYTES)
        || table_offset % 8 != 0
        || !range_within(table_offset, table_size, raw.len() as u64)
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
) -> Result<Vec<ProgramHeader>, GuestElfError> {
    let mut load_segments = Vec::new();
    for segment in program_headers {
        if segment.file_size != 0
            && !range_within(segment.file_offset, segment.file_size, raw.len() as u64)
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
        if segment.file_size > segment.memory_size
            || (segment.alignment > 1
                && segment.file_offset % segment.alignment
                    != segment.virtual_address % segment.alignment)
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

fn validate_entry_point(
    entry_point: u64,
    load_segments: &[ProgramHeader],
) -> Result<(), GuestElfError> {
    if load_segments.iter().any(|segment| {
        segment.flags & (PF_R | PF_X) == (PF_R | PF_X)
            && address_within(entry_point, segment.virtual_address, segment.memory_size)
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
        || dynamic.file_size % DYNAMIC_ENTRY_BYTES != 0
        || dynamic.file_offset % 8 != 0
        || dynamic.virtual_address % 8 != 0
        || dynamic.file_size > dynamic.memory_size
    {
        return Err(GuestElfError("guest_elf_dynamic_segment_geometry_invalid"));
    }
    if load_segments.iter().any(|load| {
        load.flags & PF_R != 0
            && contained_range(
                dynamic.file_offset,
                dynamic.file_size,
                load.file_offset,
                load.file_size,
            )
            && contained_range(
                dynamic.virtual_address,
                dynamic.memory_size,
                load.virtual_address,
                load.memory_size,
            )
    }) {
        Ok(())
    } else {
        Err(GuestElfError("guest_elf_dynamic_segment_mapping_invalid"))
    }
}

fn validate_dynamic_entries(raw: &[u8], dynamic: ProgramHeader) -> Result<(), GuestElfError> {
    let entry_count = dynamic.file_size / DYNAMIC_ENTRY_BYTES;
    let mut saw_null = false;
    let mut flags_1_count = 0_u64;
    let mut flags_1_value = 0_u64;
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
        }
    }
    if !saw_null {
        return Err(GuestElfError("guest_elf_dynamic_terminator_invalid"));
    }
    if flags_1_count != 1 || flags_1_value & DF_1_PIE == 0 {
        return Err(GuestElfError("guest_elf_df_1_pie_missing"));
    }
    Ok(())
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
        write_i64(&mut needed, 0x280, DT_NEEDED);
        assert_eq!(
            validate_guest_elf_bytes(&needed),
            Err(GuestElfError("guest_elf_needed_dependency_present"))
        );
    }

    #[test]
    fn text_relocations_and_page_level_writable_executable_aliases_reject() {
        let mut textrel = valid_elf();
        write_i64(&mut textrel, 0x280, DT_TEXTREL);
        assert_eq!(
            validate_guest_elf_bytes(&textrel),
            Err(GuestElfError("guest_elf_text_relocation_present"))
        );

        let mut overlap = valid_elf();
        write_u64(&mut overlap, 64 + 2 * 56 + 16, 0x401200);
        assert_eq!(
            validate_guest_elf_bytes(&overlap),
            Err(GuestElfError("guest_elf_executable_writable_page_overlap"))
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
        let mut raw = vec![0_u8; 0x400];
        raw[0..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        write_u16(&mut raw, 16, ET_DYN);
        write_u16(&mut raw, 18, EM_X86_64);
        write_u32(&mut raw, 20, 1);
        write_u64(&mut raw, 24, 0x401310);
        write_u64(&mut raw, 32, 64);
        write_u16(&mut raw, 52, ELF_HEADER_BYTES);
        write_u16(&mut raw, 54, PROGRAM_HEADER_BYTES);
        write_u16(&mut raw, 56, 5);
        write_program_header(
            &mut raw, 0, PT_LOAD, PF_R, 0, 0x400000, 0x300, 0x300, 0x1000,
        );
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
            0x200,
            0x402200,
            0x100,
            0x100,
            0x1000,
        );
        write_program_header(
            &mut raw,
            3,
            PT_DYNAMIC,
            PF_R | PF_W,
            0x280,
            0x402280,
            0x20,
            0x20,
            8,
        );
        write_program_header(&mut raw, 4, PT_GNU_STACK, PF_R | PF_W, 0, 0, 0, 0, 16);
        write_i64(&mut raw, 0x280, DT_FLAGS_1);
        write_u64(&mut raw, 0x288, DF_1_PIE);
        write_i64(&mut raw, 0x290, DT_NULL);
        raw
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
