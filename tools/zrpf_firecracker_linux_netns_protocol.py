"""Exact fixed binary protocol for the privileged Linux netns helper."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import IntEnum, StrEnum
from pathlib import Path

NETNS_HELPER_REQUEST_BYTES_V1 = 512
NETNS_HELPER_RESPONSE_BYTES_V1 = 256
_REQUEST_MAGIC_V1 = b"ZRPFLNXNSREQV1!!"
_RESPONSE_MAGIC_V1 = b"ZRPFLNXNSRESV1!!"
_PROTOCOL_VERSION_V1 = 1


class NetnsHelperOperationV1(IntEnum):
    CREATE = 1
    INSPECT = 2
    DESTROY = 3
    CLEANUP = 4
    ABSENCE = 5


class LinuxNetnsAdapterRejectV1(StrEnum):
    REQUEST_INVALID = "request_invalid"
    EXECUTABLE_INVALID = "executable_invalid"
    EXECUTABLE_HASH_MISMATCH = "executable_hash_mismatch"
    PROCESS_FAILED = "process_failed"
    PROCESS_TIMEOUT = "process_timeout"
    RESPONSE_INVALID = "response_invalid"
    BINDING_MISMATCH = "binding_mismatch"
    NOT_ROOT = "not_root"


class LinuxNetnsAdapterRejectedV1(RuntimeError):
    def __init__(self, code: LinuxNetnsAdapterRejectV1) -> None:
        self.code = code
        super().__init__(code.value)


@dataclass(frozen=True, slots=True)
class ParsedNetnsHelperResponseV1:
    operation: NetnsHelperOperationV1
    device: int
    inode: int
    path_absent: bool
    mount_present: bool


def encode_request_v1(
    *,
    operation: NetnsHelperOperationV1,
    namespace_root: Path,
    namespace_name: str,
    expected_device: int,
    expected_inode: int,
) -> bytes:
    if type(operation) is not NetnsHelperOperationV1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    root_bytes = canonical_root_bytes(namespace_root)
    name_bytes = canonical_name_bytes(namespace_name)
    validate_identity(operation, expected_device, expected_inode)
    request = bytearray(NETNS_HELPER_REQUEST_BYTES_V1)
    request[0:16] = _REQUEST_MAGIC_V1
    request[16:18] = _PROTOCOL_VERSION_V1.to_bytes(2, "big")
    request[18:20] = int(operation).to_bytes(2, "big")
    request[28:30] = len(root_bytes).to_bytes(2, "big")
    request[30:32] = len(name_bytes).to_bytes(2, "big")
    request[32:40] = expected_device.to_bytes(8, "big")
    request[40:48] = expected_inode.to_bytes(8, "big")
    request[48 : 48 + len(root_bytes)] = root_bytes
    request[304 : 304 + len(name_bytes)] = name_bytes
    request[480:512] = hashlib.sha256(request[:480]).digest()
    return bytes(request)


def parse_response_v1(
    raw: bytes,
    *,
    request: bytes,
    expected_operation: NetnsHelperOperationV1,
    expected_device: int,
    expected_inode: int,
) -> ParsedNetnsHelperResponseV1:
    if type(expected_operation) is not NetnsHelperOperationV1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    validate_identity(expected_operation, expected_device, expected_inode)
    _require_response_frame(raw, request)
    if u16(raw, 18) != int(expected_operation) or u16(raw, 20) != 1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
    if u16(raw, 22) != 0 or u32(raw, 24) != 0 or u32(raw, 28) != 0:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    if any(raw[62:64]) or any(raw[160:224]):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    if raw[224:256] != hashlib.sha256(raw[:224]).digest():
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    _require_request_bindings(raw, request)
    if u32(raw, 48) != 0 or u32(raw, 52) != 0 or u32(raw, 56) != 0:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    path_absent = exact_bool(raw[60])
    mount_present = exact_bool(raw[61])
    should_be_present = expected_operation in {
        NetnsHelperOperationV1.CREATE,
        NetnsHelperOperationV1.INSPECT,
    }
    if (
        mount_present != should_be_present
        or path_absent == should_be_present
        or path_absent == mount_present
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    device = u64(raw, 32)
    inode = u64(raw, 40)
    if should_be_present and (device == 0 or inode == 0):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    if expected_operation in {
        NetnsHelperOperationV1.INSPECT,
        NetnsHelperOperationV1.DESTROY,
        NetnsHelperOperationV1.ABSENCE,
    } and (expected_device or expected_inode):
        if (device, inode) != (expected_device, expected_inode):
            raise LinuxNetnsAdapterRejectedV1(
                LinuxNetnsAdapterRejectV1.BINDING_MISMATCH
            )
    return ParsedNetnsHelperResponseV1(
        operation=expected_operation,
        device=device,
        inode=inode,
        path_absent=path_absent,
        mount_present=mount_present,
    )


def canonical_root_bytes(value: Path) -> bytes:
    if not isinstance(value, Path) or not value.is_absolute():
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    text = str(value)
    try:
        raw = text.encode("ascii", errors="strict")
    except UnicodeEncodeError as exc:
        raise LinuxNetnsAdapterRejectedV1(
            LinuxNetnsAdapterRejectV1.REQUEST_INVALID
        ) from exc
    if (
        text == "/"
        or text.endswith("/")
        or len(raw) > 256
        or any(component in {"", ".", ".."} for component in text[1:].split("/"))
        or any(
            not (
                character.isascii()
                and (character.isalnum() or character in "-_.")
            )
            for component in text[1:].split("/")
            for character in component
        )
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    return raw


def canonical_name_bytes(value: str) -> bytes:
    if type(value) is not str:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    try:
        raw = value.encode("ascii", errors="strict")
    except UnicodeEncodeError as exc:
        raise LinuxNetnsAdapterRejectedV1(
            LinuxNetnsAdapterRejectV1.REQUEST_INVALID
        ) from exc
    if (
        not 8 <= len(raw) <= 64
        or not ord("a") <= raw[0] <= ord("z")
        or any(
            not (
                byte == ord("-")
                or ord("a") <= byte <= ord("z")
                or ord("0") <= byte <= ord("9")
            )
            for byte in raw
        )
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    return raw


def validate_identity(
    operation: NetnsHelperOperationV1,
    device: int,
    inode: int,
) -> None:
    if type(device) is not int or type(inode) is not int:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    if not 0 <= device <= (1 << 64) - 1 or not 0 <= inode <= (1 << 64) - 1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    both_zero = device == 0 and inode == 0
    both_present = device > 0 and inode > 0
    if operation in {NetnsHelperOperationV1.CREATE, NetnsHelperOperationV1.CLEANUP}:
        valid = both_zero
    elif operation in {NetnsHelperOperationV1.INSPECT, NetnsHelperOperationV1.DESTROY}:
        valid = both_present
    else:
        valid = both_zero or both_present
    if not valid:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)


def _require_response_frame(raw: bytes, request: bytes) -> None:
    if type(raw) is not bytes or len(raw) != NETNS_HELPER_RESPONSE_BYTES_V1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    if type(request) is not bytes or len(request) != NETNS_HELPER_REQUEST_BYTES_V1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    if raw[0:16] != _RESPONSE_MAGIC_V1 or u16(raw, 16) != _PROTOCOL_VERSION_V1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)


def _require_request_bindings(raw: bytes, request: bytes) -> None:
    root_length = int.from_bytes(request[28:30], "big")
    name_length = int.from_bytes(request[30:32], "big")
    if raw[64:96] != hashlib.sha256(request).digest():
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
    if raw[96:128] != hashlib.sha256(request[48 : 48 + root_length]).digest():
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
    if raw[128:160] != hashlib.sha256(request[304 : 304 + name_length]).digest():
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)


def exact_bool(value: int) -> bool:
    if value not in (0, 1):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    return bool(value)


def u16(raw: bytes, offset: int) -> int:
    return int.from_bytes(raw[offset : offset + 2], "big")


def u32(raw: bytes, offset: int) -> int:
    return int.from_bytes(raw[offset : offset + 4], "big")


def u64(raw: bytes, offset: int) -> int:
    return int.from_bytes(raw[offset : offset + 8], "big")
