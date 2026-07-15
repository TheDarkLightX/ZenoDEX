"""Fixed-ABI witnesses for the pinned privileged Linux netns helper."""

from __future__ import annotations

import copy
import hashlib
import os
import pickle
import signal
import struct
import subprocess
from pathlib import Path
from typing import cast

import pytest

from tools import zrpf_firecracker_linux_netns_process as helper_process
from tools import zrpf_spot_v7_firecracker_linux_netns_adapter as adapter
from tools.zrpf_v3_firecracker_netns import PinnedNetworkNamespaceV1
from tools.zrpf_v3_firecracker_trusted_runtime import _OpenedIdentityV1

DEVICE = 0x0102030405060708
INODE = 0x1112131415161718


def _fixture_request() -> bytes:
    return adapter._encode_request_v1(
        operation=adapter.NetnsHelperOperationV1.INSPECT,
        namespace_root=Path("/run/zenodex-netns-A7"),
        namespace_name="run3b941x",
        expected_device=DEVICE,
        expected_inode=INODE,
    )


def _response_for(request: bytes) -> bytes:
    operation = int.from_bytes(request[18:20], "big")
    expected_device = int.from_bytes(request[32:40], "big")
    expected_inode = int.from_bytes(request[40:48], "big")
    if operation == int(adapter.NetnsHelperOperationV1.CREATE):
        expected_device = DEVICE
        expected_inode = INODE
    root_length = int.from_bytes(request[28:30], "big")
    name_length = int.from_bytes(request[30:32], "big")
    root = request[48 : 48 + root_length]
    name = request[304 : 304 + name_length]
    response = bytearray(adapter.NETNS_HELPER_RESPONSE_BYTES_V1)
    response[0:16] = b"ZRPFLNXNSRESV1!!"
    response[16:18] = (1).to_bytes(2, "big")
    response[18:20] = operation.to_bytes(2, "big")
    response[20:22] = (1).to_bytes(2, "big")
    response[22:24] = (0).to_bytes(2, "big")
    response[24:28] = (0).to_bytes(4, "big")
    response[28:32] = (0).to_bytes(4, "big")
    response[32:40] = expected_device.to_bytes(8, "big")
    response[40:48] = expected_inode.to_bytes(8, "big")
    if operation in (1, 2):
        response[60] = 0
        response[61] = 1
    else:
        response[60] = 1
        response[61] = 0
    response[64:96] = hashlib.sha256(request).digest()
    response[96:128] = hashlib.sha256(root).digest()
    response[128:160] = hashlib.sha256(name).digest()
    response[224:256] = hashlib.sha256(response[:224]).digest()
    return bytes(response)


def test_position_distinct_fixture_round_trips_exact_result_bindings() -> None:
    request = _fixture_request()
    assert len(request) == adapter.NETNS_HELPER_REQUEST_BYTES_V1
    assert hashlib.sha256(request).hexdigest() == (
        "4eaca7fc26901d5232b991b27ac0d79e1209ed8e482971542d25af7566b4561e"
    )
    parsed = adapter._parse_response_v1(
        _response_for(request),
        request=request,
        expected_operation=adapter.NetnsHelperOperationV1.INSPECT,
        expected_device=DEVICE,
        expected_inode=INODE,
    )
    assert parsed.device == DEVICE
    assert parsed.inode == INODE
    assert parsed.mount_present is True
    assert parsed.path_absent is False


@pytest.mark.parametrize(
    "offset",
    (
        0,
        16,
        18,
        20,
        22,
        24,
        28,
        32,
        40,
        48,
        52,
        56,
        60,
        61,
        62,
        64,
        96,
        128,
        160,
        224,
    ),
)
def test_every_result_field_position_has_an_active_mutation_witness(offset: int) -> None:
    request = _fixture_request()
    mutated = bytearray(_response_for(request))
    mutated[offset] ^= 1
    if offset < 224:
        mutated[224:256] = hashlib.sha256(mutated[:224]).digest()

    with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
        adapter._parse_response_v1(
            bytes(mutated),
            request=request,
            expected_operation=adapter.NetnsHelperOperationV1.INSPECT,
            expected_device=DEVICE,
            expected_inode=INODE,
        )


def test_result_truncation_extension_and_endian_substitution_reject() -> None:
    request = _fixture_request()
    response = _response_for(request)
    cases = [response[:-1], response + b"\x00"]
    endian = bytearray(response)
    endian[32:40] = DEVICE.to_bytes(8, "little")
    endian[224:256] = hashlib.sha256(endian[:224]).digest()
    cases.append(bytes(endian))

    for case in cases:
        with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
            adapter._parse_response_v1(
                case,
                request=request,
                expected_operation=adapter.NetnsHelperOperationV1.INSPECT,
                expected_device=DEVICE,
                expected_inode=INODE,
            )


def test_every_result_reserved_flag_and_digest_bit_is_a_rejecting_witness() -> None:
    request = _fixture_request()
    accepted = _response_for(request)
    for byte_index in (*range(22, 32), *range(62, 64), *range(160, 224)):
        for bit in range(8):
            mutated = bytearray(accepted)
            mutated[byte_index] ^= 1 << bit
            mutated[224:256] = hashlib.sha256(mutated[:224]).digest()
            _assert_response_rejected(bytes(mutated), request)
    for byte_index in range(224, 256):
        for bit in range(8):
            mutated = bytearray(accepted)
            mutated[byte_index] ^= 1 << bit
            _assert_response_rejected(bytes(mutated), request)


def test_every_result_tag_binding_count_and_identity_byte_is_observable() -> None:
    request = _fixture_request()
    accepted = _response_for(request)
    active_ranges = (
        range(0, 22),
        range(32, 62),
        range(64, 160),
    )
    for byte_index in (index for values in active_ranges for index in values):
        mutated = bytearray(accepted)
        mutated[byte_index] ^= 1
        mutated[224:256] = hashlib.sha256(mutated[:224]).digest()
        _assert_response_rejected(bytes(mutated), request)


def test_exact_boolean_tags_and_position_swaps_reject() -> None:
    request = _fixture_request()
    accepted = _response_for(request)
    for offset in (60, 61):
        for invalid in (2, 127, 255):
            mutated = bytearray(accepted)
            mutated[offset] = invalid
            mutated[224:256] = hashlib.sha256(mutated[:224]).digest()
            _assert_response_rejected(bytes(mutated), request)

    swapped_identity = bytearray(accepted)
    swapped_identity[32:40], swapped_identity[40:48] = (
        swapped_identity[40:48],
        swapped_identity[32:40],
    )
    swapped_identity[224:256] = hashlib.sha256(swapped_identity[:224]).digest()
    _assert_response_rejected(bytes(swapped_identity), request)

    swapped_bindings = bytearray(accepted)
    swapped_bindings[96:128], swapped_bindings[128:160] = (
        swapped_bindings[128:160],
        swapped_bindings[96:128],
    )
    swapped_bindings[224:256] = hashlib.sha256(swapped_bindings[:224]).digest()
    _assert_response_rejected(bytes(swapped_bindings), request)


@pytest.mark.parametrize("operation", tuple(adapter.NetnsHelperOperationV1))
def test_every_operation_tag_has_an_accepting_distinguishing_witness(
    operation: adapter.NetnsHelperOperationV1,
) -> None:
    requires_identity = operation in {
        adapter.NetnsHelperOperationV1.INSPECT,
        adapter.NetnsHelperOperationV1.DESTROY,
        adapter.NetnsHelperOperationV1.ABSENCE,
    }
    device, inode = (DEVICE, INODE) if requires_identity else (0, 0)
    request = adapter._encode_request_v1(
        operation=operation,
        namespace_root=Path("/run/zenodex-netns-A7"),
        namespace_name="run3b941x",
        expected_device=device,
        expected_inode=inode,
    )
    parsed = adapter._parse_response_v1(
        _response_for(request),
        request=request,
        expected_operation=operation,
        expected_device=device,
        expected_inode=inode,
    )
    assert parsed.operation is operation


def test_adapter_routes_each_effect_once_and_keeps_every_authority_false(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[bytes] = []

    def execute_once(*, executable: Path, expected_sha256: str, request: bytes) -> bytes:
        assert executable == Path("/opt/zenodex/bin/zrpf-netns-helper")
        assert expected_sha256 == "a7" * 32
        calls.append(request)
        return _response_for(request)

    monkeypatch.setattr(adapter.os, "geteuid", lambda: 0)
    monkeypatch.setattr(adapter, "execute_pinned_helper_once", execute_once)
    kernel = adapter.PinnedLinuxSpotV7NetworkNamespaceKernelV1(
        executable=Path("/opt/zenodex/bin/zrpf-netns-helper"),
        expected_sha256="a7" * 32,
    )
    root = Path("/run/zenodex-netns-A7")
    name = "run3b941x"
    path = root / name
    namespace = PinnedNetworkNamespaceV1(
        path=path,
        identity=_OpenedIdentityV1(
            parent_fd=-1,
            file_fd=-1,
            file_name=name,
            device=DEVICE,
            inode=INODE,
        ),
        proc_root=Path("/proc"),
        trusted_uid=0,
    )

    kernel.create_fresh_namespace_mount(
        namespace_root=root,
        namespace_name=name,
        trusted_uid=0,
    )
    kernel.require_empty_network_inventory(namespace)
    kernel.destroy_exact_namespace_mount(namespace)
    kernel.require_namespace_mount_absent(namespace_path=path, trusted_uid=0)
    kernel.cleanup_unopened_namespace_mount(
        namespace_path=root / "partial99",
        trusted_uid=0,
    )

    assert [int.from_bytes(call[18:20], "big") for call in calls] == [1, 2, 3, 5, 4]
    assert kernel.live_execution_verified is False
    assert kernel.runtime_authority is False
    assert kernel.release_authority is False
    assert kernel.settlement_authority is False
    assert kernel.production_authority is False
    with pytest.raises(TypeError):
        copy.copy(kernel)
    with pytest.raises(TypeError):
        copy.deepcopy(kernel)
    with pytest.raises(TypeError):
        pickle.dumps(kernel)


def test_adapter_rejects_untracked_or_reused_namespace_identity(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[bytes] = []

    def execute_once(*, executable: Path, expected_sha256: str, request: bytes) -> bytes:
        del executable, expected_sha256
        calls.append(request)
        return _response_for(request)

    monkeypatch.setattr(adapter.os, "geteuid", lambda: 0)
    monkeypatch.setattr(adapter, "execute_pinned_helper_once", execute_once)
    kernel = adapter.PinnedLinuxSpotV7NetworkNamespaceKernelV1(
        executable=Path("/opt/zenodex/bin/zrpf-netns-helper"),
        expected_sha256="a7" * 32,
    )
    root = Path("/run/zenodex-netns-A7")
    name = "run3b941x"
    path = root / name
    namespace = PinnedNetworkNamespaceV1(
        path=path,
        identity=_OpenedIdentityV1(
            parent_fd=-1,
            file_fd=-1,
            file_name=name,
            device=DEVICE,
            inode=INODE,
        ),
        proc_root=Path("/proc"),
        trusted_uid=0,
    )

    with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
        kernel.require_empty_network_inventory(namespace)
    assert calls == []

    kernel.create_fresh_namespace_mount(
        namespace_root=root,
        namespace_name=name,
        trusted_uid=0,
    )
    with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
        kernel.create_fresh_namespace_mount(
            namespace_root=root,
            namespace_name=name,
            trusted_uid=0,
        )
    with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
        kernel.cleanup_unopened_namespace_mount(
            namespace_path=path,
            trusted_uid=0,
        )
    assert len(calls) == 1


def test_process_group_is_killed_even_after_leader_exit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    killed: list[tuple[int, signal.Signals]] = []

    class ExitedLeader:
        pid = 701

        def poll(self) -> int:
            return 0

        def wait(self, *, timeout: int) -> int:
            assert timeout == 1
            return 0

    monkeypatch.setattr(
        helper_process.os,
        "killpg",
        lambda pid, sig: killed.append((pid, sig)),
    )
    helper_process._terminate_process_group(
        cast("subprocess.Popen[bytes]", ExitedLeader())
    )
    assert killed == [(701, signal.SIGKILL)]


def test_static_elf_gate_accepts_no_interpreter_and_rejects_interp_or_needed(
    tmp_path: Path,
) -> None:
    accepted = tmp_path / "accepted.elf"
    accepted.write_bytes(_elf_fixture(program_type=1, dynamic_tag=0))
    with accepted.open("rb") as stream:
        helper_process._require_static_host_elf(stream.fileno())

    for name, program_type, dynamic_tag in (
        ("interp.elf", 3, 0),
        ("needed.elf", 2, 1),
    ):
        rejected = tmp_path / name
        rejected.write_bytes(
            _elf_fixture(program_type=program_type, dynamic_tag=dynamic_tag)
        )
        with rejected.open("rb") as stream:
            with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
                helper_process._require_static_host_elf(stream.fileno())


def _assert_response_rejected(response: bytes, request: bytes) -> None:
    with pytest.raises(adapter.LinuxNetnsAdapterRejectedV1):
        adapter._parse_response_v1(
            response,
            request=request,
            expected_operation=adapter.NetnsHelperOperationV1.INSPECT,
            expected_device=DEVICE,
            expected_inode=INODE,
        )


def _elf_fixture(*, program_type: int, dynamic_tag: int) -> bytes:
    header = bytearray(64)
    header[0:6] = b"\x7fELF\x02\x01"
    header[18:20] = (62 if os.uname().machine == "x86_64" else 183).to_bytes(
        2, "little"
    )
    header[32:40] = (64).to_bytes(8, "little")
    header[54:56] = (56).to_bytes(2, "little")
    header[56:58] = (1).to_bytes(2, "little")
    program = bytearray(56)
    program[0:4] = program_type.to_bytes(4, "little")
    program[8:16] = (120).to_bytes(8, "little")
    program[32:40] = (16).to_bytes(8, "little")
    dynamic = struct.pack("<qQ", dynamic_tag, 0)
    return bytes(header + program + dynamic)
