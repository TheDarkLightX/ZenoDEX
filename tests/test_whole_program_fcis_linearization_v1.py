"""FCIS regressions for descriptor ownership and artifact linearization.

These tests retain the ACE4E0C55 external counterexamples as repository evidence.
They exercise exact ownership-transfer lines, repeated failures, pure Markdown
preflight, and every replacement fault point around the rename linearization.
"""

from __future__ import annotations

import hashlib
import inspect
import json
import os
import stat
import sys
from collections.abc import Callable, Iterable
from pathlib import Path
from types import FrameType
from typing import Any, cast

import pytest

from tools import check_whole_program_plan_v1 as checker
from tools import live_gate_registry_v1 as registry
from tools import whole_program_artifact_binding_v1 as binding

ROOT = Path(__file__).resolve().parents[1]
HISTORICAL_PACKET = Path(
    "tests/evidence/test_hygiene/THV1-20260826-whole-program-assurance-checker.json"
)
SUCCESSOR_PACKET = Path(
    "tests/evidence/test_hygiene/THV1-20260826-z-whole-program-assurance-checker-fcis-linearization.json"
)
CURRENT_PACKET = Path(
    "tests/evidence/test_hygiene/THV1-20260826-zz-whole-program-assurance-checker-admission-repair.json"
)
HISTORICAL_PACKET_SHA256 = (
    "90d9833f3a8e569b5941894e6e0aeab06906722b42ade7264f3cb2cb8c9e0a3b"
)
PathArg = str | bytes | os.PathLike[str] | os.PathLike[bytes]


def _plan() -> dict[str, Any]:
    value = json.loads((ROOT / checker.PLAN_JSON_PATH).read_text(encoding="utf-8"))
    assert type(value) is dict
    return value


def _open_fds() -> frozenset[int]:
    return frozenset(int(name) for name in os.listdir("/proc/self/fd"))


def _close_raw(descriptors: Iterable[int]) -> None:
    for descriptor in descriptors:
        try:
            os.close(descriptor)
        except OSError:
            pass


def _line_containing(function: Callable[..., object], needle: str) -> int:
    lines, first = inspect.getsourcelines(function)
    matches = [first + index for index, line in enumerate(lines) if needle in line]
    assert len(matches) == 1, (function.__qualname__, needle, matches)
    return matches[0]


def _raise_at_line(
    function: Callable[..., object],
    needle: str,
    action: Callable[[], object],
    failure_type: type[BaseException] = MemoryError,
) -> None:
    target = _line_containing(function, needle)
    code = function.__code__

    def trace(frame: FrameType, event: str, _arg: object) -> Any:
        if frame.f_code is code and event == "line" and frame.f_lineno == target:
            raise failure_type(f"injected at {function.__qualname__}:{target}")
        return trace

    previous = sys.gettrace()
    sys.settrace(trace)
    try:
        action()
    finally:
        sys.settrace(previous)


def test_root_traversal_close_failure_unwinds_predecessor_and_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """AAA/RIPR: a failed handoff leaves no predecessor or successor descriptor."""

    real_open = os.open
    real_close = os.close
    initial: int | None = None
    failed = False

    def recording_open(
        path: PathArg,
        flags: int,
        mode: int = 0o777,
        *,
        dir_fd: int | None = None,
    ) -> int:
        nonlocal initial
        descriptor = real_open(path, flags, mode, dir_fd=dir_fd)
        if path == "/":
            initial = descriptor
        return descriptor

    def fail_initial_once(descriptor: int) -> None:
        nonlocal failed
        if descriptor == initial and not failed:
            failed = True
            raise OSError("injected predecessor close failure")
        real_close(descriptor)

    monkeypatch.setattr(registry.os, "open", recording_open)
    monkeypatch.setattr(registry.os, "close", fail_initial_once)
    before = _open_fds()
    try:
        with pytest.raises(OSError, match="predecessor close failure"):
            registry.AnchoredDirectoryV1.open(ROOT)
        monkeypatch.setattr(registry.os, "close", real_close)
        assert _open_fds() == before
    finally:
        monkeypatch.setattr(registry.os, "close", real_close)
        _close_raw(_open_fds() - before)


def test_subtree_close_failure_unwinds_predecessor_and_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """AAA/RIPR: duplicated predecessor and opened successor stay co-owned."""

    root = registry.AnchoredDirectoryV1.open(ROOT)
    real_dup = os.dup
    real_close = os.close
    predecessor: int | None = None
    failed = False

    def recording_dup(descriptor: int) -> int:
        nonlocal predecessor
        predecessor = real_dup(descriptor)
        return predecessor

    def fail_predecessor_once(descriptor: int) -> None:
        nonlocal failed
        if descriptor == predecessor and not failed:
            failed = True
            raise OSError("injected subtree predecessor close failure")
        real_close(descriptor)

    monkeypatch.setattr(registry.os, "dup", recording_dup)
    monkeypatch.setattr(registry.os, "close", fail_predecessor_once)
    before = _open_fds()
    try:
        with pytest.raises(OSError, match="subtree predecessor close failure"):
            root.walk(("tools", "bounded_json_v1.py"))
        monkeypatch.setattr(registry.os, "close", real_close)
        assert _open_fds() == before
    finally:
        monkeypatch.setattr(registry.os, "close", real_close)
        _close_raw(_open_fds() - before)
        root.close()


def test_open_entry_finalizer_failure_unwinds_directory_and_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """AAA/RIPR: a failed directory finalizer cannot discard an open return value."""

    root = registry.AnchoredDirectoryV1.open(ROOT)
    real_walk = registry.AnchoredDirectoryV1.walk
    real_close = os.close
    directory: int | None = None
    failed = False

    def recording_walk(
        self: registry.AnchoredDirectoryV1, parts: tuple[str, ...]
    ) -> int:
        nonlocal directory
        directory = real_walk(self, parts)
        return directory

    def fail_directory_once(descriptor: int) -> None:
        nonlocal failed
        if descriptor == directory and not failed:
            failed = True
            raise OSError("injected directory finalizer failure")
        real_close(descriptor)

    monkeypatch.setattr(registry.AnchoredDirectoryV1, "walk", recording_walk)
    monkeypatch.setattr(registry.os, "close", fail_directory_once)
    before = _open_fds()
    try:
        with pytest.raises(OSError, match="directory finalizer failure"):
            root.open_entry(("tools", "bounded_json_v1.py"), os.O_RDONLY)
        monkeypatch.setattr(registry.os, "close", real_close)
        assert _open_fds() == before
    finally:
        monkeypatch.setattr(registry.os, "close", real_close)
        _close_raw(_open_fds() - before)
        root.close()


def test_effect_list_allocation_precedes_execution_context_acquisition() -> None:
    """AAA/RIPR: allocation failure occurs before four artifact fds are acquired."""

    with checker.ConfinedRootV1.bind(ROOT) as root:
        before = _open_fds()
        with pytest.raises(MemoryError, match="injected at _plan_effects"):
            _raise_at_line(
                checker._plan_effects,
                "effects: list[LiveGateEffectV1] = []",
                lambda: checker.plan_live_gate_effects_v1(
                    _plan()["live_gates"], root
                ),
            )
        assert _open_fds() == before


def test_open_file_initialization_precedes_source_acquisition(tmp_path: Path) -> None:
    """AAA/RIPR: source ownership starts inside the aggregate cleanup region."""

    source = tmp_path / "source.py"
    source.write_text("print('owned')\n", encoding="utf-8")
    root = registry.AnchoredDirectoryV1.open(tmp_path)
    before = _open_fds()
    try:
        with pytest.raises(KeyboardInterrupt, match="injected at AnchoredDirectoryV1.open_file"):
            _raise_at_line(
                registry.AnchoredDirectoryV1.open_file,
                "sealed: int | None = None",
                lambda: root.open_file(source.name),
                KeyboardInterrupt,
            )
        assert _open_fds() == before
    finally:
        root.close()


def test_ad_hoc_root_ownership_is_declared_before_binding() -> None:
    """AAA/RIPR: interruption at ownership declaration precedes root acquisition."""

    use_root = checker._UseRoot(ROOT)
    before = _open_fds()
    with pytest.raises(KeyboardInterrupt, match="injected at _UseRoot.__enter__"):
        _raise_at_line(
            checker._UseRoot.__enter__,
            "self.owned = True",
            use_root.__enter__,
            KeyboardInterrupt,
        )
    assert _open_fds() == before


def test_artifact_aggregate_return_failure_unwinds_every_source() -> None:
    """AAA/RIPR: aggregate ownership remains local through the return expression."""

    root = registry.AnchoredDirectoryV1.open(ROOT)
    before = _open_fds()
    try:
        with pytest.raises(MemoryError, match="injected at _open_worktree_artifacts"):
            _raise_at_line(
                binding._open_worktree_artifacts,
                "return tuple(artifacts), ()",
                lambda: binding._open_worktree_artifacts(
                    root, binding.PLAN_ARTIFACT_SPECS_V1
                ),
            )
        assert _open_fds() == before
    finally:
        root.close()


def test_artifact_caller_transfer_failure_unwinds_every_source() -> None:
    """AAA/RIPR: caller cleanup is active before it receives an open aggregate."""

    root = registry.AnchoredDirectoryV1.open(ROOT)
    head = registry.git_v1(root, ("rev-parse", "HEAD"))[1]
    before = _open_fds()
    try:
        with pytest.raises(KeyboardInterrupt, match="injected at bind_plan_artifacts_v1"):
            _raise_at_line(
                binding.bind_plan_artifacts_v1,
                "if artifacts is None:",
                lambda: binding.bind_plan_artifacts_v1(root, head),
                KeyboardInterrupt,
            )
        assert _open_fds() == before
    finally:
        root.close()


@pytest.mark.parametrize("failure_type", (MemoryError, KeyboardInterrupt))
def test_openat2_support_post_acquisition_baseexception_closes_descriptor(
    monkeypatch: pytest.MonkeyPatch,
    failure_type: type[BaseException],
) -> None:
    """Negative regression: support-probe interruption cannot leak its root fd."""

    real_acquire = registry._OwnedDescriptorsV1.acquire
    cached = tuple(registry._OPENAT2_SUPPORT)

    def acquire_then_fail(
        self: registry._OwnedDescriptorsV1,
        slot: int,
        opener: Callable[[], int],
    ) -> int:
        descriptor = real_acquire(self, slot, opener)
        raise failure_type(f"injected after support-probe acquisition {descriptor}")

    before = _open_fds()
    registry._OPENAT2_SUPPORT.clear()
    monkeypatch.setattr(registry._OwnedDescriptorsV1, "acquire", acquire_then_fail)
    try:
        with pytest.raises(failure_type, match="support-probe acquisition"):
            registry.openat2_support_v1()
        assert _open_fds() == before
        assert registry._OPENAT2_SUPPORT == []
    finally:
        registry._OPENAT2_SUPPORT[:] = cached
        _close_raw(_open_fds() - before)


@pytest.mark.parametrize("failure_type", (MemoryError, KeyboardInterrupt))
def test_proc_record_post_acquisition_baseexception_closes_descriptor(
    monkeypatch: pytest.MonkeyPatch,
    failure_type: type[BaseException],
) -> None:
    """Negative regression: proc-record interruption cannot leak its file fd."""

    real_acquire = registry._OwnedDescriptorsV1.acquire

    def acquire_then_fail(
        self: registry._OwnedDescriptorsV1,
        slot: int,
        opener: Callable[[], int],
    ) -> int:
        descriptor = real_acquire(self, slot, opener)
        raise failure_type(f"injected after proc-record acquisition {descriptor}")

    before = _open_fds()
    monkeypatch.setattr(registry._OwnedDescriptorsV1, "acquire", acquire_then_fail)
    try:
        with pytest.raises(failure_type, match="proc-record acquisition"):
            registry._read_proc_record(Path("/proc/self/stat"), 4096)
        assert _open_fds() == before
    finally:
        _close_raw(_open_fds() - before)


@pytest.mark.parametrize("attempts", (1, 8))
def test_repeated_root_handoff_failures_have_zero_descriptor_growth(
    monkeypatch: pytest.MonkeyPatch, attempts: int
) -> None:
    """Stateful BVA: one and eight transient handoff faults retain zero fds."""

    real_close = os.close
    before = _open_fds()
    try:
        for _attempt in range(attempts):
            calls = 0

            def fail_once(descriptor: int) -> None:
                nonlocal calls
                calls += 1
                if calls == 1:
                    raise OSError("injected repeated handoff failure")
                real_close(descriptor)

            monkeypatch.setattr(registry.os, "close", fail_once)
            with pytest.raises(OSError, match="repeated handoff failure"):
                registry.AnchoredDirectoryV1.open(ROOT)
            monkeypatch.setattr(registry.os, "close", real_close)
            assert _open_fds() == before
    finally:
        monkeypatch.setattr(registry.os, "close", real_close)
        _close_raw(_open_fds() - before)


def test_public_markdown_utf8_byte_bound_is_pure_before_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """BVA: exact one MiB crosses validation; one UTF-8 byte over is pure refusal."""

    calls: list[Path | checker.ConfinedRootV1] = []

    def refusing_bind(
        cls: type[checker.ConfinedRootV1], root: Path | checker.ConfinedRootV1
    ) -> checker.ConfinedRootV1:
        del cls
        calls.append(root)
        raise checker.RootUnavailable("sentinel root bind")

    monkeypatch.setattr(checker.ConfinedRootV1, "bind", classmethod(refusing_bind))
    exact = "é" * (checker.MAX_PLAN_MARKDOWN_BYTES // 2)
    exact_findings = checker.validate_plan_v1(_plan(), root=ROOT, markdown=exact)
    assert [finding.rule_id for finding in exact_findings] == ["root_unavailable"]
    assert calls == [ROOT]

    calls.clear()
    over_findings = checker.validate_plan_v1(
        _plan(), root=ROOT, markdown=exact + "X"
    )
    assert [finding.rule_id for finding in over_findings] == [
        "plan_markdown_size_refused"
    ]
    assert calls == []


@pytest.mark.parametrize(
    "fault_point,expected_state,expected_bytes",
    (
        ("open", "NOT_APPLIED", b"old"),
        ("write", "NOT_APPLIED", b"old"),
        ("file_fsync", "NOT_APPLIED", b"old"),
        ("close", "NOT_APPLIED", b"old"),
        ("rename", "NOT_APPLIED", b"old"),
        ("directory_fsync", "APPLIED_DURABILITY_UNKNOWN", b"new"),
    ),
)
def test_replacement_fault_points_report_linearization_and_retry_exactly(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    fault_point: str,
    expected_state: str,
    expected_bytes: bytes,
) -> None:
    """Stateful fault matrix: result state agrees with target bytes and exact retry."""

    target = tmp_path / "artifact.txt"
    target.write_bytes(b"old")
    real_open = os.open
    real_write = os.write
    real_fsync = os.fsync
    real_close = os.close
    real_rename = os.rename
    temporary_fd: int | None = None
    failed = False

    def is_temporary(path: PathArg) -> bool:
        return isinstance(path, str) and path.startswith(".artifact.txt.")

    def faulting_open(
        path: PathArg,
        flags: int,
        mode: int = 0o777,
        *,
        dir_fd: int | None = None,
    ) -> int:
        nonlocal temporary_fd, failed
        if fault_point == "open" and is_temporary(path) and not failed:
            failed = True
            raise OSError("injected open failure")
        descriptor = real_open(path, flags, mode, dir_fd=dir_fd)
        if is_temporary(path):
            temporary_fd = descriptor
        return descriptor

    def faulting_write(descriptor: int, data: bytes | bytearray | memoryview) -> int:
        nonlocal failed
        if fault_point == "write" and descriptor == temporary_fd and not failed:
            failed = True
            raise OSError("injected write failure")
        return real_write(descriptor, data)

    def faulting_fsync(descriptor: int) -> None:
        nonlocal failed
        mode = os.fstat(descriptor).st_mode
        requested = (
            fault_point == "file_fsync" and descriptor == temporary_fd
        ) or (fault_point == "directory_fsync" and stat.S_ISDIR(mode))
        if requested and not failed:
            failed = True
            raise OSError(f"injected {fault_point} failure")
        real_fsync(descriptor)

    def faulting_close(descriptor: int) -> None:
        nonlocal failed
        real_close(descriptor)
        if fault_point == "close" and descriptor == temporary_fd and not failed:
            failed = True
            raise OSError("injected close failure")

    def faulting_rename(
        source: PathArg,
        destination: PathArg,
        *,
        src_dir_fd: int | None = None,
        dst_dir_fd: int | None = None,
    ) -> None:
        nonlocal failed
        if fault_point == "rename" and not failed:
            failed = True
            raise OSError("injected rename failure")
        real_rename(
            source,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )

    with checker.ConfinedRootV1.bind(tmp_path) as root:
        with monkeypatch.context() as faults:
            faults.setattr(checker.os, "open", faulting_open)
            faults.setattr(checker.os, "write", faulting_write)
            faults.setattr(checker.os, "fsync", faulting_fsync)
            faults.setattr(checker.os, "close", faulting_close)
            faults.setattr(checker.os, "rename", faulting_rename)
            result = checker.replace_confined_file_v1(
                root, Path("artifact.txt"), b"new"
            )

        assert result.state.name == expected_state
        assert target.read_bytes() == expected_bytes

        retry = checker.replace_confined_file_v1(
            root, Path("artifact.txt"), b"new"
        )
        assert retry.state.name == "APPLIED_DURABLE"
        assert target.read_bytes() == b"new"


def test_replacement_foreign_exclusive_temp_is_never_unlinked(tmp_path: Path) -> None:
    """Negative regression: an O_EXCL collision never transfers pathname ownership."""

    target = tmp_path / "artifact.txt"
    target.write_bytes(b"old")
    foreign = tmp_path / f".artifact.txt.{os.getpid()}.tmp"
    foreign.write_bytes(b"foreign")

    with checker.ConfinedRootV1.bind(tmp_path) as root:
        result = checker.replace_confined_file_v1(
            root, Path("artifact.txt"), b"new"
        )

    assert result.state is checker.ConfinedReplaceStateV1.NOT_APPLIED
    assert target.read_bytes() == b"old"
    assert foreign.read_bytes() == b"foreign"


def test_identical_bytes_pre_rename_fault_is_ambiguous_and_retryable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Stateful regression: equality cannot prove application before rename returns."""

    target = tmp_path / "artifact.txt"
    target.write_bytes(b"same")
    temporary = tmp_path / f".artifact.txt.{os.getpid()}.tmp"

    def fail_before_rename(*_args: object, **_kwargs: object) -> None:
        raise OSError("injected pre-rename fault")

    with checker.ConfinedRootV1.bind(tmp_path) as root:
        with monkeypatch.context() as fault:
            fault.setattr(checker.os, "rename", fail_before_rename)
            result = checker.replace_confined_file_v1(
                root, Path("artifact.txt"), b"same"
            )

        assert result.state is checker.ConfinedReplaceStateV1.APPLICATION_UNKNOWN
        assert target.read_bytes() == b"same"
        assert not temporary.exists()

        retry = checker.replace_confined_file_v1(
            root, Path("artifact.txt"), b"same"
        )
        assert retry.state is checker.ConfinedReplaceStateV1.APPLIED_DURABLE
        assert target.read_bytes() == b"same"


def test_applied_then_raising_rename_is_ambiguous_and_retryable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Stateful regression: a raising rename cannot be claimed as applied."""

    target = tmp_path / "artifact.txt"
    target.write_bytes(b"old")
    temporary = tmp_path / f".artifact.txt.{os.getpid()}.tmp"
    real_rename = os.rename

    def apply_then_fail(
        source: PathArg,
        destination: PathArg,
        *,
        src_dir_fd: int | None = None,
        dst_dir_fd: int | None = None,
    ) -> None:
        real_rename(
            source,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )
        raise OSError("injected post-application rename fault")

    with checker.ConfinedRootV1.bind(tmp_path) as root:
        with monkeypatch.context() as fault:
            fault.setattr(checker.os, "rename", apply_then_fail)
            result = checker.replace_confined_file_v1(
                root, Path("artifact.txt"), b"new"
            )

        assert result.state is checker.ConfinedReplaceStateV1.APPLICATION_UNKNOWN
        assert target.read_bytes() == b"new"
        assert not temporary.exists()

        retry = checker.replace_confined_file_v1(
            root, Path("artifact.txt"), b"new"
        )
        assert retry.state is checker.ConfinedReplaceStateV1.APPLIED_DURABLE
        assert target.read_bytes() == b"new"


def test_replacement_result_states_are_closed_and_caller_mapping_is_exhaustive() -> None:
    """Mutation oracle: every linearization state has one exact caller outcome."""

    states = checker.ConfinedReplaceStateV1
    not_applied = checker.ConfinedReplaceResultV1(
        states.NOT_APPLIED, "write refused"
    )
    uncertain = checker.ConfinedReplaceResultV1(
        states.APPLIED_DURABILITY_UNKNOWN, "directory sync refused"
    )
    ambiguous = checker.ConfinedReplaceResultV1(
        states.APPLICATION_UNKNOWN, "rename outcome unavailable"
    )
    durable = checker.ConfinedReplaceResultV1(states.APPLIED_DURABLE, "")

    assert checker._replacement_finding_v1(
        not_applied, checker.PLAN_JSON_PATH
    ) == checker.PlanFinding(
        "plan_artifact_write_refused", checker.PLAN_JSON_PATH.as_posix(), "write refused"
    )
    assert checker._replacement_finding_v1(
        uncertain, checker.PLAN_JSON_PATH
    ) == checker.PlanFinding(
        "plan_artifact_write_durability_unknown",
        checker.PLAN_JSON_PATH.as_posix(),
        "directory sync refused",
    )
    assert checker._replacement_finding_v1(
        ambiguous, checker.PLAN_JSON_PATH
    ) == checker.PlanFinding(
        "plan_artifact_write_application_unknown",
        checker.PLAN_JSON_PATH.as_posix(),
        "rename outcome unavailable",
    )
    assert checker._replacement_finding_v1(durable, checker.PLAN_JSON_PATH) is None


def test_hygiene_successor_preserves_history_and_bounds_ownership_claim() -> None:
    """Evidence oracle: immutable history remains exact and its successor is narrow."""

    historical = (ROOT / HISTORICAL_PACKET).read_bytes()
    packet = json.loads((ROOT / SUCCESSOR_PACKET).read_text(encoding="utf-8"))
    claim = packet["claim_scope"]
    nonclaims = packet["nonclaims"]

    assert hashlib.sha256(historical).hexdigest() == HISTORICAL_PACKET_SHA256
    assert "unwinds every acquired descriptor on BaseException paths" not in claim
    assert all(
        marker in claim
        for marker in (
            "root traversal handoff",
            "subtree walk handoff",
            "open_entry finalizer",
            "effect aggregate allocation",
            "open_file acquisition",
            "ad-hoc root transfer",
            "artifact aggregate return",
            "artifact caller transfer",
        )
    )
    assert any("persistent close failures" in item.casefold() for item in nonclaims)
    assert any("production_authority remains NONE" in item for item in nonclaims)


def test_current_hygiene_packet_invalidates_universal_predecessors_and_names_matrix() -> None:
    """Evidence oracle: only the bounded successor can serve as current evidence."""

    packet = json.loads((ROOT / CURRENT_PACKET).read_text(encoding="utf-8"))
    claim = packet["claim_scope"]
    dimensions = {
        row["name"]: row["points"] for row in packet["boundary_dimensions"]
    }
    report = checker_check_hygiene_for_live_registry()

    assert packet["supersedes_evidence_ids"] == [
        "THV1-20260826-whole-program-assurance-checker",
        "THV1-20260826-z-whole-program-assurance-checker-fcis-linearization",
    ]
    assert "unwinds every acquired descriptor" not in claim
    assert dimensions["replacement_fault_matrix"] == [
        "foreign_O_EXCL_EEXIST_preserves_foreign_temp_and_target",
        "open_write_file_fsync_close_and_preapply_rename_are_NOT_APPLIED",
        "identical_bytes_preapply_rename_fault_is_APPLICATION_UNKNOWN",
        "applied_then_raising_rename_is_APPLICATION_UNKNOWN",
        "directory_fsync_fault_is_APPLIED_DURABILITY_UNKNOWN",
        "all_tested_owned_temp_faults_allow_exact_retry",
    ]
    assert dimensions["post_acquisition_baseexception_cleanup"] == [
        "openat2_support_MemoryError",
        "openat2_support_KeyboardInterrupt",
        "proc_record_MemoryError",
        "proc_record_KeyboardInterrupt",
    ]
    assert report["selected_evidence_ids"] == [packet["evidence_id"]]
    superseded = cast(list[str], report["superseded_evidence_ids"])
    assert set(superseded) >= set(
        packet["supersedes_evidence_ids"]
    )


def checker_check_hygiene_for_live_registry() -> dict[str, object]:
    """Run the public hygiene boundary for one newly explicit critical path."""

    from tools.check_test_hygiene_v1 import ChangedPathV1, check_repository

    return check_repository(
        changed_paths=[
            ChangedPathV1(status="M", path="tools/live_gate_registry_v1.py")
        ]
    )
