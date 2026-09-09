"""Crash, response-loss and stale-worker histories observe the entire archive."""

import multiprocessing
import os
import sqlite3

import pytest

from src.zenolacuna.authority import Action, decode_signed, encode_signed
from src.zenolacuna.model import LacunaError
from src.zenolacuna.project import Project
from tests.test_zenolacuna_project import answer, initialize, signed
from tests.zenolacuna_project_helpers import public_key

ABORT_POINTS = ("after_source_snapshot", "after_verification", "after_source_insert",
                "after_event_insert", "before_commit")


def test_given_full_source_archive_when_revision_exceeds_blob_budget_then_readable_previous_state_survives(tmp_path):
    import hashlib
    from dataclasses import replace

    from src.zenolacuna.model import SourceRef
    from src.zenolacuna.project_types import RuntimeSpec, Task, task_value
    from tests.test_zenolacuna_project_evidence import _create
    from tests.zenolacuna_project_helpers import scope

    def generation(number):
        sources = []
        for index in range(32):
            name = f"source-{index:02d}.txt"
            raw = f"generation={number};source={index}".encode("ascii")
            (tmp_path / name).write_bytes(raw)
            sources.append(SourceRef(name, hashlib.sha256(raw).hexdigest()))
        return Task(replace(scope(), sources=tuple(sources)), RuntimeSpec("RELATION", (), ()), (), None, None)

    project = _create(tmp_path, generation(0))
    for number in range(1, 8):
        state = project.state()
        successor = generation(number)
        # Prepare the current-parent value before replacing working bytes.
        from src.zenolacuna.authority import Command, sign
        from src.zenolacuna.codec import encode
        from tests.zenolacuna_project_helpers import OWNER_SECRET
        request = sign(Command("test-project", state.revision, Action.REVISE, encode({
            "scope_root": state.task.scope.root, "task": task_value(successor),
            "retired_protected": [], "reason": "Approve successor source generation",
        })), OWNER_SECRET)
        project.apply(request)
    state = project.state()
    before = project.export_bytes()
    with sqlite3.connect(project.path) as db:
        assert db.execute("SELECT count(*) FROM sources").fetchone() == (256,)
    successor = generation(8)
    request = sign(Command("test-project", state.revision, Action.REVISE, encode({
        "scope_root": state.task.scope.root, "task": task_value(successor),
        "retired_protected": [], "reason": "Would exceed the archive count budget",
    })), OWNER_SECRET)
    with pytest.raises(LacunaError, match="^PROJECT_BUDGET_EXCEEDED$"):
        project.apply(request)
    generation(7)
    assert project.export_bytes() == before


@pytest.mark.parametrize("point", ABORT_POINTS)
def test_given_interrupted_transaction_when_reopened_then_previous_revision_exact(tmp_path, point):
    project = initialize(tmp_path)
    command = answer(project)
    before = project.export_bytes()

    def failed_sync(at):
        if at == point:
            raise OSError("injected persistence failure")

    project.fault_hook = failed_sync
    with pytest.raises(OSError, match="injected"):
        project.apply(command)
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    assert reopened.export_bytes() == before
    reopened.apply(command)
    assert reopened.state().survivors == (0, 2)


def _crash_writer(path: str, source: str, command: bytes, point: str) -> None:
    def crash(at: str) -> None:
        if at == point:
            os._exit(77)

    Project(path, source_root=source, owner_key=public_key(), fault_hook=crash).apply(decode_signed(command))


@pytest.mark.parametrize("point", ("after_event_insert", "before_commit", "after_commit"))
def test_given_process_death_when_restart_and_retry_then_one_decision(tmp_path, point):
    project = initialize(tmp_path)
    command = answer(project)
    before = project.export_bytes()
    process = multiprocessing.get_context("spawn").Process(
        target=_crash_writer, args=(str(project.path), str(tmp_path), encode_signed(command), point),
    )
    process.start()
    process.join(20)
    assert process.exitcode == 77
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    if point == "after_commit":
        after = reopened.export_bytes()
        assert after != before
        assert reopened.apply(command)["code"] == "IDEMPOTENT_DUPLICATE"
        assert reopened.export_bytes() == after
    else:
        assert reopened.export_bytes() == before
        reopened.apply(command)
    assert len(reopened.state().answers) == 1


def test_given_cancelled_restart_when_late_worker_returns_then_no_revival(tmp_path):
    project = initialize(tmp_path)
    late = answer(project)
    project.apply(signed(project, Action.CANCEL, {"scope_root": project.state().task.scope.root}))
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    before = reopened.export_bytes()
    assert reopened.status()["workflow"] == "CANCELLED"
    with pytest.raises(LacunaError, match="STALE_ANSWER"):
        reopened.apply(late)
    assert reopened.export_bytes() == before
    reopened.apply(signed(reopened, Action.RESUME, {"scope_root": reopened.state().task.scope.root}))
    with pytest.raises(LacunaError, match="STALE_ANSWER"):
        reopened.apply(late)
    reopened.apply(answer(reopened))
    assert reopened.state().survivors == (0, 2)


@pytest.mark.parametrize("prefix", (0, 1, 16, 100, 512, 1024, 4096))
def test_given_torn_database_when_read_then_never_fall_back_to_old_success(tmp_path, prefix):
    project = initialize(tmp_path)
    raw = project.path.read_bytes()
    broken = tmp_path / "broken.sqlite"
    broken.write_bytes(raw[:prefix])
    with pytest.raises(LacunaError, match="CORRUPT_PROJECT|PROJECT_IO_ERROR"):
        Project(broken, source_root=tmp_path, owner_key=public_key()).status()


def _racing_writer(path: str, source: str, raw: bytes, gate, output) -> None:
    project = Project(path, source_root=source, owner_key=public_key())
    gate.wait(20)
    try:
        result = project.apply(decode_signed(raw))
        output.put(result["code"])
    except LacunaError as exc:
        output.put(exc.code)


def test_given_two_workers_when_same_command_races_then_exactly_one_event(tmp_path):
    project = initialize(tmp_path)
    command = answer(project)
    context = multiprocessing.get_context("spawn")
    gate, output = context.Event(), context.Queue()
    workers = [context.Process(target=_racing_writer, args=(str(project.path), str(tmp_path),
                                                           encode_signed(command), gate, output)) for _ in range(2)]
    for worker in workers:
        worker.start()
    gate.set()
    for worker in workers:
        worker.join(20)
        assert worker.exitcode == 0
    codes = [output.get(timeout=1) for _ in workers]
    assert "DECISIONS_RESOLVED" in codes
    assert set(codes) <= {"DECISIONS_RESOLVED", "IDEMPOTENT_DUPLICATE", "PROJECT_BUSY"}
    assert project.apply(command)["code"] == "IDEMPOTENT_DUPLICATE"
    with sqlite3.connect(project.path) as db:
        assert db.execute("SELECT count(*) FROM events").fetchone() == (2,)


def test_given_source_changes_at_last_commit_boundary_then_transaction_rolls_back(tmp_path):
    from dataclasses import replace
    from hashlib import sha256

    from src.zenolacuna.authority import Command, sign
    from src.zenolacuna.codec import encode
    from src.zenolacuna.model import SourceRef
    from src.zenolacuna.project_types import RuntimeSpec, Task, task_value
    from tests.zenolacuna_project_helpers import OWNER_SECRET, scope

    source = tmp_path / "source.txt"
    source.write_bytes(b"original")
    task = Task(replace(scope(), sources=(SourceRef("source.txt", sha256(b"original").hexdigest()),)),
                RuntimeSpec("RELATION", (), ()), (), None, None)
    project = Project(tmp_path / "run.sqlite", source_root=tmp_path, owner_key=public_key())
    project.apply(sign(Command("test-project", None, Action.INIT,
                              encode({"task": task_value(task), "checker_sha256": project.checker_sha256})), OWNER_SECRET))
    command = answer(project)
    before = project.export_bytes()

    def mutate(point):
        if point == "before_commit":
            source.write_bytes(b"changed")

    project.fault_hook = mutate
    with pytest.raises(LacunaError, match="SOURCE_DRIFT"):
        project.apply(command)
    source.write_bytes(b"original")
    project.fault_hook = None
    assert project.export_bytes() == before


@pytest.mark.parametrize("point", ("after_source_insert", "after_event_insert", "before_commit"))
def test_given_new_source_revision_when_aborted_then_source_blob_and_event_roll_back(tmp_path, point):
    from dataclasses import replace
    from hashlib import sha256

    from src.zenolacuna.authority import Command, sign
    from src.zenolacuna.codec import encode
    from src.zenolacuna.model import SourceRef
    from src.zenolacuna.project_types import task_value
    from tests.test_zenolacuna_project_evidence import _create, _pipeline_task
    from tests.zenolacuna_project_helpers import OWNER_SECRET

    task = _pipeline_task(tmp_path)
    project = _create(tmp_path, task)
    before = project.export_bytes()
    parent = project.state().revision
    source = tmp_path / "transform.py"
    original = source.read_bytes()
    new = b"def transform(x):\n    return x ^ 0\n"
    source.write_bytes(new)
    successor = replace(task, scope=replace(task.scope, sources=(SourceRef("transform.py", sha256(new).hexdigest()),)))
    request = sign(Command("test-project", parent, Action.REVISE, encode({
        "scope_root": task.scope.root, "task": task_value(successor), "retired_protected": [], "reason": "New source",
    })), OWNER_SECRET)

    def interrupt(at):
        if at == point:
            raise OSError("write/sync boundary failed")

    project.fault_hook = interrupt
    with pytest.raises(OSError, match="write/sync"):
        project.apply(request)
    source.write_bytes(original)
    project.fault_hook = None
    assert project.export_bytes() == before
    with sqlite3.connect(project.path) as db:
        assert db.execute("SELECT count(*) FROM sources").fetchone() == (1,)


@pytest.mark.parametrize("point", ("before_commit", "after_commit"))
def test_given_complete_evidence_when_process_dies_then_atomic_receipt_and_idempotent_retry(tmp_path, point):
    from tests.test_zenolacuna_project_evidence import _create, _pipeline_assess, _pipeline_task

    project = _create(tmp_path, _pipeline_task(tmp_path))
    request = _pipeline_assess(project)
    before = project.export_bytes()
    process = multiprocessing.get_context("spawn").Process(
        target=_crash_writer, args=(str(project.path), str(tmp_path), encode_signed(request), point),
    )
    process.start()
    process.join(20)
    assert process.exitcode == 77
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    if point == "before_commit":
        assert reopened.export_bytes() == before
        assert reopened.status()["workflow"] != "COMPLETE_FOR_SCOPE"
    else:
        assert reopened.status()["workflow"] == "COMPLETE_FOR_SCOPE"
        assert reopened.apply(request)["code"] == "IDEMPOTENT_DUPLICATE"
    reopened.apply(request)
    assert reopened.status()["workflow"] == "COMPLETE_FOR_SCOPE"
    with sqlite3.connect(project.path) as db:
        assert db.execute("SELECT count(*) FROM events WHERE evidence IS NOT NULL").fetchone() == (1,)


def test_given_assessed_repair_when_cancelled_then_late_complete_cannot_revive_it(tmp_path):
    from tests.test_zenolacuna_project_evidence import _create, _pipeline_assess, _pipeline_task

    project = _create(tmp_path, _pipeline_task(tmp_path))
    late = _pipeline_assess(project)
    project.apply(signed(project, Action.CANCEL, {"scope_root": project.state().task.scope.root}))
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    before = reopened.export_bytes()
    with pytest.raises(LacunaError, match="STALE_ANSWER"):
        reopened.apply(late)
    assert reopened.export_bytes() == before
    reopened.apply(signed(reopened, Action.RESUME, {"scope_root": reopened.state().task.scope.root}))
    assert reopened.state().candidate is None
    with pytest.raises(LacunaError, match="CANDIDATE_REQUIRED"):
        reopened.apply(signed(reopened, Action.COMPLETE, {"scope_root": reopened.state().task.scope.root,
                                                         "candidate_root": "0" * 64}))
