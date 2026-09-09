"""Data-only preparation and signed-project shell for ZenoLacuna.

The project CLI deliberately has two stages.  ``prepare`` writes a canonical
unsigned command wire.  ``sign`` reads that wire and an operator-provided raw
Ed25519 seed, and writes the existing signed envelope.  ``apply`` is the only
command here that changes a project database.  Every other project command is
read-only or creates a new, exclusive artifact.

JSON is emitted as one stable object on stdout.  Typed workflow failures are
reported as ``{"code": ..., "status": "REJECTED"}`` with exit status 2;
private key bytes and owner pins are never included in output.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import stat
from dataclasses import replace
from pathlib import Path
from typing import NoReturn, Sequence, cast

from . import authority as _authority
from .authority import (
    MAX_PAYLOAD_BYTES,
    MAX_WIRE_BYTES,
    Action,
    Command,
    command_bytes,
    decode_signed,
    encode_signed,
    sign,
)
from .codec import MAX_JSON_BYTES, _parse, decode_candidate, encode
from .filesystem import _checked_directory
from .model import Candidate, LacunaError, OutcomeKind, Profile, Witness
from .project import Project, replay_bundle
from .project_bindings import checker_fingerprint
from .project_runtime import ExternalTools
from .project_types import RuntimeSpec, Task, decode_task, plain, task_value

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
_KEY_BYTES = 32
_ACTION_NAMES = {action.value.lower(): action for action in Action}
_ACTION_NAMES.update({action.value: action for action in Action})
_REQUEST_FIELDS = frozenset({"action", "parent", "payload", "project_id", "version"})


class _Parser(argparse.ArgumentParser):
    def error(self, _message: str) -> NoReturn:
        raise LacunaError("INVALID_ARGUMENT")


def _add_host_arguments(parser: argparse.ArgumentParser, *, inherited: bool = False) -> None:
    default = argparse.SUPPRESS if inherited else str(_REPOSITORY_ROOT)
    parser.add_argument("--source-root", default=default, metavar="PATH")
    parser.add_argument("--tau-bin", default=argparse.SUPPRESS, metavar="PATH")
    parser.add_argument("--esso-root", default=argparse.SUPPRESS, metavar="PATH")


def _add_common_subcommand_arguments(parser: argparse.ArgumentParser) -> None:
    _add_host_arguments(parser, inherited=True)


def _parser() -> _Parser:
    parser = _Parser(prog="zenolacuna project")
    _add_host_arguments(parser)
    commands = parser.add_subparsers(dest="project_command", required=True)

    prepare_init = commands.add_parser("prepare-init", help="write an unsigned initialization request")
    _add_common_subcommand_arguments(prepare_init)
    prepare_init.add_argument("--task", required=True, metavar="TASK.json")
    prepare_init.add_argument("--project-id", required=True, metavar="ID")
    prepare_init.add_argument("--out", required=True, metavar="REQUEST")

    prepare = commands.add_parser("prepare", help="write an unsigned command for the current revision")
    _add_common_subcommand_arguments(prepare)
    prepare.add_argument("--run", required=True, metavar="DB")
    prepare.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    prepare.add_argument("--action", required=True, choices=tuple(sorted(_ACTION_NAMES)), metavar="ACTION")
    prepare.add_argument("--out", required=True, metavar="REQUEST")
    prepare.add_argument("--payload", metavar="PAYLOAD.json")
    prepare.add_argument("--parent", metavar="REVISION")
    prepare.add_argument("--question", metavar="NAME")
    prepare.add_argument("--answer", metavar="ANSWER")
    prepare.add_argument("--candidate", metavar="CANDIDATE.json")
    prepare.add_argument("--task", metavar="TASK.json")
    prepare.add_argument("--reason", metavar="TEXT")
    prepare.add_argument("--retire", action="append", default=[], metavar="NAME[,NAME]")

    signer = commands.add_parser("sign", help="sign one prepared request with an offline raw seed")
    _add_common_subcommand_arguments(signer)
    signer.add_argument("--request", required=True, metavar="REQUEST")
    signer.add_argument("--key-file", required=True, metavar="KEY")
    signer.add_argument("--out", required=True, metavar="SIGNED")

    apply = commands.add_parser("apply", help="verify and apply one signed command")
    _add_common_subcommand_arguments(apply)
    apply.add_argument("--run", required=True, metavar="DB")
    apply.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    apply.add_argument("--command", required=True, metavar="SIGNED")

    for name, help_text in (
        ("status", "reconstruct current project status"),
        ("propose", "render a data-only proposal packet"),
    ):
        command = commands.add_parser(
            name, aliases=["proposals"] if name == "propose" else (), help=help_text,
        )
        _add_common_subcommand_arguments(command)
        command.add_argument("--run", required=True, metavar="DB")
        command.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")

    witness = commands.add_parser("witness", help="replay one checked distinguishing witness")
    _add_common_subcommand_arguments(witness)
    witness.add_argument("--run", required=True, metavar="DB")
    witness.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    witness.add_argument("--witness", required=True, metavar="WITNESS.json")
    witness.add_argument("--expected-revision", metavar="REVISION")

    observe = commands.add_parser("observe", help="admit one complete finite-model observation")
    _add_common_subcommand_arguments(observe)
    observe.add_argument("--run", required=True, metavar="DB")
    observe.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    observe.add_argument("--context", required=True, metavar="CONTEXT")
    observe.add_argument("--kind", required=True, choices=tuple(kind.value for kind in OutcomeKind), metavar="ACCEPT|REJECT")
    observe.add_argument("--observation", required=True, metavar="TEXT")
    observe.add_argument("--expected-revision", metavar="REVISION")

    inspect = commands.add_parser("inspect", help="inspect a candidate against the current scope")
    _add_common_subcommand_arguments(inspect)
    inspect.add_argument("--run", required=True, metavar="DB")
    inspect.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    inspect.add_argument("--candidate", required=True, metavar="CANDIDATE.json")

    candidate = commands.add_parser("candidate", help="write a built-in migration candidate")
    _add_common_subcommand_arguments(candidate)
    candidate.add_argument("--mode", required=True, choices=("guarded", "unguarded"), metavar="MODE")
    candidate.add_argument("--out", required=True, metavar="CANDIDATE.json")

    export = commands.add_parser("export", help="write the exact replay bundle")
    _add_common_subcommand_arguments(export)
    export.add_argument("--run", required=True, metavar="DB")
    export.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    export.add_argument("--out", required=True, metavar="BUNDLE")

    replay = commands.add_parser("replaybundle", help="replay an exact historical bundle")
    _add_common_subcommand_arguments(replay)
    replay.add_argument("--bundle", required=True, metavar="BUNDLE")
    replay.add_argument("--owner-key", required=True, metavar="PUBLIC_KEY")
    replay.add_argument("--expected-revision", metavar="REVISION")

    task = commands.add_parser("task", help="validate or create a project task artifact")
    _add_common_subcommand_arguments(task)
    task.add_argument("--task", "--input", dest="task_input", metavar="TASK.json")
    task.add_argument("--adapter", choices=("relation", "restricted-pipeline", "signal-migration"))
    task.add_argument("--profile", choices=tuple(profile.value for profile in Profile))
    task.add_argument("--inputs", action="append", metavar="N[,N]")
    task.add_argument("--observations", action="append", metavar="NAME[,NAME]")
    task.add_argument("--out", required=True, metavar="TASK.json")
    return parser


def _absolute(path: str | Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _read_bytes(
    path: str | Path,
    maximum: int,
    *,
    missing_code: str = "INPUT_MISSING",
    symlink_code: str = "INPUT_SYMLINK",
    invalid_code: str = "INPUT_INVALID",
) -> bytes:
    input_path = _absolute(path)
    try:
        _checked_directory(input_path.parent, missing_code)
    except LacunaError as error:
        if error.code == missing_code:
            raise
        raise LacunaError(symlink_code if error.code == "PATH_SYMLINK" else invalid_code) from error
    try:
        details = os.lstat(input_path)
    except FileNotFoundError as exc:
        raise LacunaError(missing_code) from exc
    except OSError as exc:
        raise LacunaError("IO_ERROR") from exc
    if stat.S_ISLNK(details.st_mode):
        raise LacunaError(symlink_code)
    if not stat.S_ISREG(details.st_mode) or details.st_size > maximum:
        raise LacunaError(invalid_code)
    descriptor = os.open(input_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode) or opened.st_size > maximum:
            raise LacunaError(invalid_code)
        chunks: list[bytes] = []
        remaining = maximum + 1
        while remaining:
            chunk = os.read(descriptor, min(65_536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        result = b"".join(chunks)
        if len(result) > maximum:
            raise LacunaError(invalid_code)
        return result
    finally:
        os.close(descriptor)


def _write_exclusive(path: str | Path, raw: bytes, *, maximum: int) -> Path:
    if type(raw) is not bytes or len(raw) > maximum:
        raise LacunaError("OUTPUT_TOO_LARGE")
    output_path = _absolute(path)
    parent = output_path.parent
    try:
        _checked_directory(parent, "OUTPUT_PARENT_MISSING")
    except LacunaError as error:
        if error.code == "OUTPUT_PARENT_MISSING":
            raise
        raise LacunaError("OUTPUT_PARENT_INVALID") from error
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(output_path, flags, 0o600)
    except FileExistsError as exc:
        raise LacunaError("OUTPUT_EXISTS") from exc
    except OSError as exc:
        if getattr(exc, "errno", None) == 40:  # ELOOP on common Unix hosts.
            raise LacunaError("OUTPUT_SYMLINK") from exc
        raise LacunaError("OUTPUT_IO_ERROR") from exc
    try:
        offset = 0
        while offset < len(raw):
            offset += os.write(descriptor, raw[offset:])
        os.fsync(descriptor)
    except OSError as exc:
        raise LacunaError("OUTPUT_IO_ERROR") from exc
    finally:
        os.close(descriptor)
    return output_path


def _read_json(path: str | Path, maximum: int = MAX_JSON_BYTES) -> object:
    return _parse(_read_bytes(path, maximum))


def _parse_inline_or_file(value: str, maximum: int = MAX_JSON_BYTES) -> object:
    if value.lstrip().startswith(("{", "[")):
        raw = value.encode("utf-8")
        if len(raw) > maximum:
            raise LacunaError("JSON_TOO_LARGE")
        return _parse(raw)
    return _read_json(value, maximum)


def _read_task(path: str | Path) -> Task:
    raw = _read_bytes(path, MAX_JSON_BYTES)
    value = _parse(raw)
    task = decode_task(value)
    if encode(task_value(task)) != raw:
        raise LacunaError("NONCANONICAL_TASK")
    return task


def _read_candidate(path: str | Path) -> Candidate:
    raw = _read_bytes(path, MAX_JSON_BYTES)
    candidate = decode_candidate(raw)
    if encode(candidate) != raw:
        raise LacunaError("NONCANONICAL_CANDIDATE")
    return candidate


def _read_witness(path: str | Path) -> Witness:
    raw = _read_bytes(path, MAX_JSON_BYTES)
    value = _parse(raw)
    if type(value) is not dict:
        raise LacunaError("JSON_TYPE")
    item = cast(dict[str, object], value)
    expected = {
        "scope_root", "context", "left_hypothesis", "right_hypothesis",
        "left_outcome", "right_outcome",
    }
    if set(item) != expected:
        raise LacunaError("JSON_FIELDS")
    scope_root = item["scope_root"]
    if type(scope_root) is not str or len(scope_root) != 64 or any(
        character not in "0123456789abcdef" for character in scope_root
    ):
        raise LacunaError("INVALID_DIGEST")
    indices = tuple(item[name] for name in (
        "context", "left_hypothesis", "right_hypothesis", "left_outcome", "right_outcome",
    ))
    if any(type(index) is not int for index in indices):
        raise LacunaError("JSON_TYPE")
    witness = Witness(scope_root, *cast(tuple[int, int, int, int, int], indices))
    if encode(plain(witness)) != raw:
        raise LacunaError("NONCANONICAL_WITNESS")
    return witness


def _read_key(path: str | Path) -> bytes:
    input_path = _absolute(path)
    try:
        _checked_directory(input_path.parent, "KEY_MISSING")
    except LacunaError as error:
        if error.code == "KEY_MISSING":
            raise
        raise LacunaError("KEY_INVALID") from error
    try:
        details = os.lstat(input_path)
    except FileNotFoundError as exc:
        raise LacunaError("KEY_MISSING") from exc
    if stat.S_ISLNK(details.st_mode):
        raise LacunaError("KEY_SYMLINK")
    if not stat.S_ISREG(details.st_mode) or not stat.S_IMODE(details.st_mode) & 0o400 \
            or stat.S_IMODE(details.st_mode) & 0o077:
        raise LacunaError("KEY_PERMISSIONS")
    descriptor = os.open(input_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        opened = os.fstat(descriptor)
        mode = stat.S_IMODE(opened.st_mode)
        if not stat.S_ISREG(opened.st_mode) or not mode & 0o400 or mode & 0o077:
            raise LacunaError("KEY_PERMISSIONS")
        if opened.st_size != _KEY_BYTES:
            raise LacunaError("KEY_INVALID")
        raw = os.read(descriptor, _KEY_BYTES + 1)
        if len(raw) != _KEY_BYTES or os.read(descriptor, 1):
            raise LacunaError("KEY_INVALID")
        return raw
    finally:
        os.close(descriptor)


def _decode_request(raw: bytes) -> Command:
    """Decode exactly one canonical unsigned command wire.

    A public ``decode_command`` helper may be supplied by the authority module
    later.  The fallback uses the authority module's already-tested bounded
    wire primitives, keeping this CLI from reimplementing signature semantics.
    """
    decoder = getattr(_authority, "decode_command", None)
    if callable(decoder):
        command = decoder(raw)
        if type(command) is not Command or command_bytes(command) != raw:
            raise LacunaError("MALFORMED_APPROVAL")
        return command
    value = _authority._parse_object(raw, MAX_WIRE_BYTES)
    item = _authority._closed_object(value, _REQUEST_FIELDS)
    _authority._version(item["version"])
    payload = _authority._payload(_authority._decode_payload_b64(item["payload"]))
    command = Command(
        _authority._project_id(item["project_id"]),
        None if item["parent"] is None else _authority._root(item["parent"]),
        _authority._action(item["action"]),
        payload,
    )
    if command_bytes(command) != raw:
        raise LacunaError("MALFORMED_APPROVAL")
    return command


def _action(value: str) -> Action:
    try:
        return _ACTION_NAMES[value]
    except KeyError as exc:
        raise LacunaError("INVALID_ARGUMENT") from exc


def _csv_strings(values: Sequence[str]) -> tuple[str, ...]:
    result: list[str] = []
    for value in values:
        result.extend(part for part in value.split(",") if part)
    return tuple(result)


def _csv_ints(values: Sequence[str]) -> tuple[int, ...]:
    result: list[int] = []
    for value in _csv_strings(values):
        try:
            result.append(int(value, 10))
        except ValueError as exc:
            raise LacunaError("INVALID_RUNTIME_INPUTS") from exc
    return tuple(result)


def _tools(args: argparse.Namespace) -> ExternalTools:
    tau_bin = None if getattr(args, "tau_bin", None) is None else _absolute(args.tau_bin)
    esso_root = None if getattr(args, "esso_root", None) is None else _absolute(args.esso_root)
    return ExternalTools(tau_bin=tau_bin, esso_root=esso_root)


def _project(args: argparse.Namespace) -> Project:
    return Project(
        args.run,
        source_root=args.source_root,
        owner_key=args.owner_key,
        tools=_tools(args),
    )


def _summary(path: Path, raw: bytes, *, kind: str) -> dict[str, object]:
    return {
        "artifact": kind,
        "bytes": len(raw),
        "path": str(path),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "status": "WRITTEN",
    }


def _prepare_payload(args: argparse.Namespace, status: dict[str, object], action: Action) -> bytes:
    if args.payload is not None:
        value = _parse_inline_or_file(args.payload, MAX_PAYLOAD_BYTES)
        if type(value) is not dict:
            raise LacunaError("JSON_TYPE")
        return encode(value)
    scope_root = status.get("scope_root")
    if type(scope_root) is not str:
        raise LacunaError("INTERNAL_RENDER_ERROR")
    if action is Action.ANSWER:
        question = args.question
        if question is None:
            analysis = status.get("analysis")
            if type(analysis) is dict:
                pending = cast(dict[str, object], analysis).get("pending_question")
                if type(pending) is dict:
                    question = cast(dict[str, object], pending).get("name")
        if type(question) is not str or args.answer is None:
            raise LacunaError("INVALID_ARGUMENT")
        witness_root = status.get("witness_root")
        if type(witness_root) is not str:
            raise LacunaError("INTERNAL_RENDER_ERROR")
        return encode({
            "answer": args.answer,
            "question": question,
            "scope_root": scope_root,
            "witness_root": witness_root,
        })
    if action is Action.REVISE:
        if args.task is None or args.reason is None:
            raise LacunaError("INVALID_ARGUMENT")
        task = _read_task(args.task)
        return encode({
            "reason": args.reason,
            "retired_protected": list(_csv_strings(args.retire)),
            "scope_root": scope_root,
            "task": task_value(task),
        })
    if action is Action.ASSESS:
        if args.candidate is None:
            raise LacunaError("INVALID_ARGUMENT")
        candidate = _read_candidate(args.candidate)
        return encode({"candidate": plain(candidate), "scope_root": scope_root})
    if action is Action.COMPLETE:
        analysis = status.get("analysis")
        if type(analysis) is dict and analysis.get("workflow") != "READY_FOR_REPLAY":
            raise LacunaError(str(analysis["code"]))
        candidate_root = status.get("candidate_root")
        if type(candidate_root) is not str:
            raise LacunaError("CANDIDATE_REQUIRED")
        return encode({"candidate_root": candidate_root, "scope_root": scope_root})
    if action in (Action.CANCEL, Action.RESUME):
        return encode({"scope_root": scope_root})
    raise LacunaError("UNSUPPORTED_ACTION")


def _prepare_init(args: argparse.Namespace) -> dict[str, object]:
    task = _read_task(args.task)
    payload = encode({"checker_sha256": checker_fingerprint(), "task": task_value(task)})
    command = Command(args.project_id, None, Action.INIT, payload)
    raw = command_bytes(command)
    path = _write_exclusive(args.out, raw, maximum=MAX_WIRE_BYTES)
    result = _summary(path, raw, kind="UNSIGNED_REQUEST")
    result.update({"action": command.action.value, "project_id": command.project_id})
    return result


def _prepare(args: argparse.Namespace) -> dict[str, object]:
    project = _project(args)
    action = _action(args.action)
    # A REVISE request is a read-only successor proposal.  Its parent and
    # scope root come from authenticated history even while the working tree
    # is intentionally in SOURCE_DRIFT after the operator edits source files.
    if action is Action.REVISE:
        historical_status = getattr(project, "revision_status", None)
        status = historical_status() if callable(historical_status) else project.status()
    else:
        status = project.status()
    parent = args.parent if args.parent is not None else status["revision"]
    if type(parent) is not str:
        raise LacunaError("INTERNAL_RENDER_ERROR")
    payload = _prepare_payload(args, status, action)
    command = Command(cast(str, status["project_id"]), parent, action, payload)
    raw = command_bytes(command)
    path = _write_exclusive(args.out, raw, maximum=MAX_WIRE_BYTES)
    result = _summary(path, raw, kind="UNSIGNED_REQUEST")
    result.update({"action": command.action.value, "parent": command.parent, "project_id": command.project_id})
    return result


def _sign_request(args: argparse.Namespace) -> dict[str, object]:
    request_raw = _read_bytes(args.request, MAX_WIRE_BYTES)
    command = _decode_request(request_raw)
    signed = sign(command, _read_key(args.key_file))
    raw = encode_signed(signed)
    path = _write_exclusive(args.out, raw, maximum=MAX_WIRE_BYTES)
    result = _summary(path, raw, kind="SIGNED_COMMAND")
    result.update({"action": command.action.value, "project_id": command.project_id})
    return result


def _apply(args: argparse.Namespace) -> dict[str, object]:
    signed = decode_signed(_read_bytes(args.command, MAX_WIRE_BYTES))
    return _project(args).apply(signed)


def _task_factory(args: argparse.Namespace) -> dict[str, object]:
    if args.task_input is not None:
        task = _read_task(args.task_input)
    elif args.adapter == "signal-migration":
        from .signal_migration import OBSERVATIONS, migration_scope

        scope = migration_scope(_absolute(args.source_root))
        profile = Profile.REAL_OWNER if args.profile is None else Profile(args.profile)
        task = Task(scope=replace(scope, profile=profile),
                    runtime=RuntimeSpec("SIGNAL_MIGRATION", tuple(range(128)), OBSERVATIONS),
                    delegates=(), tau_sha256=None, esso_sha256=None)
    else:
        raise LacunaError("TASK_INPUT_REQUIRED")
    if args.adapter is not None:
        adapter = args.adapter.replace("-", "_").upper()
        inputs = task.runtime.inputs if args.inputs is None else _csv_ints(args.inputs)
        observations = task.runtime.observations if args.observations is None else _csv_strings(args.observations)
        task = replace(task, runtime=RuntimeSpec(adapter, inputs, observations))
    if args.profile is not None:
        task = replace(task, scope=replace(task.scope, profile=Profile(args.profile)))
    tau_sha256, esso_sha256 = _tool_pins(args)
    if tau_sha256 is not None or esso_sha256 is not None:
        task = replace(
            task,
            tau_sha256=tau_sha256 if tau_sha256 is not None else task.tau_sha256,
            esso_sha256=esso_sha256 if esso_sha256 is not None else task.esso_sha256,
        )
    raw = encode(task_value(task))
    path = _write_exclusive(args.out, raw, maximum=MAX_JSON_BYTES)
    result = _summary(path, raw, kind="TASK")
    result.update({"adapter": task.runtime.adapter, "profile": task.scope.profile.value, "scope_root": task.scope.root})
    return result


def _tool_pins(args: argparse.Namespace) -> tuple[str | None, str | None]:
    """Resolve explicitly selected native tools into task-owned fingerprints."""
    tau_sha256: str | None = None
    tau_bin = getattr(args, "tau_bin", None)
    if tau_bin is not None:
        from src.tau_composition.runtime import TauQueryError, TauRuntime

        try:
            tau_sha256 = TauRuntime(_absolute(tau_bin)).binary_sha256
        except (OSError, ValueError, TauQueryError) as exc:
            raise LacunaError("SOLVER_MISSING") from exc
    esso_sha256: str | None = None
    esso_root = getattr(args, "esso_root", None)
    if esso_root is not None:
        from .project_bindings import esso_fingerprint

        esso_sha256 = esso_fingerprint(_absolute(esso_root))
    return tau_sha256, esso_sha256


def _candidate_factory(args: argparse.Namespace) -> dict[str, object]:
    from .signal_migration import CandidateMode, migration_candidate

    mode = CandidateMode(args.mode.upper())
    candidate = migration_candidate(mode)
    raw = encode(candidate)
    path = _write_exclusive(args.out, raw, maximum=MAX_JSON_BYTES)
    result = _summary(path, raw, kind="CANDIDATE")
    result.update({"mode": mode.value, "name": candidate.name})
    return result


def _proposals(args: argparse.Namespace) -> dict[str, object]:
    result = _project(args).proposals()
    # Older Project implementations expose the current report inside the
    # packet. Keep the CLI response stable while the root API migrates to a
    # top-level analysis field with its witness and admitted survivors.
    if type(result) is dict and "analysis" not in result:
        packet = result.get("packet")
        if type(packet) is dict and type(packet.get("current")) is dict:
            result["analysis"] = packet["current"]
    return result


def _run_project(args: argparse.Namespace) -> dict[str, object]:
    command = args.project_command
    if command == "prepare-init":
        return _prepare_init(args)
    if command == "prepare":
        return _prepare(args)
    if command == "sign":
        return _sign_request(args)
    if command == "apply":
        return _apply(args)
    if command == "status":
        return _project(args).status()
    if command in ("propose", "proposals"):
        return _proposals(args)
    if command == "witness":
        project = _project(args)
        expected = args.expected_revision
        if expected is None:
            expected = project.state().revision
        return project.admit_witness(_read_witness(args.witness), expected_revision=expected)
    if command == "observe":
        project = _project(args)
        expected = args.expected_revision
        if expected is None:
            status = project.status()
            expected = status.get("revision")
        if type(expected) is not str:
            raise LacunaError("INTERNAL_RENDER_ERROR")
        return project.admit_observation(
            args.context, OutcomeKind(args.kind), args.observation, expected_revision=expected,
        )
    if command == "inspect":
        return _project(args).inspect_candidate(_read_candidate(args.candidate))
    if command == "candidate":
        return _candidate_factory(args)
    if command == "export":
        raw = _project(args).export_bytes()
        path = _write_exclusive(args.out, raw, maximum=MAX_JSON_BYTES * 4)
        return _summary(path, raw, kind="REPLAY_BUNDLE")
    if command == "replaybundle":
        raw = _read_bytes(args.bundle, MAX_JSON_BYTES * 4)
        return replay_bundle(raw, owner_key=args.owner_key, expected_revision=args.expected_revision,
                             tools=_tools(args))
    if command == "task":
        return _task_factory(args)
    raise LacunaError("INVALID_ARGUMENT")


def _json_value(value: object) -> object:
    if value is None or type(value) in (bool, int, str):
        return value
    if type(value) is bytes:
        return base64.b64encode(value).decode("ascii")
    if type(value) is tuple or type(value) is list:
        return [_json_value(item) for item in value]
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise LacunaError("INTERNAL_RENDER_ERROR")
        return {key: _json_value(item) for key, item in value.items()}
    return _json_value(plain(value))


def _emit(value: object) -> None:
    rendered = _json_value(value)
    print(json.dumps(rendered, ensure_ascii=True, sort_keys=True, separators=(",", ":")))


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = _parser().parse_args(list(argv) if argv is not None else None)
        _emit(_run_project(args))
        return 0
    except LacunaError as error:
        _emit({"code": error.code, "status": "REJECTED"})
        return 2
    except OSError:
        _emit({"code": "IO_ERROR", "status": "REJECTED"})
        return 2


__all__ = ["main"]
