#!/usr/bin/env python3
"""Stable local JSON CLI for the bounded ZenoLacuna finite-model shell."""

from __future__ import annotations

import argparse
import json
import os
import stat
import subprocess
import sys
import tempfile
from dataclasses import fields, is_dataclass
from enum import Enum
from pathlib import Path
from typing import NoReturn, Sequence

_EARLY_ARGUMENTS = sys.argv[1:]
if _EARLY_ARGUMENTS and _EARLY_ARGUMENTS[0] == "project":
    # Project code must be imported only in a fresh worker.  The worker owns
    # the source manifest and captures it before importing the project package;
    # an isolated interpreter also prevents an unrelated parent process from
    # reusing a timestamp-valid bytecode cache.
    with tempfile.TemporaryDirectory(prefix="zenolacuna-cli-") as cache_root:
        _cache_prefix = str(Path(cache_root) / "pycache")
        _entrypoint = Path(__file__).with_name("zenolacuna_project_entry.py")
        raise SystemExit(subprocess.call(
            [
                sys.executable,
                "-I",
                "-B",
                "-X",
                f"pycache_prefix={_cache_prefix}",
                str(_entrypoint),
                *_EARLY_ARGUMENTS[1:],
            ],
        ))

_REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from src.tau_workbench.programs import MAX_SOURCE_BYTES, Program  # noqa: E402
from src.zenolacuna.codec import (  # noqa: E402
    MAX_JSON_BYTES,
    decode_candidate,
    decode_decision,
    decode_scope,
)
from src.zenolacuna.engine import analyze  # noqa: E402
from src.zenolacuna.model import LacunaError, Profile  # noqa: E402
from src.zenolacuna.ports.programs import replay_pipeline  # noqa: E402
from src.zenolacuna.shell import ShellResult, Store  # noqa: E402


class _Parser(argparse.ArgumentParser):
    def error(self, _message: str) -> NoReturn:
        raise LacunaError("INVALID_ARGUMENT")


def _host_arguments(parser: argparse.ArgumentParser, *, inherited: bool) -> None:
    default = argparse.SUPPRESS if inherited else str(_REPOSITORY_ROOT)
    parser.add_argument("--source-root", default=default, metavar="PATH")
    profile_default = argparse.SUPPRESS if inherited else Profile.SIMULATED.value
    parser.add_argument(
        "--profile",
        choices=tuple(profile.value for profile in Profile),
        default=profile_default,
        metavar="PROFILE",
    )


def _parser() -> _Parser:
    parser = _Parser(prog="zenolacuna")
    _host_arguments(parser, inherited=False)
    commands = parser.add_subparsers(dest="command", required=True)
    describe = commands.add_parser("describe", help="describe the finite local profile")
    _host_arguments(describe, inherited=True)
    analyze = commands.add_parser("analyze", help="create a run from a finite scope")
    _host_arguments(analyze, inherited=True)
    analyze.add_argument("--task", required=True, metavar="TASK.json")
    analyze.add_argument("--out", required=True, metavar="RUN")
    answer = commands.add_parser("answer", help="apply one simulated decision")
    _host_arguments(answer, inherited=True)
    answer.add_argument("--run", required=True, metavar="RUN")
    answer.add_argument("--decision", required=True, metavar="DECISION.json")
    assess = commands.add_parser("assess-repair", help="assess and persist a valid candidate")
    _host_arguments(assess, inherited=True)
    assess.add_argument("--run", required=True, metavar="RUN")
    assess.add_argument("--candidate", required=True, metavar="CANDIDATE.json")
    programs = commands.add_parser("check-programs", help="replay a restricted source-explicit pipeline")
    _host_arguments(programs, inherited=True)
    selector = programs.add_mutually_exclusive_group(required=True)
    selector.add_argument("--task", metavar="TASK.json")
    selector.add_argument("--run", metavar="RUN")
    programs.add_argument("--candidate", metavar="CANDIDATE.json")
    programs.add_argument("--expected-revision", metavar="REVISION")
    programs.add_argument("--bits", required=True, type=int, metavar="N")
    programs.add_argument("--program", action="append", default=[], metavar="PROGRAM.py")
    for name, help_text in (
        ("replay", "rerun the finite checker"),
        ("status", "recompute current run status"),
        ("cancel", "persist a cancelled lifecycle revision"),
        ("resume", "persist an explicit lifecycle resume revision"),
    ):
        command = commands.add_parser(name, help=help_text)
        _host_arguments(command, inherited=True)
        command.add_argument("--run", required=True, metavar="RUN")
    return parser


def _command_names(parser: _Parser) -> tuple[str, ...]:
    for action in parser._actions:
        choices = getattr(action, "choices", None)
        if action.dest == "command" and type(choices) is dict and all(
            type(name) is str for name in choices
        ):
            return tuple(sorted(choices))
    raise LacunaError("INTERNAL_RENDER_ERROR")


def _read_bytes(path: str, maximum: int) -> bytes:
    input_path = Path(os.path.abspath(path))
    try:
        details = os.lstat(input_path)
    except FileNotFoundError as exc:
        raise LacunaError("INPUT_MISSING") from exc
    if stat.S_ISLNK(details.st_mode):
        raise LacunaError("INPUT_SYMLINK")
    if not stat.S_ISREG(details.st_mode) or details.st_size > maximum:
        raise LacunaError("INPUT_INVALID")
    descriptor = os.open(input_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode) or opened.st_size > maximum:
            raise LacunaError("INPUT_INVALID")
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
            raise LacunaError("INPUT_INVALID")
        return result
    finally:
        os.close(descriptor)


def _read_input(path: str) -> bytes:
    return _read_bytes(path, MAX_JSON_BYTES)


def _read_program(path: str) -> bytes:
    return _read_bytes(path, MAX_SOURCE_BYTES)


def _json_value(value: object) -> object:
    if value is None or type(value) in (bool, int, str):
        return value
    if isinstance(value, Enum):
        return value.value
    if is_dataclass(value):
        return {field.name: _json_value(getattr(value, field.name)) for field in fields(value)}
    if type(value) is tuple or type(value) is list:
        return [_json_value(item) for item in value]
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise LacunaError("INTERNAL_RENDER_ERROR")
        return {key: _json_value(item) for key, item in value.items()}
    raise LacunaError("INTERNAL_RENDER_ERROR")


def _emit(value: object) -> None:
    rendered = _json_value(value)
    print(json.dumps(rendered, ensure_ascii=True, sort_keys=True, separators=(",", ":")))


def _result_value(result: ShellResult) -> dict[str, object]:
    return {
        "code": result.code,
        "report": _json_value(result.report),
        "revision": result.revision,
        "status": result.status,
    }


def _describe(parser: _Parser) -> dict[str, object]:
    return {
        "authority": "NONE",
        "checker_compatibility": "CHECKER_DRIFT_REQUIRES_FRESH_RUN",
        "claim": "FINITE_MODEL_ONLY",
        "commands": _command_names(parser),
        "project_workflow": {
            "command": "zenolacuna project",
            "authority": "REAL_OWNER_SIGNED_ED25519",
            "execution": "FRESH_SOURCE_PROCESS",
            "evidence": "DURABLE_SQLITE_SIGNED_EVENT_HISTORY",
        },
        "profiles": {
            "REAL_OWNER": "UNAVAILABLE_TRUSTED_HOST_PORT",
            "SIMULATED": "actor=simulated-owner",
        },
        "persistence": "COOPERATIVE_LOCAL_FILESYSTEM",
        "replay_candidate": "MODEL_SELECTED_CANDIDATE when no assessed candidate exists",
        "run_program_replay": "READ_ONLY_REPORT_NOT_PERSISTED_RUNTIME_CERTIFICATE",
        "scope_kinds": ("FINITE_RELATION", "FINITE_STATE_GRAPH", "BOUNDED_HISTORY"),
    }


def _store(args: argparse.Namespace) -> Store:
    return Store(
        args.run,
        source_root=args.source_root,
        profile=Profile(args.profile),
    )


def _execute(args: argparse.Namespace, parser: _Parser) -> dict[str, object]:
    if args.command == "describe":
        return _describe(parser)
    if args.command == "analyze":
        scope = decode_scope(_read_input(args.task))
        store = Store.initialize(
            args.out,
            scope,
            source_root=args.source_root,
            profile=Profile(args.profile),
        )
        return _result_value(store.status())
    if args.command == "check-programs":
        if not 1 <= args.bits <= 8 or not 1 <= len(args.program) <= 4:
            raise LacunaError("INVALID_ARGUMENT")
        if args.run is not None:
            if args.candidate is not None or args.expected_revision is None:
                raise LacunaError("INVALID_ARGUMENT")
            programs = tuple(
                Program(f"program_{index}", _read_program(path))
                for index, path in enumerate(args.program, start=1)
            )
            return _result_value(
                _store(args).check_programs(
                    programs,
                    args.bits,
                    expected_revision=args.expected_revision,
                )
            )
        if args.task is None or args.candidate is None or args.expected_revision is not None:
            raise LacunaError("INVALID_ARGUMENT")
        scope = decode_scope(_read_input(args.task))
        if scope.profile is not Profile(args.profile):
            raise LacunaError("AUTHORIZATION_PROFILE_MISMATCH")
        if scope.profile is Profile.REAL_OWNER:
            raise LacunaError("UNAUTHORIZED")
        candidate = decode_candidate(_read_input(args.candidate))
        programs = tuple(
            Program(f"program_{index}", _read_program(path))
            for index, path in enumerate(args.program, start=1)
        )
        report = replay_pipeline(
            scope,
            analyze(scope).survivors,
            candidate,
            programs,
            args.bits,
            tuple(range(1 << args.bits)),
        )
        rendered = _json_value(report)
        if type(rendered) is not dict:
            raise LacunaError("INTERNAL_RENDER_ERROR")
        return rendered
    store = _store(args)
    if args.command == "answer":
        raw = _read_input(args.decision)
        return _result_value(store.answer(decode_decision(raw), raw))
    if args.command == "assess-repair":
        raw = _read_input(args.candidate)
        return _result_value(store.assess_repair(decode_candidate(raw), raw))
    if args.command == "replay":
        return _result_value(store.replay())
    if args.command == "status":
        return _result_value(store.status())
    if args.command == "cancel":
        return _result_value(store.cancel())
    if args.command == "resume":
        return _result_value(store.resume())
    raise LacunaError("INVALID_ARGUMENT")


def main(argv: Sequence[str] | None = None) -> int:
    selected = list(argv) if argv is not None else sys.argv[1:]
    # Keep the original finite-model CLI grammar stable.  The signed-project
    # workflow has its own parser and is selected before argparse sees the
    # legacy command names.
    if selected and selected[0] == "project":
        from src.zenolacuna.project_cli import main as project_main

        return project_main(selected[1:])
    try:
        parser = _parser()
        args = parser.parse_args(selected)
        _emit(_execute(args, parser))
        return 0
    except LacunaError as error:
        _emit({"code": error.code, "status": "REJECTED"})
        return 2
    except OSError:
        _emit({"code": "IO_ERROR", "status": "REJECTED"})
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
