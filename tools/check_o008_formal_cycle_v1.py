#!/usr/bin/env python3
"""Fail-closed admission checker for the O-008 formal-cycle evidence packet (v3).

JSON contract:
    stdout  exactly one compact JSON report (schema
            ``zenodex/o008-formal-cycle-admission-report/v3``) followed by a newline.
    stderr  empty except argparse usage text.
    exit 0  the committed packet at P is admitted against its subject commit S, the
            HEAD and worktree copies of every pinned source still equal S, and proof
            replay is NOT_RUN or EXECUTED_PASS.
    exit 1  rejected, drifted, EXECUTED_FAIL, or REFUSED.
    exit 2  infrastructure failure (``INFRA_*``: Git unavailable, root not a Git
            top-level, replay tool missing or timed out, I/O error).

The packet admitted is the committed blob at P (the last commit touching the packet
path in HEAD's history), never the worktree file. The report's ``claim_ceiling`` is
emitted from module constants; no packet content can raise it. Authority: NONE.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from typing import Any

if str(Path(__file__).resolve().parents[1]) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o008_formal_cycle_admission_v1 as core
from tools import o008_formal_cycle_shell_v1 as shell

DEFAULT_ROOT = Path(__file__).resolve().parents[1]


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT, help="absolute Git top-level")
    parser.add_argument("--packet-commit", default=None, help="expected packet commit P (40 hex)")
    parser.add_argument("--replay", action="store_true", help="execute the recorded proof tools")
    parser.add_argument("--python", default=sys.executable, help="interpreter for pytest replays")
    parser.add_argument("--esso-python", default=None, help="interpreter with ESSO importable")
    parser.add_argument("--esso-pythonpath", default=None, help="PYTHONPATH for ESSO replays")
    return parser.parse_args(argv)


def _replay(
    root: Path,
    packet: dict[str, Any],
    outcome: core.AdmissionOutcomeV1,
    args: argparse.Namespace,
) -> tuple[core.ReplayEvaluationV1, tuple[core.AdmissionErrorV1, ...]]:
    if not outcome.packet_admitted:
        return core.ReplayEvaluationV1(core.REPLAY_STATUS_REFUSED_V1, (), ()), (
            core.AdmissionErrorV1("REPLAY_REFUSED_NOT_ADMITTED", "proof_replay", "packet rejected"),
        )
    if not outcome.current_applicable:
        return core.ReplayEvaluationV1(core.REPLAY_STATUS_REFUSED_V1, (), ()), (
            core.AdmissionErrorV1("REPLAY_REFUSED_WORKTREE_DRIFT", "proof_replay", "sources drifted"),
        )
    with tempfile.TemporaryDirectory(prefix="o008-replay-") as tmp:
        environment = shell.ReplayEnvironmentV1(
            python=args.python,
            esso_python=args.esso_python,
            esso_pythonpath=args.esso_pythonpath,
            tmp_dir=Path(tmp),
        )
        observations = shell.run_proof_replay_v1(root, environment)
    evaluation = core.evaluate_proof_replay_v1(packet, observations)
    return evaluation, core.compare_author_record_v1(packet, evaluation)


def run_checker_v1(args: argparse.Namespace) -> dict[str, Any]:
    """Wire the shell reads into the pure core and return the report."""

    packet_commit: str | None = None
    subject_commit: str | None = None
    head: str | None = None
    executing: dict[str, str] = {}
    not_run = core.ReplayEvaluationV1(core.REPLAY_STATUS_NOT_RUN_V1, (), ())
    try:
        root = shell.resolve_repo_root_v1(args.root)
        git = shell.GitReadPortV1(root)
        head = shell.head_commit_v1(git)
        tools = shell.read_executing_tools_v1(Path(__file__))
        executing = dict(tools.sha256_by_path)
        topology = shell.read_packet_topology_v1(git, root, head)
        packet_commit = topology.packet_commit
        if args.packet_commit is not None and args.packet_commit != packet_commit:
            core._reject("PACKET_COMMIT_MISMATCH", packet_commit, str(args.packet_commit))
        packet = core.decode_packet_v1(topology.packet_blob_at_p)
        subject_commit = str(packet.get("subject_commit"))
        snapshot = shell.read_subject_snapshot_v1(git, subject_commit)
        current = shell.read_current_source_state_v1(git, root, head, core.applicability_paths_v1(packet))
        context = core.AdmissionContextV1(snapshot, topology, current, tools)
        outcome = core.admit_packet_v1(packet, context)
        replay, extra = (_replay(root, packet, outcome, args) if args.replay else (not_run, ()))
        return core.render_report_v1(
            core.ReportInputsV1(
                packet_commit, subject_commit, head, outcome, replay, executing, tuple(extra)
            )
        )
    except core.AdmissionRejectV1 as exc:
        error = core.AdmissionErrorV1(exc.code, exc.path, exc.detail)
        infra = error if exc.code.startswith("INFRA_") else None
        return core.render_report_v1(
            core.ReportInputsV1(
                packet_commit,
                subject_commit,
                head,
                None,
                not_run,
                executing,
                () if infra else (error,),
                infra,
            )
        )
    except OSError as exc:
        io_error = core.AdmissionErrorV1("INFRA_IO_ERROR", str(args.root), type(exc).__name__)
        return core.render_report_v1(
            core.ReportInputsV1(
                packet_commit, subject_commit, head, None, not_run, executing, (), io_error
            )
        )


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    report = run_checker_v1(args)
    sys.stdout.write(json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n")
    return core.exit_code_for_report_v1(report)


if __name__ == "__main__":
    raise SystemExit(main())
