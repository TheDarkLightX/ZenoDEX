#!/usr/bin/env python3
"""Deterministic builder for the O-008 formal-cycle evidence packet (v3).

The packet JSON and its Markdown companion are projections of one exact source
commit S. This tool reads S through Git, optionally executes the recorded proof
tools against a worktree that equals S, and writes the canonical projection.

JSON contract:
    stdout  one compact JSON status line.
    exit 0  packet written, or ``--check`` found the on-disk files byte-identical.
    exit 1  the subject is inconsistent (projection rejected), the worktree drifted
            from S when ``--replay`` was requested, or ``--check`` found drift.
    exit 2  infrastructure failure (``INFRA_*``).

The builder refuses to write any output when the projection is rejected.
Authority: NONE.
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
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--subject-commit", required=True)
    parser.add_argument("--created-date", required=True)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--esso-python", default=None)
    parser.add_argument("--esso-pythonpath", default=None)
    parser.add_argument("--output-json", type=Path, default=Path(core.PACKET_JSON_PATH_V1))
    parser.add_argument("--output-md", type=Path, default=Path(core.PACKET_MD_PATH_V1))
    parser.add_argument("--check", action="store_true", help="compare instead of writing")
    return parser.parse_args(argv)


def _require_worktree_equals_subject(root: Path, snapshot: core.SubjectSnapshotV1) -> None:
    for path in core.SOURCE_PIN_PATHS_V1:
        blob = snapshot.blobs.get(path)
        raw = shell.working_bytes_v1(root, path)
        if blob is None or raw is None or core.sha256_hex_v1(raw) != blob.sha256:
            core._reject("REPLAY_REFUSED_WORKTREE_DRIFT", path, "worktree differs from subject")


def _author_record(root: Path, snapshot: core.SubjectSnapshotV1, args: argparse.Namespace) -> dict[str, Any]:
    if not args.replay:
        return {"status": core.REPLAY_STATUS_NOT_RUN_V1}
    _require_worktree_equals_subject(root, snapshot)
    preview = core.project_packet_v1(
        snapshot, created_date=args.created_date, author_replay_record={"status": "NOT_RUN"}
    )
    with tempfile.TemporaryDirectory(prefix="o008-build-replay-") as tmp:
        environment = shell.prepare_replay_environment_v1(
            python=args.python,
            esso_python=args.esso_python,
            esso_pythonpath=args.esso_pythonpath,
            tmp_dir=Path(tmp),
        )
        observations = shell.run_proof_replay_v1(root, environment)
    evaluation = core.evaluate_proof_replay_v1(preview, observations)
    if evaluation.status != core.REPLAY_STATUS_EXECUTED_PASS_V1:
        first = evaluation.errors[0] if evaluation.errors else None
        detail = f"{first.code} at {first.path}: {first.detail}" if first else evaluation.status
        core._reject("REPLAY_EXECUTED_FAIL", "proof_replay", detail)
    # Only the deterministic subset is recorded: raw stdout/stderr hashes carry timings.
    # The toolchain is derived from the replayed tools, never from this builder process.
    runs = [
        {key: run[key] for key in ("command_id", "exit_code", "comparable")}
        for run in evaluation.runs
    ]
    return {"status": "EXECUTED", "runs": runs, "toolchain": dict(evaluation.toolchain)}


def build_v1(args: argparse.Namespace) -> dict[str, Any]:
    root = shell.resolve_repo_root_v1(args.root)
    git = shell.GitReadPortV1(root)
    snapshot = shell.read_subject_snapshot_v1(git, args.subject_commit)
    record = _author_record(root, snapshot, args)
    packet = core.project_packet_v1(snapshot, created_date=args.created_date, author_replay_record=record)
    json_bytes = core.canonical_packet_bytes_v1(packet)
    # Render from the decoded canonical bytes so the builder and the checker see
    # byte-identical inputs (key order included).
    md_bytes = core.render_markdown_v1(core.decode_packet_v1(json_bytes)).encode("utf-8")
    json_path = root / args.output_json
    md_path = root / args.output_md
    if args.check:
        committed = shell.working_bytes_v1(root, str(args.output_json))
        if committed is not None:
            recorded = core.decode_json_object_v1(committed, context=str(args.output_json), require_canonical=False)
            recorded_status = recorded.get("proof_replay", {}).get("author_record", {}).get("status")
            if recorded_status != record["status"]:
                core._reject(
                    "CHECK_MODE_MISMATCH",
                    str(args.output_json),
                    f"committed author record is {recorded_status}; this check runs {record['status']} (use --replay accordingly)",
                )
        drift = [
            str(path)
            for path, expected in ((args.output_json, json_bytes), (args.output_md, md_bytes))
            if shell.working_bytes_v1(root, str(path)) != expected
        ]
        return {"ok": not drift, "mode": "check", "drift": drift, "subject_commit": args.subject_commit}
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_bytes(json_bytes)
    md_path.write_bytes(md_bytes)
    return {
        "ok": True,
        "mode": "write",
        "subject_commit": args.subject_commit,
        "packet_sha256": core.sha256_hex_v1(json_bytes),
        "markdown_sha256": core.sha256_hex_v1(md_bytes),
        "author_record_status": record["status"],
    }


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        status = build_v1(args)
    except core.AdmissionRejectV1 as exc:
        status = {
            "ok": False,
            "mode": "check" if args.check else "write",
            "error": {"code": exc.code, "path": exc.path, "detail": exc.detail},
        }
    except OSError as exc:
        status = {"ok": False, "error": {"code": "INFRA_IO_ERROR", "path": str(args.root), "detail": type(exc).__name__}}
    sys.stdout.write(json.dumps(status, sort_keys=True, separators=(",", ":")) + "\n")
    if status.get("ok"):
        return 0
    error = status.get("error")
    return 2 if isinstance(error, dict) and str(error.get("code", "")).startswith("INFRA_") else 1


if __name__ == "__main__":
    raise SystemExit(main())
