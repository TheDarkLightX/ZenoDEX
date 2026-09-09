#!/usr/bin/env python3
"""Validate changed-file hygiene evidence and execute its pinned pytest nodes."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.check_test_hygiene_v1 import (
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    REPO_ROOT,
    ChangedPathV1,
    TestHygieneError,
    check_repository,
    collect_git_changed_paths,
)
from tools.test_hygiene_evidence_v1 import load_packet_with_mutations
from tools.test_hygiene_model_v1 import PacketV1, load_contract
from tools.thv1_mutation_ledger_v1 import (
    CONTRACT_RELATIVE_V1,
    EVIDENCE_DIR_RELATIVE_V1,
    LedgerError,
    LedgerOptionsV1,
    ledger_exit_code_v1,
    run_ledger_v1,
)


def run_declared_pytest_nodes(
    node_ids: Sequence[str],
    *,
    repo_root: Path = REPO_ROOT,
    python_executable: str = sys.executable,
) -> None:
    """Run already-validated node IDs as an argv vector without shell parsing."""

    if not node_ids:
        return
    subprocess.run(
        [python_executable, "-m", "pytest", "-q", *node_ids],
        cwd=repo_root,
        check=True,
        stdout=sys.stderr,
    )


def _parse_changed_file(value: str) -> ChangedPathV1:
    status, separator, path = value.partition(":")
    if not separator:
        raise TestHygieneError("--changed-file must use STATUS:path")
    return ChangedPathV1(status=status, path=path)


def _resolve_head_commit(repo_root: Path) -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "--verify", "HEAD^{commit}"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise TestHygieneError(f"mutation replay could not resolve HEAD: {exc}") from exc


def _commit_bytes(repo_root: Path, commit: str, path: str) -> bytes:
    try:
        return subprocess.run(
            ["git", "show", f"{commit}:{path}"],
            cwd=repo_root,
            capture_output=True,
            check=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as exc:
        raise TestHygieneError(f"mutation replay {path} is absent from commit {commit}") from exc


def _require_worktree_bytes(
    repo_root: Path,
    commit: str,
    path: str,
    *,
    label: str,
) -> bytes:
    worktree_path = repo_root / path
    if not worktree_path.is_file():
        raise TestHygieneError(f"mutation replay missing worktree {label}: {path}")
    committed = _commit_bytes(repo_root, commit, path)
    if worktree_path.read_bytes() != committed:
        raise TestHygieneError(
            f"mutation replay worktree {label} differs from commit {commit}: {path}"
        )
    return committed


def _standard_paths(repo_root: Path) -> tuple[Path, Path]:
    return repo_root / CONTRACT_RELATIVE_V1, repo_root / EVIDENCE_DIR_RELATIVE_V1


def _require_standard_replay_paths(
    repo_root: Path,
    contract_path: Path,
    evidence_dir: Path,
) -> None:
    standard_contract, standard_evidence = _standard_paths(repo_root)
    if contract_path.resolve() != standard_contract.resolve() or evidence_dir.resolve() != (
        standard_evidence.resolve()
    ):
        raise TestHygieneError(
            "--replay-mutations requires the standard contract and evidence paths"
        )


def _load_replay_packets(
    *,
    repo_root: Path,
    commit: str,
    evidence_ids: Sequence[str],
) -> tuple[PacketV1, ...]:
    contract_path, evidence_dir = _standard_paths(repo_root)
    _require_worktree_bytes(
        repo_root,
        commit,
        CONTRACT_RELATIVE_V1,
        label="contract",
    )
    contract = load_contract(contract_path)
    packets: list[PacketV1] = []
    for evidence_id in evidence_ids:
        relative_packet = f"{EVIDENCE_DIR_RELATIVE_V1}/{evidence_id}.json"
        _require_worktree_bytes(
            repo_root,
            commit,
            relative_packet,
            label="packet",
        )
        packet, rows = load_packet_with_mutations(
            evidence_dir / f"{evidence_id}.json",
            contract,
        )
        if packet.evidence_id != evidence_id:
            raise TestHygieneError(
                f"mutation replay packet {relative_packet} declares {packet.evidence_id}"
            )
        if "mutation" in packet.families and not any(row.kind == "mechanical" for row in rows):
            raise TestHygieneError(
                f"{packet.evidence_id}: mutation evidence requires a mechanical row"
            )
        for label, pins in (("source", packet.source_pins), ("test", packet.test_pins)):
            for pin in pins:
                committed = _require_worktree_bytes(
                    repo_root,
                    commit,
                    pin.path,
                    label=label,
                )
                if hashlib.sha256(committed).hexdigest() != pin.sha256:
                    raise TestHygieneError(
                        f"{packet.evidence_id}: committed {label} sha256 drift for {pin.path}"
                    )
        packets.append(packet)
    return tuple(packets)


def _replay_mutations(
    *,
    repo_root: Path,
    commit: str,
    packets: Sequence[PacketV1],
    python_executable: str,
) -> dict[str, object]:
    counts = {
        "mechanical": 0,
        "killed": 0,
        "narrative": 0,
        "legacy": 0,
        "survived": 0,
        "errors": 0,
        "ledger_nonzero": 0,
    }
    with tempfile.TemporaryDirectory(prefix="thv1-gate-") as directory:
        workdir = Path(directory)
        for packet in packets:
            ledger_report = run_ledger_v1(
                LedgerOptionsV1(
                    repo_root=repo_root,
                    packet=packet.evidence_id,
                    rev=commit,
                    python=python_executable,
                    workdir=workdir,
                    keep=False,
                    packet_file=None,
                    filters=(),
                )
            )
            for key in ("mechanical", "killed", "narrative", "legacy", "survived", "errors"):
                counts[key] += cast(int, ledger_report[key])
            if ledger_exit_code_v1(ledger_report) != 0:
                counts["ledger_nonzero"] += 1
    replay_ok = counts["survived"] == 0 and counts["errors"] == 0 and counts["ledger_nonzero"] == 0
    return {
        **counts,
        "subject_commit": commit,
        "ok": replay_ok,
    }


def _run_gate(
    *,
    repo_root: Path,
    contract_path: Path,
    evidence_dir: Path,
    changed_paths: Sequence[ChangedPathV1],
    replay_mutations: bool,
    python_executable: str = sys.executable,
    subject_commit: str | None = None,
) -> dict[str, object]:
    if replay_mutations:
        _require_standard_replay_paths(repo_root, contract_path, evidence_dir)
        commit = _resolve_head_commit(repo_root) if subject_commit is None else subject_commit
    report = check_repository(
        repo_root=repo_root,
        contract_path=contract_path,
        evidence_dir=evidence_dir,
        changed_paths=changed_paths,
    )
    if replay_mutations:
        packets = _load_replay_packets(
            repo_root=repo_root,
            commit=commit,
            evidence_ids=cast(list[str], report["selected_evidence_ids"]),
        )
    run_declared_pytest_nodes(
        cast(list[str], report["pytest_node_ids"]),
        repo_root=repo_root,
        python_executable=python_executable,
    )
    if replay_mutations:
        report["mutation_replay"] = _replay_mutations(
            repo_root=repo_root,
            commit=commit,
            packets=packets,
            python_executable=python_executable,
        )
        report["ok"] = cast(dict[str, object], report["mutation_replay"])["ok"]
    return report


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--evidence-dir", type=Path, default=DEFAULT_EVIDENCE_DIR)
    parser.add_argument("--base-ref")
    parser.add_argument("--changed-file", action="append", default=[])
    parser.add_argument("--replay-mutations", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.base_ref and args.changed_file:
            raise TestHygieneError("use either --base-ref or --changed-file")
        subject_commit = _resolve_head_commit(REPO_ROOT) if args.replay_mutations else None
        if args.base_ref:
            changed = collect_git_changed_paths(
                REPO_ROOT,
                cast(str, args.base_ref),
                head_ref="HEAD" if subject_commit is None else subject_commit,
            )
        else:
            changed = tuple(
                _parse_changed_file(value) for value in cast(list[str], args.changed_file)
            )
        report = _run_gate(
            repo_root=REPO_ROOT,
            contract_path=cast(Path, args.contract),
            evidence_dir=cast(Path, args.evidence_dir),
            changed_paths=changed,
            replay_mutations=cast(bool, args.replay_mutations),
            subject_commit=subject_commit,
        )
    except (LedgerError, TestHygieneError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as exc:
        print(
            f"error: declared hygiene evidence failed with exit {exc.returncode}", file=sys.stderr
        )
        return exc.returncode or 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif not args.replay_mutations:
        print(
            "test-hygiene-v1: evidence passed "
            f"critical={report['critical_path_count']} "
            f"nodes={len(cast(list[str], report['pytest_node_ids']))}"
        )
    else:
        replay = cast(dict[str, object], report["mutation_replay"])
        print(
            "test-hygiene-v1: mutation replay "
            f"{'passed' if replay['ok'] is True else 'failed'} "
            f"mechanical={replay['mechanical']} killed={replay['killed']} "
            f"narrative={replay['narrative']} legacy={replay['legacy']} "
            f"subject={replay['subject_commit']}"
        )
    if args.replay_mutations:
        return 0 if report["ok"] is True else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
