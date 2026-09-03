#!/usr/bin/env python3
"""Execute the declared mutation rows of a Test Hygiene Contract V1 evidence packet.

A THV1 packet declares ``mutations: [{description, killed_by, mutant | narrative}]``.
Before this ledger existed ``killed_by`` was a string no gate executed, and reviews
found declared killers that did not kill (campaign finding G7). The ledger makes a
mechanical row executable and executed, so a packet cannot claim a killer that does
not kill:

1. ``git archive <rev>`` of the subject repository is extracted into a fresh copy per
   row under ``<workdir>/<packet>/row-NN/`` (default ``$TMPDIR/thv1-ledger``); the
   worktree is never read for sources and never written;
2. the copy's pinned bytes must equal the packet's pins for the mutated path and the
   killer's file (``PIN_DRIFT`` otherwise), the ``needle`` must occur exactly once in
   ``mutant.path`` (``NEEDLE_COUNT`` otherwise), and the ``replacement`` is written in
   its place; the mutated file's sha256 is recorded;
3. the killer runs in the copy: a pinned pytest node (``<python> -m pytest -q -x -p
   no:cacheprovider <node>`` with ``PYTHONDONTWRITEBYTECODE=1``) or, for
   ``<crate>/tests/<target>.rs::<filter>`` killers, ``cargo test --offline --locked
   --test <target> <filter>`` in the crate directory with ``CARGO_TARGET_DIR`` under
   the work directory (or the caller's);
4. the same killer must PASS on an unmutated control copy first (``CONTROL_FAILED``
   otherwise: a killer that fails for reasons unrelated to the mutant proves
   nothing) and must then FAIL on the mutated copy: pytest exit 1 or a cargo
   ``test result: FAILED`` summary is ``KILLED``; exit 0 is ``SURVIVED`` (the row
   fails and the ledger exits 1); any other failure (collection error, compile
   error) is ``UNVIABLE`` and also fails the row.

Narrative rows (``narrative: true``) and legacy string-only rows (packets cut before
the mechanical cutover) are listed with their own verdict but never counted as
killed or survived.

Output: one JSON object on stdout, ``{schema, packet, subject_commit, rows,
mechanical, narrative, legacy, killed, survived, errors}`` with rows sorted by
(description, killer) and without timestamps; logs and wall-clock go to stderr.
Exit 0 only when every mechanical row is ``KILLED``; 1 when a row survived or
errored; 2 on a packet, repository, or tool failure.

Nonclaim: the ledger executes declared rows only; it does not measure mutants nobody
declared, and a green ledger says nothing about code no row names.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Callable, Mapping, Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.test_hygiene_evidence_v1 import (
    MutationRowV1,
    load_packet_with_mutations,
    needle_occurrences_v1,
)
from tools.test_hygiene_model_v1 import (
    REPO_ROOT,
    PacketV1,
    TestHygieneError,
    load_contract,
    sha256_file,
)

LEDGER_SCHEMA_V1 = "zenodex/thv1-mutation-ledger/v1"
EVIDENCE_DIR_RELATIVE_V1 = "tests/evidence/test_hygiene"
CONTRACT_RELATIVE_V1 = "tools/test_hygiene_contract_v1.json"
DEFAULT_TIMEOUT_SECONDS_V1 = 1800

VERDICT_KILLED = "KILLED"
VERDICT_SURVIVED = "SURVIVED"
VERDICT_NARRATIVE = "NARRATIVE"
VERDICT_LEGACY = "LEGACY"
VERDICT_CONTROL_FAILED = "CONTROL_FAILED"
VERDICT_PIN_DRIFT = "PIN_DRIFT"
VERDICT_NEEDLE_COUNT = "NEEDLE_COUNT"
VERDICT_TIMEOUT = "TIMEOUT"
VERDICT_UNVIABLE = "UNVIABLE"
ERROR_VERDICTS = frozenset(
    {
        VERDICT_CONTROL_FAILED,
        VERDICT_PIN_DRIFT,
        VERDICT_NEEDLE_COUNT,
        VERDICT_TIMEOUT,
        VERDICT_UNVIABLE,
    }
)
REPORT_KEYS_V1 = (
    "schema",
    "packet",
    "subject_commit",
    "rows",
    "mechanical",
    "narrative",
    "legacy",
    "killed",
    "survived",
    "errors",
)
ROW_KEYS_V1 = (
    "description",
    "killer",
    "mutation",
    "mutant_sha256",
    "exit",
    "seconds",
    "verdict",
)

_CARGO_SUMMARY_RE = re.compile(r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed;", re.M)
_PYTEST_TESTS_FAILED_EXIT = 1


class LedgerError(RuntimeError):
    """Raised when the packet, the subject repository, or the tool chain fails closed."""


# ---------------------------------------------------------------------------
# Functional core: killers, mutants, verdicts, report
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True, slots=True)
class PytestKillerV1:
    node_id: str

    @property
    def test_path(self) -> str:
        return self.node_id.split("::", 1)[0]


@dataclasses.dataclass(frozen=True, slots=True)
class CargoKillerV1:
    test_path: str
    filter: str
    lib: bool = False

    @property
    def crate_dir(self) -> str:
        if self.lib:
            return self.test_path.rsplit("/src/", 1)[0]
        return self.test_path.rsplit("/tests/", 1)[0]

    @property
    def target(self) -> str:
        return Path(self.test_path).stem


KillerV1 = PytestKillerV1 | CargoKillerV1


def parse_killer_v1(killed_by: str) -> KillerV1:
    """Classify a ``killed_by`` string: a pytest node id, ``<crate>/tests/<target>.rs::<filter>``
    (an integration test) or ``<crate>/src/<file>.rs::<filter>`` (a crate unit test)."""

    path, separator, rest = killed_by.partition("::")
    if not separator or not rest or any(character.isspace() for character in killed_by):
        raise LedgerError(f"malformed killer: {killed_by!r}")
    if path.endswith(".py"):
        return PytestKillerV1(killed_by)
    if path.endswith(".rs") and "/tests/" in path:
        return CargoKillerV1(path, rest)
    if path.endswith(".rs") and "/src/" in path:
        # A guard whose only honest test is a crate unit test: the check it protects is
        # private, and no accepted certificate can reach it from an integration test
        # (opus2 P40 P2-2/P2-3). Without this form such a guard could carry no mechanical
        # row at all, which is how one shipped with a test that never called it.
        return CargoKillerV1(path, rest, lib=True)
    raise LedgerError(f"unsupported killer form: {killed_by!r}")


def pytest_argv_v1(python: str, killer: PytestKillerV1) -> tuple[str, ...]:
    return (python, "-m", "pytest", "-q", "-x", "-p", "no:cacheprovider", killer.node_id)


def cargo_argv_v1(killer: CargoKillerV1) -> tuple[str, ...]:
    if killer.lib:
        return ("cargo", "test", "--offline", "--locked", "--lib", "--", killer.filter)
    return ("cargo", "test", "--offline", "--locked", "--test", killer.target, killer.filter)


def apply_mutant_v1(text: str, needle: str, replacement: str) -> str:
    """Return ``text`` with its single ``needle`` occurrence replaced; refuse any other count."""

    count = needle_occurrences_v1(text, needle)
    if count != 1:
        raise LedgerError(f"needle occurs {count} times; a mutant needs exactly one")
    return text.replace(needle, replacement, 1)


def cargo_summaries_v1(stdout: str) -> tuple[tuple[str, int, int], ...]:
    """Return every ``test result:`` line as (status, passed, failed)."""

    return tuple(
        (status, int(passed), int(failed))
        for status, passed, failed in _CARGO_SUMMARY_RE.findall(stdout)
    )


@dataclasses.dataclass(frozen=True, slots=True)
class RunResultV1:
    exit_code: int
    stdout: str
    stderr: str
    seconds: float
    timed_out: bool = False


def control_error_v1(killer: KillerV1, result: RunResultV1) -> str | None:
    """Why an unmutated control run does not qualify the killer, or None when it passes."""

    if result.timed_out:
        return "control run timed out"
    if result.exit_code != 0:
        return f"control run exited {result.exit_code}"
    if isinstance(killer, CargoKillerV1):
        summaries = cargo_summaries_v1(result.stdout)
        if not summaries or any(status != "ok" for status, _, _ in summaries):
            return "control run has no green cargo summary"
        if sum(passed for _, passed, _ in summaries) < 1:
            return "control run selected zero cargo tests"
        return None
    # Opus P38 P3: the pytest control needs the same "something actually ran" guard as the
    # cargo path. A node id that selects nothing exits 0, and a killer that never ran cannot
    # qualify a mutant.
    if pytest_passed_v1(result.stdout) < 1:
        return "control run selected zero pytest tests"
    return None


def pytest_passed_v1(stdout: str | bytes) -> int:
    """The passed count of a ``pytest -q`` summary line, or 0 when there is none."""

    text = stdout.decode("utf-8", "replace") if isinstance(stdout, bytes) else stdout
    total = 0
    for line in text.splitlines():
        match = re.search(r"\b(\d+) passed\b", line)
        if match:
            total = max(total, int(match.group(1)))
    return total


def mutant_verdict_v1(killer: KillerV1, result: RunResultV1) -> str:
    """KILLED only when the killer ran and reported failing tests under the mutant."""

    if result.timed_out:
        return VERDICT_TIMEOUT
    if result.exit_code == 0:
        return VERDICT_SURVIVED
    if isinstance(killer, CargoKillerV1):
        failed = any(count > 0 for _, _, count in cargo_summaries_v1(result.stdout))
        return VERDICT_KILLED if failed else VERDICT_UNVIABLE
    return VERDICT_KILLED if result.exit_code == _PYTEST_TESTS_FAILED_EXIT else VERDICT_UNVIABLE


@dataclasses.dataclass(frozen=True, slots=True)
class RowOutcomeV1:
    description: str
    killer: str
    mutant_sha256: str | None
    exit: int | None
    seconds: float
    verdict: str
    mutation: dict[str, str] | None = None

    def to_json(self) -> dict[str, object]:
        return {
            "description": self.description,
            "killer": self.killer,
            "mutation": self.mutation,
            "mutant_sha256": self.mutant_sha256,
            "exit": self.exit,
            "seconds": round(self.seconds, 3),
            "verdict": self.verdict,
        }


def sorted_rows_v1(rows: Sequence[MutationRowV1]) -> tuple[MutationRowV1, ...]:
    return tuple(sorted(rows, key=lambda row: (row.description, row.killed_by)))


def ledger_report_v1(
    *, packet: str, subject_commit: str, outcomes: Sequence[RowOutcomeV1]
) -> dict[str, object]:
    """The deterministic report: sorted rows, counts, no timestamps."""

    ordered = sorted(outcomes, key=lambda outcome: (outcome.description, outcome.killer))
    verdicts = [outcome.verdict for outcome in ordered]
    narrative = verdicts.count(VERDICT_NARRATIVE)
    legacy = verdicts.count(VERDICT_LEGACY)
    killed = verdicts.count(VERDICT_KILLED)
    survived = verdicts.count(VERDICT_SURVIVED)
    errors = sum(1 for verdict in verdicts if verdict in ERROR_VERDICTS)
    return {
        "schema": LEDGER_SCHEMA_V1,
        "packet": packet,
        "subject_commit": subject_commit,
        "rows": [outcome.to_json() for outcome in ordered],
        "mechanical": len(ordered) - narrative - legacy,
        "narrative": narrative,
        "legacy": legacy,
        "killed": killed,
        "survived": survived,
        "errors": errors,
    }


def ledger_exit_code_v1(report: Mapping[str, object]) -> int:
    """0 only when every mechanical row was killed and nothing errored."""

    return 0 if report["survived"] == 0 and report["errors"] == 0 else 1


# ---------------------------------------------------------------------------
# Imperative shell: git archive, copies, subprocesses
# ---------------------------------------------------------------------------

RunnerV1 = Callable[[Sequence[str], Path, Mapping[str, str], int], RunResultV1]
LogV1 = Callable[[str], None]


def _log(message: str) -> None:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%H:%M:%S")
    print(f"[thv1-ledger {stamp}] {message}", file=sys.stderr, flush=True)


def _text(value: object) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return "" if value is None else str(value)


def default_runner_v1(
    argv: Sequence[str], cwd: Path, env: Mapping[str, str], timeout_seconds: int
) -> RunResultV1:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            list(argv),
            cwd=cwd,
            env=dict(env),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        return RunResultV1(-1, _text(exc.stdout), _text(exc.stderr), time.monotonic() - started, True)
    return RunResultV1(
        completed.returncode, completed.stdout, completed.stderr, time.monotonic() - started
    )


def run_environment_v1(base: Mapping[str, str], *, cargo_target_dir: Path) -> dict[str, str]:
    env = dict(base)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.setdefault("LANG", "C.UTF-8")
    env.setdefault("LC_ALL", "C.UTF-8")
    env["CARGO_INCREMENTAL"] = "0"
    env.setdefault("CARGO_TARGET_DIR", str(cargo_target_dir))
    return env


def archive_subject_v1(repo_root: Path, rev: str, tar_path: Path) -> str:
    """Write ``git archive <rev>`` to ``tar_path`` and return the resolved commit."""

    try:
        commit = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--verify", f"{rev}^{{commit}}"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        subprocess.run(
            ["git", "-C", str(repo_root), "archive", "--format=tar", "-o", str(tar_path), commit],
            capture_output=True,
            text=True,
            check=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise LedgerError(f"git archive of {rev} failed: {exc}") from exc
    return commit


def extract_copy_v1(tar_path: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    try:
        subprocess.run(
            ["tar", "-xf", str(tar_path), "-C", str(destination)],
            capture_output=True,
            text=True,
            check=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise LedgerError(f"extracting {tar_path} failed: {exc}") from exc


@dataclasses.dataclass(frozen=True, slots=True)
class LedgerOptionsV1:
    repo_root: Path
    packet: str
    rev: str = "HEAD"
    python: str = sys.executable
    workdir: Path | None = None
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS_V1
    keep: bool = False
    packet_file: Path | None = None
    filters: tuple[str, ...] = ()


def _default_workdir() -> Path:
    return Path(os.environ.get("TMPDIR") or tempfile.gettempdir()) / "thv1-ledger"


def _pin_drift(packet: PacketV1, copy: Path, path: str) -> str | None:
    pin = packet.current_pin_for(path)
    if pin is None:
        return f"{path} is not pinned by the packet"
    absolute = copy / path
    if not absolute.is_file():
        return f"{path} is missing from the subject"
    if sha256_file(absolute) != pin.sha256:
        return f"{path} differs from its pin"
    return None


def _killer_cwd(copy: Path, killer: KillerV1) -> Path:
    return copy / killer.crate_dir if isinstance(killer, CargoKillerV1) else copy


def _killer_argv(python: str, killer: KillerV1) -> tuple[str, ...]:
    if isinstance(killer, CargoKillerV1):
        return cargo_argv_v1(killer)
    return pytest_argv_v1(python, killer)


def _execute_mechanical_row(
    *,
    row: MutationRowV1,
    index: int,
    packet: PacketV1,
    packet_dir: Path,
    tar_path: Path,
    killer: KillerV1,
    options: LedgerOptionsV1,
    env: Mapping[str, str],
    runner: RunnerV1,
    log: LogV1,
) -> RowOutcomeV1:
    mutant = row.mutant
    assert mutant is not None  # mechanical rows carry a mutant by construction
    row_dir = packet_dir / f"row-{index:02d}"
    extract_copy_v1(tar_path, row_dir)
    try:
        for path in (mutant.path, killer.test_path):
            drift = _pin_drift(packet, row_dir, path)
            if drift is not None:
                log(f"row {index}: PIN_DRIFT: {drift}")
                return RowOutcomeV1(row.description, row.killed_by, None, None, 0.0, VERDICT_PIN_DRIFT)
        target = row_dir / mutant.path
        text = target.read_bytes().decode("utf-8")
        try:
            mutated = apply_mutant_v1(text, mutant.needle, mutant.replacement)
        except LedgerError as exc:
            log(f"row {index}: NEEDLE_COUNT: {exc}")
            return RowOutcomeV1(row.description, row.killed_by, None, None, 0.0, VERDICT_NEEDLE_COUNT)
        mutated_bytes = mutated.encode("utf-8")
        target.write_bytes(mutated_bytes)
        mutant_sha256 = hashlib.sha256(mutated_bytes).hexdigest()
        # Opus P38 P2-6: the digest of the mutated FILE cannot tell a reader which mutation
        # ran, so a row could read as KILLED while a different edit did the killing. Record
        # the mutation itself: where it was applied, digests of the exact needle and
        # replacement, and the needle's first line for a human to match against the row.
        mutation = {
            "path": mutant.path,
            "needle_sha256": hashlib.sha256(mutant.needle.encode("utf-8")).hexdigest(),
            "replacement_sha256": hashlib.sha256(mutant.replacement.encode("utf-8")).hexdigest(),
            "needle_first_line": mutant.needle.splitlines()[0][:120] if mutant.needle else "",
        }
        result = runner(_killer_argv(options.python, killer), _killer_cwd(row_dir, killer), env, options.timeout_seconds)
        verdict = mutant_verdict_v1(killer, result)
        log(f"row {index}: {verdict} exit={result.exit_code} seconds={result.seconds:.1f}")
        if verdict != VERDICT_KILLED:
            log(f"row {index}: stdout tail: {result.stdout[-600:]!r}")
            log(f"row {index}: stderr tail: {result.stderr[-600:]!r}")
        return RowOutcomeV1(
            row.description,
            row.killed_by,
            mutant_sha256,
            result.exit_code,
            result.seconds,
            verdict,
            mutation,
        )
    finally:
        if not options.keep:
            shutil.rmtree(row_dir, ignore_errors=True)


def run_ledger_v1(
    options: LedgerOptionsV1,
    *,
    runner: RunnerV1 = default_runner_v1,
    log: LogV1 = _log,
) -> dict[str, object]:
    """Archive the subject, execute every declared row, and return the report."""

    workdir = options.workdir or _default_workdir()
    packet_dir = workdir / options.packet
    if packet_dir.exists():
        shutil.rmtree(packet_dir)
    packet_dir.mkdir(parents=True)
    try:
        tar_path = packet_dir / "archive.tar"
        subject_commit = archive_subject_v1(options.repo_root, options.rev, tar_path)
        log(f"subject {subject_commit} archived to {tar_path}")
        control = packet_dir / "control"
        extract_copy_v1(tar_path, control)
        contract_path = control / CONTRACT_RELATIVE_V1
        if not contract_path.is_file():
            raise LedgerError(f"subject has no {CONTRACT_RELATIVE_V1}")
        contract = load_contract(contract_path)
        packet_path = options.packet_file or control / EVIDENCE_DIR_RELATIVE_V1 / f"{options.packet}.json"
        if not packet_path.is_file():
            raise LedgerError(f"packet not found: {packet_path}")
        packet, rows = load_packet_with_mutations(packet_path, contract)
        if packet.evidence_id != options.packet:
            raise LedgerError(f"packet {packet_path} declares {packet.evidence_id}, not {options.packet}")
        ordered = sorted_rows_v1(rows)
        if options.filters:
            ordered = tuple(row for row in ordered if any(item in row.description for item in options.filters))
            log(f"filters active: {len(ordered)} of {len(rows)} rows selected; the report is partial")
        env = run_environment_v1(os.environ, cargo_target_dir=packet_dir / "cargo-target")

        controls: dict[str, tuple[KillerV1, RunResultV1]] = {}
        for row in ordered:
            if row.kind != "mechanical" or row.killed_by in controls:
                continue
            killer = parse_killer_v1(row.killed_by)
            log(f"control: {row.killed_by}")
            result = runner(_killer_argv(options.python, killer), _killer_cwd(control, killer), env, options.timeout_seconds)
            failure = control_error_v1(killer, result)
            if failure is not None:
                log(f"control: {row.killed_by}: {failure}")
                log(f"control stdout tail: {result.stdout[-600:]!r}")
                log(f"control stderr tail: {result.stderr[-600:]!r}")
            controls[row.killed_by] = (killer, result)

        outcomes: list[RowOutcomeV1] = []
        for index, row in enumerate(ordered, start=1):
            if row.kind == "narrative":
                outcomes.append(RowOutcomeV1(row.description, row.killed_by, None, None, 0.0, VERDICT_NARRATIVE))
                continue
            if row.kind == "legacy":
                outcomes.append(RowOutcomeV1(row.description, row.killed_by, None, None, 0.0, VERDICT_LEGACY))
                continue
            killer, control_result = controls[row.killed_by]
            if control_error_v1(killer, control_result) is not None:
                outcomes.append(
                    RowOutcomeV1(
                        row.description,
                        row.killed_by,
                        None,
                        control_result.exit_code,
                        control_result.seconds,
                        VERDICT_CONTROL_FAILED,
                    )
                )
                continue
            log(f"row {index}: {row.description}")
            outcomes.append(
                _execute_mechanical_row(
                    row=row,
                    index=index,
                    packet=packet,
                    packet_dir=packet_dir,
                    tar_path=tar_path,
                    killer=killer,
                    options=options,
                    env=env,
                    runner=runner,
                    log=log,
                )
            )
        report = ledger_report_v1(packet=packet.evidence_id, subject_commit=subject_commit, outcomes=outcomes)
        log(
            f"done: mechanical={report['mechanical']} narrative={report['narrative']} "
            f"legacy={report['legacy']} killed={report['killed']} survived={report['survived']} "
            f"errors={report['errors']}"
        )
        return report
    finally:
        if not options.keep:
            shutil.rmtree(packet_dir, ignore_errors=True)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--packet", required=True, help="evidence id, e.g. THV1-20260903-example-v1")
    parser.add_argument("--repo", type=Path, default=REPO_ROOT, help="subject repository root")
    parser.add_argument("--rev", default="HEAD", help="commit to archive (default HEAD)")
    parser.add_argument("--python", default=sys.executable, help="interpreter for pytest killers")
    parser.add_argument("--workdir", type=Path, default=None, help="default $TMPDIR/thv1-ledger")
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS_V1)
    parser.add_argument("--keep", action="store_true", help="keep the copies for inspection")
    parser.add_argument(
        "--packet-file",
        type=Path,
        default=None,
        help="authoring aid: read the packet from this path instead of the archived copy",
    )
    parser.add_argument(
        "--filter",
        action="append",
        default=[],
        help="authoring aid: run only rows whose description contains this text (partial report)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    options = LedgerOptionsV1(
        repo_root=cast(Path, args.repo).resolve(),
        packet=cast(str, args.packet),
        rev=cast(str, args.rev),
        python=cast(str, args.python),
        workdir=cast(Path | None, args.workdir),
        timeout_seconds=cast(int, args.timeout_seconds),
        keep=cast(bool, args.keep),
        packet_file=cast(Path | None, args.packet_file),
        filters=tuple(cast(list[str], args.filter)),
    )
    try:
        report = run_ledger_v1(options)
    except (LedgerError, TestHygieneError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return ledger_exit_code_v1(report)


if __name__ == "__main__":
    raise SystemExit(main())
