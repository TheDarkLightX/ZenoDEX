"""Regressions for the THV1 mutation ledger and the mechanical mutation-row schema.

The ledger executes every declared mutation row of a test-hygiene packet against a
fresh ``git archive`` copy; these tests pin that a needle must occur exactly once, that
a killer which still passes marks the row SURVIVED and the ledger exit 1, that
narrative rows are listed but never counted, that a Rust row runs through cargo, that
the JSON report shape is stable and sorted, and that the packet loader refuses every
row shape other than mechanical, narrative, or (pre-cutover) legacy.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Sequence, cast

import pytest

from tools import thv1_mutation_ledger_v1 as ledger
from tools.check_test_hygiene_v1 import ChangedPathV1, check_repository
from tools.test_hygiene_evidence_v1 import (
    MECHANICAL_MUTATION_ROWS_FROM,
    MUTATION_ROW_KINDS,
    load_packet_with_mutations,
    load_packets,
    load_packets_with_mutations,
    needle_occurrences_v1,
)
from tools.test_hygiene_model_v1 import (
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    TestHygieneError,
    load_contract,
)

_REAL_CONTRACT = load_contract(DEFAULT_CONTRACT)
_MOD_SOURCE = "def guard(value: int) -> bool:\n    if value < 0:\n        return False\n    return True\n"
_MOD_TEST = (
    "from pkg.mod import guard\n\n\n"
    "def test_negative_is_refused() -> None:\n    assert guard(-1) is False\n\n\n"
    "def test_positive_is_admitted() -> None:\n    assert guard(1) is True\n"
)
_GUARD_NEEDLE = "    if value < 0:\n        return False\n"
_NEGATIVE_NODE = "tests/test_mod.py::test_negative_is_refused"
_POSITIVE_NODE = "tests/test_mod.py::test_positive_is_admitted"
_PACKET_ID = "THV1-20260903-ledger-subject-v1"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        [
            "git",
            "-c",
            "user.name=ledger",
            "-c",
            "user.email=ledger@example.invalid",
            "-c",
            "commit.gpgsign=false",
            *args,
        ],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _killed_row() -> dict[str, object]:
    return {
        "description": "drop the negative guard",
        "killed_by": _NEGATIVE_NODE,
        "mutant": {
            "path": "pkg/mod.py",
            "needle_lines": _GUARD_NEEDLE.split("\n"),
            "replacement_lines": [""],
        },
    }


def _surviving_row() -> dict[str, object]:
    return {
        "description": "spell the admission differently",
        "killed_by": _POSITIVE_NODE,
        "mutant": {
            "path": "pkg/mod.py",
            "needle_lines": ["    return True", ""],
            "replacement_lines": ["    return bool(1)", ""],
        },
    }


def _narrative_row() -> dict[str, object]:
    return {
        "description": "an argument no test executes",
        "killed_by": _POSITIVE_NODE,
        "narrative": True,
    }


def _packet(
    repo: Path,
    *,
    evidence_id: str = _PACKET_ID,
    rows: Sequence[dict[str, object]] = (),
    source_paths: Sequence[str] = ("pkg/mod.py",),
) -> dict[str, object]:
    test_path = "tests/test_mod.py"
    return {
        "schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_id": evidence_id,
        "created_date": "2026-09-03",
        "claim_scope": "Synthetic subject for the mutation ledger regressions.",
        "change_kind": "assurance_infrastructure",
        "risk_class": "assurance",
        "invariant_ids": ["LEDGER-DECLARED-KILLER-MUST-KILL"],
        "failure_modes": ["a declared killer does not kill"],
        "source_pins": [{"path": path, "sha256": _sha256(repo / path)} for path in source_paths],
        "removed_paths": [],
        "test_pins": [
            {
                "path": test_path,
                "sha256": _sha256(repo / test_path),
                "node_ids": [_NEGATIVE_NODE, _POSITIVE_NODE],
            }
        ],
        "evidence_families": ["negative_regression", "boundary", "mutation"],
        "aaa": {"status": "applied", "reason": "one arrangement, one call, exact assertions"},
        "reject_is_noop": {"status": "not_applicable", "reason": "pure functions only"},
        "boundary_dimensions": [{"name": "sign", "points": ["negative", "positive"]}],
        "mutations": list(rows),
        "nonclaims": ["This synthetic packet grants nothing."],
    }


def _subject(tmp_path: Path) -> Path:
    """A committed git repository with one guarded function and two tests."""

    repo = tmp_path / "subject"
    _write(repo / "pkg/__init__.py", "")
    _write(repo / "pkg/mod.py", _MOD_SOURCE)
    _write(repo / "tests/__init__.py", "")
    _write(repo / "tests/test_mod.py", _MOD_TEST)
    (repo / "tools").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(DEFAULT_CONTRACT, repo / "tools/test_hygiene_contract_v1.json")
    return repo


def _commit_packet(repo: Path, packet: dict[str, object]) -> None:
    evidence_id = str(packet["evidence_id"])
    _write(
        repo / f"tests/evidence/test_hygiene/{evidence_id}.json",
        json.dumps(packet, indent=2) + "\n",
    )
    if not (repo / ".git").exists():
        _git(repo, "init", "-q")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "subject")


def _options(repo: Path, tmp_path: Path, **overrides: Any) -> ledger.LedgerOptionsV1:
    values: dict[str, Any] = {
        "repo_root": repo,
        "packet": _PACKET_ID,
        "python": sys.executable,
        "workdir": tmp_path / "work",
    }
    values.update(overrides)
    return ledger.LedgerOptionsV1(**values)


def _quiet(_: str) -> None:
    return None


def _rows(report: dict[str, object]) -> list[dict[str, Any]]:
    return cast(list[dict[str, Any]], report["rows"])


# A green pytest control run prints a passed summary; the ledger requires one, so the stub
# speaks the same shape (the cargo path has always had the equivalent guard).
_CONTROL_STDOUT_V1 = "1 passed in 0.01s\n"


def _stub_runner(
    *, control_exit: int, mutant_exit: int, stdout: str = ""
) -> tuple[ledger.RunnerV1, list[tuple[tuple[str, ...], Path]]]:
    calls: list[tuple[tuple[str, ...], Path]] = []

    def runner(argv: Sequence[str], cwd: Path, env: Any, timeout: int) -> ledger.RunResultV1:
        calls.append((tuple(argv), Path(cwd)))
        in_control = "control" in Path(cwd).parts
        if in_control:
            text = stdout if "passed" in stdout else stdout + _CONTROL_STDOUT_V1
            return ledger.RunResultV1(control_exit, text, "", 0.01)
        return ledger.RunResultV1(mutant_exit, stdout, "", 0.01)

    return runner, calls


# ---------------------------------------------------------------------------
# Pure core
# ---------------------------------------------------------------------------


def test_needle_must_occur_exactly_once() -> None:
    assert ledger.apply_mutant_v1("abc", "b", "x") == "axc"
    with pytest.raises(ledger.LedgerError, match="occurs 2 times"):
        ledger.apply_mutant_v1("a b a", "a", "x")
    with pytest.raises(ledger.LedgerError, match="occurs 0 times"):
        ledger.apply_mutant_v1("abc", "zz", "x")
    # Overlapping occurrences count as two start positions, so the edit site is ambiguous.
    with pytest.raises(ledger.LedgerError, match="occurs 2 times"):
        ledger.apply_mutant_v1("aaa", "aa", "x")
    assert needle_occurrences_v1("aaa", "aa") == 2
    assert needle_occurrences_v1("abc", "") == 0


def test_killer_forms_are_classified_and_malformed_ones_refused() -> None:
    node = ledger.parse_killer_v1("tests/core/test_x.py::test_y[param]")
    assert isinstance(node, ledger.PytestKillerV1)
    assert node.test_path == "tests/core/test_x.py"
    assert ledger.pytest_argv_v1("py", node) == (
        "py", "-m", "pytest", "-q", "-x", "-p", "no:cacheprovider", "tests/core/test_x.py::test_y[param]",
    )
    cargo = ledger.parse_killer_v1("zk/probe/tests/probe.rs::probe_")
    assert isinstance(cargo, ledger.CargoKillerV1)
    assert (cargo.crate_dir, cargo.target, cargo.filter) == ("zk/probe", "probe", "probe_")
    assert cargo.test_path == "zk/probe/tests/probe.rs"
    assert ledger.cargo_argv_v1(cargo) == (
        "cargo", "test", "--offline", "--locked", "--test", "probe", "probe_",
    )
    # opus2 P40 P2-2: a guard whose only honest test is a crate unit test needs a killer form
    # of its own, or it can carry no mechanical row at all.
    lib = ledger.parse_killer_v1("zk/probe/src/lib.rs::lib::tests::probe_")
    assert isinstance(lib, ledger.CargoKillerV1) and lib.lib is True
    assert (lib.crate_dir, lib.filter) == ("zk/probe", "lib::tests::probe_")
    assert ledger.cargo_argv_v1(lib) == (
        "cargo", "test", "--offline", "--locked", "--lib", "--", "lib::tests::probe_",
    )
    # Opus P41 P2-4: a --lib filter runs across the whole crate, so without this the declared
    # path is decorative and the pin check guards a file the test need not live in.
    with pytest.raises(ledger.LedgerError, match="must start with the declared module"):
        ledger.parse_killer_v1("zk/probe/src/state.rs::lib::tests::probe_")
    for malformed in ("tests/test_x.py", "tests/test_x.py::", "tests/test x.py::t", "notes.txt::t", "src/lib.rs::t"):
        with pytest.raises(ledger.LedgerError):
            ledger.parse_killer_v1(malformed)


def test_pytest_verdicts_require_a_failing_test_run() -> None:
    killer = ledger.PytestKillerV1(_NEGATIVE_NODE)
    run = ledger.RunResultV1
    assert ledger.mutant_verdict_v1(killer, run(0, "", "", 1.0)) == ledger.VERDICT_SURVIVED
    assert ledger.mutant_verdict_v1(killer, run(1, "", "", 1.0)) == ledger.VERDICT_KILLED
    # A collection error or usage error is not a kill: the killer never ran.
    assert ledger.mutant_verdict_v1(killer, run(2, "", "", 1.0)) == ledger.VERDICT_UNVIABLE
    assert ledger.mutant_verdict_v1(killer, run(4, "", "", 1.0)) == ledger.VERDICT_UNVIABLE
    assert ledger.mutant_verdict_v1(killer, run(-1, "", "", 1.0, timed_out=True)) == ledger.VERDICT_TIMEOUT
    # A pytest control must have run at least one test (Opus P38 P3), the guard the cargo
    # path already had: a node id that selects nothing exits 0 and proves nothing.
    assert ledger.control_error_v1(killer, run(0, "3 passed in 0.1s", "", 1.0)) is None
    assert (
        ledger.control_error_v1(killer, run(0, "", "", 1.0)) == "control run selected zero pytest tests"
    )
    assert ledger.control_error_v1(killer, run(1, "", "", 1.0)) == "control run exited 1"
    assert ledger.control_error_v1(killer, run(-1, "", "", 1.0, timed_out=True)) == "control run timed out"


def test_cargo_verdicts_read_the_test_summary() -> None:
    killer = ledger.CargoKillerV1("zk/probe/tests/probe.rs", "probe_")
    run = ledger.RunResultV1
    failed = "running 1 test\ntest probe_one ... FAILED\n\ntest result: FAILED. 0 passed; 1 failed; 0 ignored\n"
    green = "running 1 test\ntest probe_one ... ok\n\ntest result: ok. 1 passed; 0 failed; 0 ignored\n"
    empty = "running 0 tests\n\ntest result: ok. 0 passed; 0 failed; 0 ignored\n"
    assert ledger.mutant_verdict_v1(killer, run(101, failed, "", 1.0)) == ledger.VERDICT_KILLED
    assert ledger.mutant_verdict_v1(killer, run(101, "", "error[E0308]: mismatched types", 1.0)) == ledger.VERDICT_UNVIABLE
    assert ledger.mutant_verdict_v1(killer, run(0, green, "", 1.0)) == ledger.VERDICT_SURVIVED
    assert ledger.control_error_v1(killer, run(0, green, "", 1.0)) is None
    assert ledger.control_error_v1(killer, run(0, empty, "", 1.0)) == "control run selected zero cargo tests"
    assert ledger.control_error_v1(killer, run(0, "", "", 1.0)) == "control run has no green cargo summary"
    assert ledger.cargo_summaries_v1(failed + green) == (("FAILED", 0, 1), ("ok", 1, 0))


def test_report_shape_is_stable_sorted_and_counts_only_mechanical_rows() -> None:
    outcome = ledger.RowOutcomeV1
    outcomes = [
        outcome("zeta", "t::b", "ab" * 32, 1, 2.5, ledger.VERDICT_KILLED),
        outcome("alpha", "t::b", "cd" * 32, 0, 1.25, ledger.VERDICT_SURVIVED),
        outcome("alpha", "t::a", None, None, 0.0, ledger.VERDICT_NARRATIVE),
        outcome("mid", "t::c", None, None, 0.0, ledger.VERDICT_LEGACY),
        outcome("mid", "t::b", None, None, 0.0, ledger.VERDICT_PIN_DRIFT),
    ]
    report = ledger.ledger_report_v1(packet="THV1-20260903-x-v1", subject_commit="0" * 40, outcomes=outcomes)
    assert tuple(report) == ledger.REPORT_KEYS_V1
    rows = report["rows"]
    assert isinstance(rows, list)
    assert [(row["description"], row["killer"]) for row in rows] == [
        ("alpha", "t::a"), ("alpha", "t::b"), ("mid", "t::b"), ("mid", "t::c"), ("zeta", "t::b"),
    ]
    assert all(tuple(row) == ledger.ROW_KEYS_V1 for row in rows)
    assert (report["mechanical"], report["narrative"], report["legacy"]) == (3, 1, 1)
    assert (report["killed"], report["survived"], report["errors"]) == (1, 1, 1)
    assert ledger.ledger_exit_code_v1(report) == 1
    assert json.loads(json.dumps(report, sort_keys=True)) == report
    green = ledger.ledger_report_v1(packet="p", subject_commit="0" * 40, outcomes=outcomes[:1])
    assert ledger.ledger_exit_code_v1(green) == 0
    # Each disjunct of the exit rule is load-bearing on its own: a report carrying a
    # survivor and no error, and one carrying an error and no survivor, both exit 1.
    # Asserting only the mixed report above would admit an exit rule that reads one
    # counter and ignores the other.
    survivor_only = ledger.ledger_report_v1(
        packet="p", subject_commit="0" * 40, outcomes=[outcomes[0], outcomes[1]]
    )
    assert (survivor_only["survived"], survivor_only["errors"]) == (1, 0)
    assert ledger.ledger_exit_code_v1(survivor_only) == 1
    error_only = ledger.ledger_report_v1(
        packet="p", subject_commit="0" * 40, outcomes=[outcomes[0], outcomes[4]]
    )
    assert (error_only["survived"], error_only["errors"]) == (0, 1)
    assert ledger.ledger_exit_code_v1(error_only) == 1


def test_narrative_rows_are_not_counted() -> None:
    narrative = ledger.RowOutcomeV1("why", "t::a", None, None, 0.0, ledger.VERDICT_NARRATIVE)
    report = ledger.ledger_report_v1(packet="p", subject_commit="0" * 40, outcomes=[narrative])
    assert (report["mechanical"], report["narrative"], report["killed"], report["survived"]) == (0, 1, 0, 0)
    assert ledger.ledger_exit_code_v1(report) == 0


# ---------------------------------------------------------------------------
# Shell: a real git subject, real pytest killers
# ---------------------------------------------------------------------------


def test_ledger_kills_survives_and_leaves_the_worktree_alone(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    _commit_packet(repo, _packet(repo, rows=[_surviving_row(), _narrative_row(), _killed_row()]))
    source_before = _sha256(repo / "pkg/mod.py")

    report = ledger.run_ledger_v1(_options(repo, tmp_path), log=_quiet)

    verdicts = {row["description"]: row for row in _rows(report)}
    assert verdicts["drop the negative guard"]["verdict"] == ledger.VERDICT_KILLED
    assert verdicts["drop the negative guard"]["exit"] == 1
    assert verdicts["spell the admission differently"]["verdict"] == ledger.VERDICT_SURVIVED
    assert verdicts["an argument no test executes"] == {
        "description": "an argument no test executes",
        "killer": _POSITIVE_NODE,
        "mutation": None,
        "mutant_sha256": None,
        "exit": None,
        "seconds": 0.0,
        "verdict": ledger.VERDICT_NARRATIVE,
    }
    expected_mutant = hashlib.sha256(_MOD_SOURCE.replace(_GUARD_NEEDLE, "", 1).encode()).hexdigest()
    assert verdicts["drop the negative guard"]["mutant_sha256"] == expected_mutant
    # Opus P38 P2-6: the report must say which mutation ran, not only that the file changed,
    # so a verdict can be tied to the row that claims it.
    mutation = verdicts["drop the negative guard"]["mutation"]
    assert mutation == {
        "path": "pkg/mod.py",
        "needle_sha256": hashlib.sha256(_GUARD_NEEDLE.encode()).hexdigest(),
        "replacement_sha256": hashlib.sha256(b"").hexdigest(),
        "needle_first_line": _GUARD_NEEDLE.splitlines()[0][:120],
    }
    assert mutation["needle_sha256"] != mutation["replacement_sha256"]
    assert (report["mechanical"], report["narrative"], report["killed"], report["survived"], report["errors"]) == (2, 1, 1, 1, 0)
    assert report["subject_commit"] == _git(repo, "rev-parse", "HEAD")
    assert ledger.ledger_exit_code_v1(report) == 1
    assert _sha256(repo / "pkg/mod.py") == source_before
    assert not (tmp_path / "work" / _PACKET_ID).exists()


def test_cli_prints_one_json_document_and_exits_one_on_a_survivor(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    repo = _subject(tmp_path)
    _commit_packet(repo, _packet(repo, rows=[_killed_row(), _surviving_row()]))

    code = ledger.main(["--packet", _PACKET_ID, "--repo", str(repo), "--workdir", str(tmp_path / "work")])

    captured = capsys.readouterr()
    report = json.loads(captured.out)
    assert code == 1
    # The CLI serialises with sorted keys; the key set is the stable contract.
    assert set(report) == set(ledger.REPORT_KEYS_V1)
    assert all(set(row) == set(ledger.ROW_KEYS_V1) for row in report["rows"])
    assert report["packet"] == _PACKET_ID and report["survived"] == 1 and report["killed"] == 1
    assert "[thv1-ledger" in captured.err and "[thv1-ledger" not in captured.out


def test_surviving_killer_fails_the_row_and_the_exit_code(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    _commit_packet(repo, _packet(repo, rows=[_killed_row()]))
    runner, calls = _stub_runner(control_exit=0, mutant_exit=0)

    report = ledger.run_ledger_v1(_options(repo, tmp_path), runner=runner, log=_quiet)

    assert [row["verdict"] for row in _rows(report)] == [ledger.VERDICT_SURVIVED]
    assert ledger.ledger_exit_code_v1(report) == 1
    assert len(calls) == 2 and calls[0][0][-1] == _NEGATIVE_NODE
    assert "control" in calls[0][1].parts and calls[1][1].name == "row-01"


def test_control_failure_pin_drift_and_needle_count_are_errors(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    drifted = _packet(repo, rows=[_killed_row()])
    drifted["test_pins"][0]["sha256"] = "0" * 64  # type: ignore[index]
    doubled: dict[str, object] = {
        "description": "needle that occurs twice",
        "killed_by": _NEGATIVE_NODE,
        "mutant": {"path": "pkg/mod.py", "needle_lines": ["return"], "replacement_lines": ["yield"]},
    }
    _commit_packet(repo, _packet(repo, rows=[doubled]))
    _write(repo / f"tests/evidence/test_hygiene/{_PACKET_ID}-drifted.json", json.dumps(drifted) + "\n")

    failing_control, _ = _stub_runner(control_exit=1, mutant_exit=1)
    report = ledger.run_ledger_v1(_options(repo, tmp_path), runner=failing_control, log=_quiet)
    assert [row["verdict"] for row in _rows(report)] == [ledger.VERDICT_CONTROL_FAILED]
    assert report["errors"] == 1 and ledger.ledger_exit_code_v1(report) == 1

    passing_control, _ = _stub_runner(control_exit=0, mutant_exit=1)
    report = ledger.run_ledger_v1(_options(repo, tmp_path), runner=passing_control, log=_quiet)
    assert [row["verdict"] for row in _rows(report)] == [ledger.VERDICT_NEEDLE_COUNT]
    assert ledger.ledger_exit_code_v1(report) == 1

    drifted_path = repo / f"tests/evidence/test_hygiene/{_PACKET_ID}.json"
    drifted["evidence_id"] = _PACKET_ID
    _write(tmp_path / f"{_PACKET_ID}.json", json.dumps(drifted) + "\n")
    report = ledger.run_ledger_v1(
        _options(repo, tmp_path, packet_file=tmp_path / f"{_PACKET_ID}.json"), runner=passing_control, log=_quiet
    )
    assert [row["verdict"] for row in _rows(report)] == [ledger.VERDICT_PIN_DRIFT]
    assert drifted_path.is_file()


@pytest.mark.skipif(shutil.which("cargo") is None, reason="cargo is not installed")
def test_rust_row_runs_through_cargo(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo = _subject(tmp_path)
    _write(repo / "zk/probe/Cargo.toml", '[package]\nname = "probe"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\n')
    _write(
        repo / "zk/probe/Cargo.lock",
        "# This file is automatically @generated by Cargo.\n# It is not intended for manual editing.\n"
        'version = 4\n\n[[package]]\nname = "probe"\nversion = "0.1.0"\n',
    )
    _write(repo / "zk/probe/src/lib.rs", "pub fn probe() -> u32 {\n    1\n}\n")
    _write(repo / "zk/probe/tests/probe.rs", "#[test]\nfn probe_returns_one() {\n    assert_eq!(probe::probe(), 1);\n}\n")
    row: dict[str, object] = {
        "description": "return two from the probe",
        "killed_by": "zk/probe/tests/probe.rs::probe_returns_one",
        "mutant": {
            "path": "zk/probe/src/lib.rs",
            "needle_lines": ["    1", "}"],
            "replacement_lines": ["    2", "}"],
        },
    }
    packet = _packet(repo, rows=[row], source_paths=("pkg/mod.py", "zk/probe/src/lib.rs", "zk/probe/tests/probe.rs"))
    _commit_packet(repo, packet)
    monkeypatch.setenv("CARGO_TARGET_DIR", str(tmp_path / "cargo-target"))

    report = ledger.run_ledger_v1(_options(repo, tmp_path, timeout_seconds=600), log=_quiet)

    (outcome,) = _rows(report)
    assert outcome["verdict"] == ledger.VERDICT_KILLED and outcome["exit"] == 101
    assert report["killed"] == 1 and ledger.ledger_exit_code_v1(report) == 0


# ---------------------------------------------------------------------------
# Schema: exactly three row shapes
# ---------------------------------------------------------------------------


def _load(tmp_path: Path, packet: dict[str, object]) -> Any:
    path = tmp_path / f"{packet['evidence_id']}.json"
    _write(path, json.dumps(packet) + "\n")
    return load_packet_with_mutations(path, _REAL_CONTRACT)


def test_mechanical_row_requires_a_pinned_source_path_and_a_closed_mutant(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    row = _killed_row()
    _, rows = _load(tmp_path, _packet(repo, rows=[row]))
    assert [(item.kind, item.mutant.path if item.mutant else None) for item in rows] == [("mechanical", "pkg/mod.py")]

    unpinned = _killed_row()
    unpinned["mutant"]["path"] = "pkg/other.py"  # type: ignore[index]
    with pytest.raises(TestHygieneError, match="mutant path is not a pinned source path"):
        _load(tmp_path, _packet(repo, rows=[unpinned]))

    for field, value, message in (
        ("needle_lines", [""], "expected a non-empty needle"),
        ("needle_lines", [], "expected at least one line"),
        ("needle_lines", 7, "expected a list of lines"),
        ("needle_lines", ["ok", 7], "expected string"),
        # A literal control character is what the line format exists to keep out of a
        # packet: the O-008 checker admits printable ASCII only.
        ("needle_lines", ["    if value < 0:\n        return False\n"], "printable ASCII"),
        ("needle_lines", ["\ttab"], "printable ASCII"),
        ("replacement_lines", None, "expected a list of lines"),
        ("replacement_lines", _GUARD_NEEDLE.split("\n"), "replacement must differ from needle"),
        ("extra", "x", "unknown fields"),
    ):
        broken = _killed_row()
        broken["mutant"][field] = value  # type: ignore[index]
        with pytest.raises(TestHygieneError, match=message):
            _load(tmp_path, _packet(repo, rows=[broken]))


def test_row_shape_is_mechanical_or_narrative_and_nothing_else(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    _, rows = _load(tmp_path, _packet(repo, rows=[_narrative_row()]))
    assert rows[0].kind == "narrative" and rows[0].mutant is None

    both = _killed_row()
    both["narrative"] = True
    with pytest.raises(TestHygieneError, match="exactly one of mutant or narrative"):
        _load(tmp_path, _packet(repo, rows=[both]))
    for value in (False, 1, "true"):
        soft = _narrative_row()
        soft["narrative"] = value
        with pytest.raises(TestHygieneError, match="narrative: must be true"):
            _load(tmp_path, _packet(repo, rows=[soft]))
    with pytest.raises(TestHygieneError, match="exactly one of mutant or narrative"):
        _load(tmp_path, _packet(repo, rows=[{"description": "x", "killed_by": _POSITIVE_NODE, "narrative": True, "extra": 1}]))


def test_string_only_rows_are_refused_from_the_cutover(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    legacy: dict[str, object] = {"description": "a string claim", "killed_by": _POSITIVE_NODE}
    assert MECHANICAL_MUTATION_ROWS_FROM == "20260903"
    with pytest.raises(TestHygieneError, match="string-only mutation rows are refused from 20260903"):
        _load(tmp_path, _packet(repo, evidence_id="THV1-20260903-example-v1", rows=[legacy]))
    _, rows = _load(tmp_path, _packet(repo, evidence_id="THV1-20260902-example-v1", rows=[legacy]))
    assert [row.kind for row in rows] == ["legacy"]


def test_cargo_killer_requires_a_pinned_rust_test_path(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    _write(repo / "zk/probe/src/lib.rs", "pub fn probe() -> u32 { 1 }\n")
    _write(repo / "zk/probe/tests/probe.rs", "#[test]\nfn probe_one() {}\n")
    rust_row: dict[str, object] = {
        "description": "a rust mutant",
        "killed_by": "zk/probe/tests/probe.rs::probe_one",
        "mutant": {"path": "zk/probe/src/lib.rs", "needle_lines": ["1"], "replacement_lines": ["2"]},
    }
    pinned = ("pkg/mod.py", "zk/probe/src/lib.rs", "zk/probe/tests/probe.rs")
    _, rows = _load(tmp_path, _packet(repo, rows=[rust_row], source_paths=pinned))
    assert rows[0].kind == "mechanical"
    with pytest.raises(TestHygieneError, match="mutation killer is not a pinned node"):
        _load(tmp_path, _packet(repo, rows=[rust_row], source_paths=("pkg/mod.py", "zk/probe/src/lib.rs")))
    spaced: dict[str, object] = {**rust_row, "killed_by": "zk/probe/tests/probe.rs::probe one"}
    with pytest.raises(TestHygieneError, match="mutation killer is not a pinned node"):
        _load(tmp_path, _packet(repo, rows=[spaced], source_paths=pinned))
    # The crate unit-test form: accepted when its crate source is pinned, refused when not.
    lib_row: dict[str, object] = {
        "description": "a rust guard whose only test is a crate unit test",
        "killed_by": "zk/probe/src/lib.rs::lib::tests::probe_one",
        "mutant": {"path": "zk/probe/src/lib.rs", "needle_lines": ["1"], "replacement_lines": ["2"]},
    }
    _, lib_rows = _load(tmp_path, _packet(repo, rows=[lib_row], source_paths=pinned))
    assert lib_rows[0].kind == "mechanical"
    unpinned_lib: dict[str, object] = {**lib_row, "killed_by": "zk/other/src/lib.rs::lib::tests::probe_one"}
    with pytest.raises(TestHygieneError, match="mutation killer is not a pinned node"):
        _load(tmp_path, _packet(repo, rows=[unpinned_lib], source_paths=pinned))
    # opus2 P42 P2-4: the module-segment rule the ledger enforces must also be enforced here,
    # or the two readers of a row disagree about which rows are well formed.
    foreign_module: dict[str, object] = {**lib_row, "killed_by": "zk/probe/src/lib.rs::other::tests::probe_one"}
    with pytest.raises(TestHygieneError, match="must start with lib::"):
        _load(tmp_path, _packet(repo, rows=[foreign_module], source_paths=pinned))
    legacy_cargo: dict[str, object] = {"description": "old", "killed_by": "zk/probe/tests/probe.rs::probe_one"}
    with pytest.raises(TestHygieneError, match="mutation killer is not a pinned node"):
        _load(tmp_path, _packet(repo, evidence_id="THV1-20260901-example-v1", rows=[legacy_cargo], source_paths=pinned))


def test_load_packets_keeps_its_public_shape(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    evidence_dir = repo / "tests/evidence/test_hygiene"
    _write(evidence_dir / f"{_PACKET_ID}.json", json.dumps(_packet(repo, rows=[_killed_row(), _narrative_row()])) + "\n")
    packets = load_packets(evidence_dir, _REAL_CONTRACT)
    loaded = load_packets_with_mutations(evidence_dir, _REAL_CONTRACT)
    assert [packet.evidence_id for packet in packets] == [_PACKET_ID]
    assert [(packet.evidence_id, [row.kind for row in rows]) for packet, rows in loaded] == [
        (_PACKET_ID, ["mechanical", "narrative"])
    ]


# ---------------------------------------------------------------------------
# Checker: counts, needle liveness on current pins, added-packet rule
# ---------------------------------------------------------------------------


def _check(repo: Path, changed: Sequence[ChangedPathV1] = ()) -> dict[str, object]:
    return check_repository(
        repo_root=repo,
        contract_path=repo / "tools/test_hygiene_contract_v1.json",
        evidence_dir=repo / "tests/evidence/test_hygiene",
        changed_paths=changed,
    )


def test_checker_counts_rows_and_checks_needles_on_current_pins(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    packet_path = repo / f"tests/evidence/test_hygiene/{_PACKET_ID}.json"
    _write(packet_path, json.dumps(_packet(repo, rows=[_killed_row(), _narrative_row()])) + "\n")
    assert _check(repo)["mutation_rows"] == {"mechanical": 1, "narrative": 1, "legacy": 0, "mechanical_current": 1}

    doubled = _killed_row()
    doubled["mutant"]["needle_lines"] = ["return"]  # type: ignore[index]
    _write(packet_path, json.dumps(_packet(repo, rows=[doubled])) + "\n")
    with pytest.raises(TestHygieneError, match="mutant needle occurs 2 times in pkg/mod.py"):
        _check(repo)

    # Once the pinned source drifts the row is a historical record: counted, not needle-checked.
    _write(repo / "pkg/mod.py", _MOD_SOURCE + "\n# drift\n")
    assert _check(repo)["mutation_rows"] == {"mechanical": 1, "narrative": 0, "legacy": 0, "mechanical_current": 0}


def test_added_packet_with_string_only_rows_is_refused_in_diff_mode(tmp_path: Path) -> None:
    repo = _subject(tmp_path)
    legacy: dict[str, object] = {"description": "a string claim", "killed_by": _POSITIVE_NODE}
    name = "THV1-20260805-backdated-v1"
    relative = f"tests/evidence/test_hygiene/{name}.json"
    _write(repo / relative, json.dumps(_packet(repo, evidence_id=name, rows=[legacy])) + "\n")
    assert _check(repo)["mutation_rows"]["legacy"] == 1  # type: ignore[index]
    with pytest.raises(TestHygieneError, match="declares string-only mutation rows"):
        _check(repo, [ChangedPathV1(status="A", path=relative)])


def test_repository_evidence_loads_with_row_kinds() -> None:
    loaded = load_packets_with_mutations(DEFAULT_EVIDENCE_DIR, _REAL_CONTRACT)
    kinds = {row.kind for _, rows in loaded for row in rows}
    assert kinds <= set(MUTATION_ROW_KINDS)
    # The loader's fence is one-directional: a packet dated on or after the cutover may not
    # carry a string-only row, and a packet dated before it MAY. A pre-cutover lineage that
    # declares a mechanical row is an improvement, not a violation, so the older half is not
    # required to be uniformly legacy.
    for packet, rows in loaded:
        if packet.evidence_id[5:13] >= MECHANICAL_MUTATION_ROWS_FROM:
            assert all(row.kind != "legacy" for row in rows), packet.evidence_id
    older_mechanical = {
        packet.evidence_id
        for packet, rows in loaded
        if packet.evidence_id[5:13] < MECHANICAL_MUTATION_ROWS_FROM
        and any(row.kind == "mechanical" for row in rows)
    }
    assert older_mechanical, "a pre-cutover lineage should be able to declare a mechanical row"
    assert "mechanical" in kinds and "legacy" in kinds
