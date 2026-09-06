"""Fail-closed research qualification and full-vector comparison controls."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

from experiments.tau_economic_qualification_v1 import qualify
from experiments.tau_economic_qualification_v1.reference import corpus
from experiments.tau_economic_qualification_v1.runner import TraceObservation, Variant, prepare

ROOT = Path(__file__).resolve().parents[2]


def test_selected_gate_match_cannot_hide_an_incorrect_standalone_output(monkeypatch):
    case = next(case for case in corpus() if case.spec_id == "nonce_replay_guard_v1")
    source = (ROOT / "src/tau_specs/recommended/nonce_replay_guard_v1.tau").read_bytes()
    prepared = prepare(case.spec_id, source, Variant.ORIGINAL)
    wrong = (1 - case.expected_outputs[0], *case.expected_outputs[1:])
    observation = TraceObservation((wrong,), 1, "a" * 64, (), "b" * 64, "c" * 64)
    monkeypatch.setattr(qualify, "run_trace", lambda *_: observation)
    with pytest.raises(ValueError, match="Tau output disagreement"):
        qualify._checked_run(3, prepared, (case,))


def test_wrong_fixed_vector_is_detected_before_engine_execution(monkeypatch):
    case = next(case for case in corpus() if case.spec_id == "nonce_replay_guard_v1")
    source = (ROOT / "src/tau_specs/recommended/nonce_replay_guard_v1.tau").read_bytes()
    prepared = prepare(case.spec_id, source, Variant.ORIGINAL)
    wrong = replace(case, expected_outputs=(1 - case.expected_outputs[0], *case.expected_outputs[1:]))
    def forbidden(*_):
        pytest.fail("engine reached with a contradictory reference vector")
    monkeypatch.setattr(qualify, "run_trace", forbidden)
    with pytest.raises(ValueError, match="independent reference"):
        qualify._checked_run(3, prepared, (wrong,))


def test_failed_rerun_overwrites_old_pass_report(tmp_path, monkeypatch, capsys):
    report = tmp_path / "report.json"
    report.write_text('{"status":"PASS"}')
    monkeypatch.setattr("sys.argv", ["qualify", "--tau-binary", str(tmp_path / "missing"),
                                    "--output", str(report), "--repeats", "2"])
    assert qualify.main() == 1
    assert json.loads(report.read_text())["status"] == "FAIL"
    assert json.loads(capsys.readouterr().out)["status"] == "FAIL"


def test_changed_normalizer_cannot_reach_execution(monkeypatch):
    monkeypatch.setattr(qualify, "source_subject", lambda: {"src/integration/tau_runner.py": "0" * 64})
    with pytest.raises(ValueError, match="normalizer source drift"):
        qualify.run_qualification(Path("/does-not-exist"))


def test_foreign_binary_is_rejected_without_execution(tmp_path):
    foreign = tmp_path / "foreign"
    foreign.write_bytes(b"Never execute this payload")
    with pytest.raises(ValueError, match="differs from the measured"):
        qualify.run_qualification(foreign)


def test_output_write_failure_returns_failure_even_after_success(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(qualify, "run_qualification", lambda *a, **k: {"status": "PASS", "authority": "NONE"})
    monkeypatch.setattr("sys.argv", ["qualify", "--tau-binary", "/unused", "--output", str(tmp_path)])
    assert qualify.main() == 1
    assert json.loads(capsys.readouterr().out)["status"] == "FAIL"


def test_final_report_failure_leaves_incomplete_marker_instead_of_old_pass(tmp_path, monkeypatch, capsys):
    report = tmp_path / "report.json"
    report.write_text('{"status":"PASS"}')
    real_writer = qualify.atomic_report
    def fail_final(path, payload):
        if payload["status"] == "INCOMPLETE":
            real_writer(path, payload)
        else:
            raise OSError("injected final write failure")
    monkeypatch.setattr(qualify, "atomic_report", fail_final)
    monkeypatch.setattr(qualify, "run_qualification", lambda *a, **k: {"status": "PASS", "authority": "NONE"})
    monkeypatch.setattr("sys.argv", ["qualify", "--tau-binary", "/unused", "--output", str(report)])
    assert qualify.main() == 1
    assert json.loads(report.read_text()) == {"status": "INCOMPLETE", "authority": "NONE"}
    assert json.loads(capsys.readouterr().out)["output_state"] == "INCOMPLETE"


def test_failed_initial_invalidation_never_executes_or_claims_old_report_removed(tmp_path, monkeypatch, capsys):
    report = tmp_path / "report.json"
    report.write_text('{"status":"PASS"}')
    def failed_writer(*_):
        raise PermissionError("injected initial invalidation failure")
    def forbidden(*a, **k):
        pytest.fail("qualification started before report invalidation")
    monkeypatch.setattr(qualify, "atomic_report", failed_writer)
    monkeypatch.setattr(qualify, "run_qualification", forbidden)
    monkeypatch.setattr("sys.argv", ["qualify", "--tau-binary", "/unused", "--output", str(report)])
    assert qualify.main() == 1
    output = json.loads(capsys.readouterr().out)
    assert output["status"] == "FAIL"
    assert output["stale_output_possible"] is True
    assert output["output_state"] == "UNVERIFIED_PREEXISTING"
    assert json.loads(report.read_text())["status"] == "PASS"
