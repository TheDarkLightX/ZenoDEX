"""Failure paths of the source-bound research replay, without simulated proof."""

import json
from types import SimpleNamespace

import pytest

from tools import benchmark_tau_swarm as benchmark


def test_required_replay_sources_cannot_be_recorded_as_absent(tmp_path, monkeypatch) -> None:
    monkeypatch.setattr(benchmark, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="source_file_missing"):
        benchmark._source_hashes()


def test_source_drift_saves_only_a_failed_replay_record(tmp_path, monkeypatch) -> None:
    # This checks failure reporting only. No native execution is simulated as
    # passing evidence: there are no cases and the outcome must be FAIL.
    snapshots = iter(({"source.py": "a" * 64}, {"source.py": "b" * 64}))
    monkeypatch.setattr(benchmark, "_source_hashes", lambda: next(snapshots))
    monkeypatch.setattr(benchmark, "_cases", lambda: ())
    runtime = SimpleNamespace(records=[], binary_sha256="c" * 64, check_subject=lambda: None)
    monkeypatch.setattr(benchmark, "TauRuntime", lambda *args, **kwargs: runtime)
    out = tmp_path / "replay"
    args = SimpleNamespace(out=out, tau=tmp_path / "unused", timeout_seconds=1)
    with pytest.raises(benchmark.EvidenceMismatch, match="source_changed_during_replay"):
        benchmark.run(args)
    report = json.loads((out / "report.json").read_text())
    assert report["status"] == "FAIL" and report["authority"] == "NONE"
    assert report["error_code"] == "source_changed_during_replay"
    assert json.loads((out / "native_queries.json").read_text()) == []
