"""Evidence writer rejects source drift, missing inputs and output ownership races."""

import json
from pathlib import Path

import pytest

from src.tau_composition.runtime import TauQueryError
from tools import benchmark_tau_workbench as bench


def _candidate_file(tmp_path: Path) -> Path:
    path = tmp_path / "candidates.json"
    path.write_text(json.dumps({"candidates": [{"stage": "encoder", "name": "candidate",
        "source": "def transform(x): return x", "intent": "advisory", "negative_control": False}]}))
    return path


def test_output_created_by_another_writer_is_preserved(monkeypatch, tmp_path, capsys) -> None:
    out = tmp_path / "results"
    real = Path.mkdir
    def raced(path, *args, **kwargs):
        real(path, *args, **kwargs)
        (path / "report.json").write_text("other writer")
        raise FileExistsError("output_created_concurrently")
    monkeypatch.setattr(Path, "mkdir", raced)
    assert bench.main(["--tau", "/bin/true", "--candidates", str(tmp_path / "absent"), "--out", str(out)]) != 0
    assert (out / "report.json").read_text() == "other writer"


@pytest.mark.parametrize("mode", ["drift", "unknown"])
def test_incomplete_native_or_drifting_source_cannot_publish_pass(mode, monkeypatch, tmp_path, capsys) -> None:
    path = _candidate_file(tmp_path)
    out = tmp_path / "results"
    hashes = iter(({"source": "before"}, {"source": "after"}))
    monkeypatch.setattr(bench, "_source_hashes", lambda: next(hashes))
    monkeypatch.setattr(bench, "_run", lambda *args: {"baseline": {}})
    if mode == "unknown":
        def unavailable(*args, **kwargs):
            raise TauQueryError("native_timeout")
        monkeypatch.setattr(bench, "TauRuntime", unavailable)
    code = bench.main(["--tau", "/bin/true", "--candidates", str(path), "--out", str(out)])
    result = json.loads((out / "report.json").read_text())
    assert code != 0 and result["authority"] == "NONE"
    assert result["status"] == ("FAIL" if mode == "drift" else "UNKNOWN")
    assert result["error_code"] == ("source_changed_during_replay" if mode == "drift" else "native_timeout")


def test_missing_required_source_is_a_hard_failure(monkeypatch, tmp_path) -> None:
    monkeypatch.setattr(bench, "ROOT", tmp_path)
    monkeypatch.setattr(bench, "_swarm_hashes", lambda: {})
    with pytest.raises(ValueError, match="source_file_missing"):
        bench._source_hashes()


@pytest.mark.parametrize("name", ["tests/test_tau_workbench_benchmark.py",
                                 "docs/research/tau_workbench_plan_20260908.md"])
def test_manifest_binds_its_own_obligations_and_negative_evidence(monkeypatch, name) -> None:
    before = bench._source_hashes()
    real = Path.read_bytes
    def changed(path):
        return b"changed evidence" if path == bench.ROOT / name else real(path)
    monkeypatch.setattr(Path, "read_bytes", changed)
    assert bench._source_hashes() != before


@pytest.mark.parametrize("payload", [b'{"candidates": [ ] }\n', b'{\r\n"candidates": [ ] }\r\n'])
def test_saved_candidate_input_preserves_the_exact_hashed_bytes(tmp_path, payload) -> None:
    bench._write(tmp_path, {"candidates.json": payload})
    assert (tmp_path / "candidates.json").read_bytes() == payload


@pytest.mark.parametrize("mutation", ["duplicate", "extra", "bool", "empty", "oversize"])
def test_untrusted_candidate_metadata_is_closed_and_bounded(mutation, tmp_path) -> None:
    text = _candidate_file(tmp_path).read_text()
    data = json.loads(text)
    if mutation == "duplicate":
        text = text.replace('"name":', '"name": "a", "name":', 1)
    elif mutation == "extra":
        data["authority"] = "ALLOW"
        text = json.dumps(data)
    elif mutation == "bool":
        data["candidates"][0]["negative_control"] = 1
        text = json.dumps(data)
    elif mutation == "empty":
        text = '{"candidates": []}'
    else:
        text = " " * 128_001
    with pytest.raises(ValueError):
        bench._proposals(text)
