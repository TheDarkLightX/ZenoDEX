"""Structured CLI evidence for the bounded Tau workbench command."""

import hashlib
import json
import os
from pathlib import Path
from typing import Any, cast

import pytest

from src.tau_composition.resources import ExpressionBudgetError
from src.tau_composition.runtime import TauQueryError
from src.tau_workbench.codec import MAX_TASK_BYTES, decode_task, encode_task
from src.tau_workbench.examples import message_task
from tools import tau_workbench


@pytest.fixture
def native() -> str:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if binary is None or binary == "":
        pytest.skip("explicit native Tau binary required")
    return cast(str, binary)


def run(capsys, *argv: str) -> tuple[int, dict[str, Any]]:
    code = tau_workbench.main(list(argv))
    output = capsys.readouterr()
    assert output.err == ""
    return code, json.loads(output.out)


def test_describe_is_parser_derived_and_scope_bound(capsys) -> None:
    code, result = run(capsys, "describe")
    assert code == 0
    assert result["schema"] == "tau-workbench/cli-v1"
    assert set(result["commands"]) == {"describe", "example", "compile"}
    compile_flags = {
        flag
        for item in result["commands"]["compile"]
        for flag in item["flags"]
    }
    assert {"--task", "--tau", "--order", "--out"} <= compile_flags
    tau_option = next(
        item for item in result["commands"]["compile"] if item["name"] == "tau"
    )
    assert tau_option["required"] is True
    assert result["authority"] == "NONE"
    assert result["runtime_mounted"] is False
    assert result["effects"]["compile"]["candidate_source_execution"] is False
    assert result["limits"]["task_bytes"] == MAX_TASK_BYTES
    assert result["limits"]["bits"] == [1, 8]
    assert result["exit_codes"] == {
        "0": "completed", "2": "invalid_input", "3": "UNKNOWN",
    }
    assert any("CPython" in claim for claim in result["nonclaims"])
    assert any("novelty" in claim for claim in result["nonclaims"])
    assert any("maximum-volume" in claim for claim in result["nonclaims"])


def test_example_is_the_closed_message_task_encoding(capsys) -> None:
    code, result = run(capsys, "example")
    assert code == 0
    task = decode_task(json.dumps(result))
    assert task == message_task()
    assert encode_task(task) == result


def test_malformed_task_file_is_rejected_before_native_creation(
    capsys, monkeypatch, tmp_path: Path,
) -> None:
    path = tmp_path / "malformed.json"
    path.write_bytes(b"{")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("native runtime was created for malformed input")

    monkeypatch.setattr(tau_workbench, "TauRuntime", forbidden)
    code, result = run(
        capsys, "compile", "--task", str(path), "--tau", "/bin/true",
        "--out", str(tmp_path / "artifacts"),
    )
    assert code == 2
    assert result == {
        "authority": "NONE", "error_code": "task_json", "status": "invalid_input",
    }


def test_closed_schema_and_order_reject_before_native_creation(
    capsys, monkeypatch, tmp_path: Path,
) -> None:
    payload = encode_task(message_task())
    payload["unexpected"] = True
    path = tmp_path / "closed-schema.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("native runtime was created for closed-schema input")

    monkeypatch.setattr(tau_workbench, "TauRuntime", forbidden)
    code, result = run(
        capsys, "compile", "--task", str(path), "--tau", "/bin/true",
        "--out", str(tmp_path / "schema-artifacts"),
    )
    assert code == 2 and result["error_code"] == "task_object_shape"
    assert not (tmp_path / "schema-artifacts").exists()

    code, result = run(
        capsys, "compile", "--order", "encoder,encoder,decoder",
        "--tau", "/bin/true", "--out", str(tmp_path / "order-artifacts"),
    )
    assert code == 2 and result["error_code"] == "order_permutation"
    assert not (tmp_path / "order-artifacts").exists()


def test_unsupported_candidate_source_is_rejected_without_a_native_query(
    capsys, tmp_path: Path, monkeypatch,
) -> None:
    payload = encode_task(message_task())
    payload["stages"][0]["programs"][0]["source"] = (
        "def transform(x):\n    return abs(x)\n"
    )
    path = tmp_path / "unsupported-source.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("unsupported source reached native Tau")

    from src.tau_composition import runtime as runtime_module

    monkeypatch.setattr(runtime_module, "_run_subprocess_with_output_caps", forbidden)
    output = tmp_path / "unsupported-artifacts"
    code, result = run(
        capsys, "compile", "--task", str(path), "--tau", "/bin/true",
        "--out", str(output),
    )
    assert code == 2
    assert result["status"] == "invalid_input"
    assert not output.exists()


def test_existing_output_directory_is_never_overwritten(
    capsys, monkeypatch, tmp_path: Path,
) -> None:
    output = tmp_path / "existing"
    output.mkdir()
    keep = output / "keep.txt"
    keep.write_text("prior evidence", encoding="utf-8")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("native runtime was created for an existing output")

    monkeypatch.setattr(tau_workbench, "TauRuntime", forbidden)
    code, result = run(
        capsys, "compile", "--tau", "/bin/true", "--out", str(output),
    )
    assert code == 2
    assert result["error_code"] == "output_directory_exists"
    assert keep.read_text(encoding="utf-8") == "prior evidence"
    assert tuple(path.name for path in output.iterdir()) == ("keep.txt",)


def test_report_is_published_only_after_every_dependency_is_written(monkeypatch, tmp_path) -> None:
    output = tmp_path / "incomplete"
    real = Path.write_bytes
    def fail_task(path, data):
        if path.name == "task.json":
            raise OSError("simulated_artifact_write_failure")
        return real(path, data)
    monkeypatch.setattr(Path, "write_bytes", fail_task)
    with pytest.raises(OSError, match="simulated_artifact_write_failure"):
        tau_workbench._write_artifacts(output, {"report.json": b'{"status":"compiled_native_checked"}',
                                                "stage_00.tau": b"gate", "task.json": b"{}"})
    assert not (output / "report.json").exists()


def test_native_unknown_writes_no_artifacts(capsys, monkeypatch, tmp_path: Path) -> None:
    output = tmp_path / "unknown"

    def unavailable(*_args, **_kwargs):
        raise TauQueryError("native_timeout")

    monkeypatch.setattr(tau_workbench, "TauRuntime", unavailable)
    code, result = run(
        capsys, "compile", "--tau", "/bin/true", "--out", str(output),
    )
    assert code == 3
    assert result == {
        "authority": "NONE", "error_code": "native_timeout", "status": "UNKNOWN",
    }
    assert not output.exists()


def test_expression_unknown_writes_no_artifacts(capsys, monkeypatch, tmp_path: Path) -> None:
    output = tmp_path / "expression-unknown"

    def fail_compile(*_args, **_kwargs):
        raise ExpressionBudgetError("expression_node_bound")

    monkeypatch.setattr(tau_workbench, "compile_task", fail_compile)
    code, result = run(
        capsys, "compile", "--tau", "/bin/true", "--out", str(output),
    )
    assert code == 3
    assert result == {
        "authority": "NONE", "error_code": "expression_node_bound", "status": "UNKNOWN",
    }
    assert not output.exists()


def test_invalid_tau_binary_writes_no_artifacts(capsys, tmp_path: Path) -> None:
    output = tmp_path / "missing-binary"
    code, result = run(
        capsys, "compile", "--tau", str(tmp_path / "missing-tau"),
        "--out", str(output),
    )
    assert code == 2
    assert result["error_code"] == "tau_binary"
    assert not output.exists()


def test_compiled_report_binds_admitted_sources_and_native_labels(
    capsys, tmp_path: Path, native: str,
) -> None:
    output = tmp_path / "compiled"
    code, report = run(
        capsys, "compile", "--tau", native, "--out", str(output),
    )
    assert code == 0
    task = message_task()
    assert report["schema"] == "tau-workbench/compile-v1"
    assert report["status"] == "compiled_native_checked"
    assert report["authority"] == "NONE"
    assert report["runtime_mounted"] is False
    assert report["task_id"] == task.subject_id
    assert report["expansion_order"] == [stage.name for stage in task.stages]
    assert report["source_counts"] == {
        "candidate_sources": 24,
        "admitted_candidate_sources": sum(
            stage["admitted_candidate_count"] for stage in report["stages"]
        ),
        "source_input_evaluations": 6144,
        "domain_values_per_source": 256,
    }
    assert report["native_queries"] == len(report["native_query_labels"])
    assert report["native_queries"] > 0
    assert len(report["binary_sha256"]) == 64

    expected_candidate_files: set[str] = set()
    for stage_index, stage_report in enumerate(report["stages"]):
        gate_file = output / stage_report["gate_file"]
        gate_bytes = gate_file.read_bytes()
        assert hashlib.sha256(gate_bytes).hexdigest() == stage_report["gate_sha256"]
        assert b"authority: NONE" in gate_bytes
        assert len(stage_report["candidates"]) == stage_report["admitted_candidate_count"]
        for class_report in stage_report["admitted_classes"]:
            assert class_report["class_code"] in stage_report["admitted_class_codes"]
            for candidate in class_report["candidates"]:
                candidate_index = candidate["candidate_index"]
                program = task.stages[stage_index].programs[candidate_index]
                filename = f"stage_{stage_index:02d}_candidate_{candidate_index:02d}.py"
                expected_candidate_files.add(filename)
                assert candidate["file"] == filename
                assert candidate["name"] == program.name
                assert candidate["class_code"] == class_report["class_code"]
                assert (output / filename).read_bytes() == program.source
                assert candidate["sha256"] == program.sha256
                assert candidate["source_sha256"] == program.sha256

    artifact_names = {path.name for path in output.iterdir()}
    assert expected_candidate_files <= artifact_names
    assert {"task.json", "report.json", "native_queries.json"} <= artifact_names
    assert decode_task((output / "task.json").read_text(encoding="utf-8")) == task
    records = json.loads((output / "native_queries.json").read_text(encoding="utf-8"))
    assert len(records) == len(report["native_query_labels"])
    for label, record in zip(report["native_query_labels"], records, strict=True):
        assert label["operation"] == record["operation"]
        assert label["binary_sha256"] == record["binary_sha256"]
        assert label["query_sha256"] == hashlib.sha256(
            record["query"].encode("utf-8")
        ).hexdigest()
    assert json.loads((output / "report.json").read_text(encoding="utf-8")) == report
    assert report["artifacts"] == sorted(artifact_names)


def test_compiled_report_honors_full_stage_order(
    capsys, tmp_path: Path, native: str,
) -> None:
    output = tmp_path / "reordered"
    code, report = run(
        capsys, "compile", "--tau", native, "--order", "decoder", "adapter", "encoder",
        "--out", str(output),
    )
    assert code == 0
    assert report["expansion_order"] == ["decoder", "adapter", "encoder"]
