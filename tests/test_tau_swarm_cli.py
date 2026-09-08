"""JSON contract of tools/tau_swarm.py; native fixtures stay explicit."""

import hashlib
import json
import os

import pytest

from src.tau_composition.runtime import TauQueryError
from src.tau_swarm.codec import decode_problem, encode_problem
from tools import tau_swarm


@pytest.fixture
def native() -> str:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if not binary:
        pytest.skip("explicit native Tau binary required")
    return binary


def run(capsys, *argv):
    code = tau_swarm.main(list(argv))
    return code, json.loads(capsys.readouterr().out)


def test_describe_publishes_discoverable_commands_and_limits(capsys) -> None:
    code, result = run(capsys, "describe")
    assert code == 0
    assert result["schema"] == "tau-swarm/cli-v1"
    assert result["authority"] == "NONE" and result["runtime_mounted"] is False
    assert set(result["commands"]) == {"describe", "example", "compile"}
    flags = {flag for item in result["commands"]["compile"] for flag in item["flags"]}
    assert {"--problem", "--example", "--balanced-anchor", "--order", "--tau",
            "--environment", "--out"} <= flags
    assert result["problem_schema"] == "tau-swarm/problem-v1"
    assert result["exit_codes"] == {"0": "completed", "2": "invalid_input",
                                    "3": "UNKNOWN"}
    assert result["limits"]["inspection_control_bits"] == 10
    assert "agent execution" in result["nonclaims"] and result["recovery"]
    for name in ("describe", "example", "compile"):
        assert any(item["name"] for item in result["commands"][name]) or name == "describe"


@pytest.mark.parametrize("name", ["planning", "asymmetric", "triangle"])
def test_example_emits_closed_real_boolean_problem_data(capsys, name) -> None:
    code, result = run(capsys, "example", name)
    assert code == 0
    assert set(result) == {"schema", "contract", "blocks", "anchor"}
    assert result["schema"] == "tau-swarm/problem-v1"
    problem = decode_problem(json.dumps(result))
    assert encode_problem(problem) == result
    constants = [term["value"] for term in result["anchor"].values()
                 if term["kind"] == "constant"]
    assert constants and all(type(value) is bool for value in constants)


def test_balanced_anchor_only_applies_to_the_triangle_example(capsys) -> None:
    code, result = run(capsys, "example", "triangle", "--balanced-anchor")
    assert code == 0
    assert result["anchor"]["left_low"] == {"kind": "constant", "value": True}
    code, result = run(capsys, "example", "planning", "--balanced-anchor")
    assert code == 2 and result["error_code"] == "balanced_anchor_requires_triangle"
    assert result["status"] == "invalid_input" and result["authority"] == "NONE"


@pytest.mark.parametrize("argv", [
    ("compile", "--example", "triangle"),
    ("compile", "--tau", "/nonexistent/tau"),
    ("compile", "--example", "triangle", "--problem", "p.json", "--tau", "t"),
    ("example",),
    ("example", "unknown"),
    ("unknown",),
    (),
])
def test_argument_errors_are_exact_invalid_input(capsys, argv) -> None:
    code, result = run(capsys, *argv)
    assert code == 2
    assert result["status"] == "invalid_input"
    assert result["error_code"].startswith("argument_error")


def test_duplicate_keys_in_a_problem_file_fail_before_any_native_work(
        capsys, tmp_path) -> None:
    path = tmp_path / "problem.json"
    text = json.dumps(encode_problem(tau_swarm.example("asymmetric")))
    path.write_text("{" + '"schema": "tau-swarm/problem-v1", ' + text[1:],
                    encoding="utf-8")
    code, result = run(capsys, "compile", "--problem", str(path),
                       "--tau", "/nonexistent/tau")
    assert code == 2 and result["error_code"] == "duplicate_json_key"


def test_invalid_order_is_rejected_before_the_runtime_is_built(capsys) -> None:
    code, result = run(capsys, "compile", "--example", "asymmetric",
                       "--order", "A,A", "--tau", "/nonexistent/tau")
    assert code == 2 and result["error_code"] == "expansion_order_permutation"
    code, result = run(capsys, "compile", "--example", "asymmetric",
                       "--order", "", "--tau", "/nonexistent/tau")
    assert code == 2 and result["error_code"] == "expansion_order_permutation"


@pytest.mark.parametrize("text,code", [
    ('{"allow_breaking": 1}', "exact_boolean_required"),
    ('{"other": true}', "inspection_environment_fields"),
    ('[]', "inspection_environment_fields"),
    ('{"allow_breaking": true, "allow_breaking": false}', "duplicate_json_key"),
])
def test_environment_json_must_be_exact(capsys, text, code) -> None:
    exit_code, result = run(capsys, "compile", "--example", "planning",
                            "--environment", text, "--tau", "/nonexistent/tau")
    assert exit_code == 2 and result["error_code"] == code


def test_native_unavailability_is_reported_as_unknown(capsys, monkeypatch) -> None:
    def unavailable(*_args, **_kwargs):
        raise TauQueryError("native_timeout")

    monkeypatch.setattr(tau_swarm, "TauRuntime", unavailable)
    code, result = run(capsys, "compile", "--example", "asymmetric", "--tau", "/bin/true")
    assert code == 3
    assert result == {"status": "UNKNOWN", "error_code": "native_timeout",
                      "authority": "NONE"}


def test_a_missing_binary_never_completes_and_writes_nothing(capsys, tmp_path) -> None:
    out = tmp_path / "out"
    code, result = run(capsys, "compile", "--example", "asymmetric",
                       "--tau", str(tmp_path / "absent-tau"), "--out", str(out))
    assert code == 2
    assert result["status"] == "invalid_input"
    assert not out.exists()


def test_compiled_example_writes_verifiable_artifacts(capsys, tmp_path, native) -> None:
    out = tmp_path / "asymmetric"
    code, report = run(capsys, "compile", "--example", "asymmetric",
                       "--tau", native, "--out", str(out))
    assert code == 0
    assert report["status"] == "compiled_native_checked"
    assert report["authority"] == "NONE" and report["runtime_mounted"] is False
    assert report["expansion_order"] == ["A", "B"]
    assert report["native_queries"] > 0 and len(report["binary_sha256"]) == 64
    assert report["domains"][0]["input_order"] == ["a"]
    assert report["domains"][1]["input_order"] == ["b", "c"]
    for name in ("problem.json", "report.json", "native_queries.json",
                 "agent_00.tau", "agent_00.contract.json",
                 "agent_01.tau", "agent_01.contract.json"):
        assert (out / name).is_file()
    for domain in report["domains"]:
        payload = (out / domain["gate_file"]).read_bytes()
        assert hashlib.sha256(payload).hexdigest() == domain["gate_sha256"]
        assert b"authority: NONE" in payload
    assert decode_problem((out / "problem.json").read_text(encoding="utf-8")) == \
        tau_swarm.example("asymmetric")
    records = json.loads((out / "native_queries.json").read_text(encoding="utf-8"))
    assert len(records) >= report["native_queries"]
    assert json.loads((out / "report.json").read_text(encoding="utf-8")) == report


def test_custom_problem_file_and_explicit_order_compile(capsys, tmp_path, native) -> None:
    path = tmp_path / "triangle.json"
    path.write_text(json.dumps(encode_problem(tau_swarm.example("triangle"))),
                    encoding="utf-8")
    out = tmp_path / "triangle"
    code, report = run(capsys, "compile", "--problem", str(path), "--order",
                       "right,left", "--tau", native, "--out", str(out))
    assert code == 0
    assert report["expansion_order"] == ["right", "left"]
    assert [domain["agent"] for domain in report["domains"]] == ["left", "right"]
    assert (out / "agent_01.contract.json").is_file()


def test_environment_inspection_reports_the_documented_tradeoff(
        capsys, tmp_path, native) -> None:
    out = tmp_path / "planning"
    code, report = run(capsys, "compile", "--example", "planning", "--environment",
                       '{"allow_breaking": true}', "--tau", native, "--out", str(out))
    assert code == 0
    inspection = report["inspection"]
    assert inspection["schema"] == "tau-swarm/inspection-v1"
    assert inspection["independent_combinations"] == 3
    assert inspection["all_globally_feasible_combinations"] == 15
    assert inspection["envelope_id"] == report["envelope_id"]
    assert json.loads((out / "inspection.json").read_text(encoding="utf-8")) == inspection
    schema_agent = next(a for a in inspection["agents"] if a["agent"] == "schema")
    assert schema_agent["choice_count"] == len(schema_agent["choices"])
    for excluded in schema_agent["excluded_choices"]:
        assert excluded["violated_requirements"]


def test_existing_output_directory_is_never_overwritten(capsys, tmp_path, native) -> None:
    out = tmp_path / "used"
    out.mkdir()
    (out / "keep.txt").write_text("prior evidence", encoding="utf-8")
    code, result = run(capsys, "compile", "--example", "asymmetric",
                       "--tau", native, "--out", str(out))
    assert code == 2 and result["error_code"] == "output_directory_exists"
    assert [path.name for path in out.iterdir()] == ["keep.txt"]
    assert (out / "keep.txt").read_text(encoding="utf-8") == "prior evidence"
