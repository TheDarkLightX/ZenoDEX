"""Executable local choice gates preserve independent Boolean-domain oracles."""

from __future__ import annotations

import itertools
import os
import sys
from pathlib import Path

import pytest

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.terms import constant, join, meet, variable
from src.tau_swarm import exports
from src.tau_swarm.examples import asymmetric_choices, planning_swarm
from src.tau_swarm.models import AgentBlock, AgentDomain, AutonomyEnvelope, SwarmProblem


@pytest.fixture
def native() -> TauRuntime:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if not binary:
        pytest.skip("explicit native Tau binary required")
    return TauRuntime(Path(binary), timeout_seconds=3)


def _rows(contract: Contract) -> tuple[dict[str, bool], ...]:
    names = contract.environment + contract.controls
    return tuple(dict(zip(names, bits, strict=True))
                 for bits in itertools.product((False, True), repeat=len(names)))


def _one_bit_envelope(runtime: TauRuntime) -> AutonomyEnvelope:
    contract = Contract("one_bit", (), ("x",), (Requirement("zero", variable("x")),))
    block = AgentBlock("worker", ("x",))
    problem = SwarmProblem(contract, (block,), RepairMap((("x", constant(False)),)))
    return AutonomyEnvelope(problem, (AgentDomain(block, variable("x")),), ("worker",),
                            0, runtime.binary_sha256)


@pytest.mark.parametrize("own_count", (2, 3))
def test_native_agent_gate_matches_at_most_one_choice_oracle(
    native: TauRuntime, own_count: int
) -> None:
    from src.tau_swarm.compiler import AutonomyCompiler

    names = tuple(f"x{index}" for index in range(own_count))
    conflicts = tuple(meet(variable(left), variable(right))
                      for left, right in itertools.combinations(names, 2))
    controls = names + ("peer_choice",)
    contract = Contract("choice_planning", (), controls, (
        Requirement("choices", join(*conflicts, meet(variable(names[0]), variable("peer_choice")))),
    ))
    problem = SwarmProblem(
        contract, (AgentBlock("worker", names), AgentBlock("peer", ("peer_choice",))),
        RepairMap(tuple((name, constant(False)) for name in controls)),
    )
    envelope = AutonomyCompiler(native).compile(problem)
    rows = _rows(envelope.local_contract("worker"))
    before = tuple(dict(row) for row in rows)

    actual = exports.replay_agent_gate(native, envelope, "worker", rows)

    assert actual == tuple(sum(row.values()) <= 1 for row in rows)
    assert actual == tuple(envelope.permits("worker", row) for row in rows)
    assert rows == before
    source = exports.export_agent_gate(envelope, "worker")
    assert "peer_choice" not in source
    assert "authority: NONE" in source
    assert "o2[" not in source


def test_native_environment_gate_preserves_human_mode_and_local_choice_fields(native: TauRuntime) -> None:
    from src.tau_swarm.compiler import AutonomyCompiler

    envelope = AutonomyCompiler(native).compile(planning_swarm())
    rows = _rows(envelope.local_contract("schema"))

    actual = exports.replay_agent_gate(native, envelope, "schema", rows)

    expected = tuple(not (row["breaking"] and (row["additive"] or not row["allow_breaking"]))
                     for row in rows)
    assert actual == expected
    assert actual == tuple(envelope.permits("schema", row) for row in rows)
    source = exports.export_agent_gate(envelope, "schema")
    assert "# i1: environment allow_breaking" in source
    assert "# i2: choice breaking" in source
    assert "# i3: choice additive" in source
    assert "upgrade" not in source
    assert "migration" not in source


def test_native_constant_gate_returns_only_executed_row_results(native: TauRuntime) -> None:
    from src.tau_swarm.compiler import AutonomyCompiler

    envelope = AutonomyCompiler(native).compile(asymmetric_choices())
    steps = ({"a": False}, {"a": True}, {"a": False})
    start = len(native.records)

    assert exports.replay_agent_gate(native, envelope, "A", steps) == (True, True, True)
    records = native.records[start:]
    assert len(records) in {1, 4}
    assert all(record.operation == "execute_agent_gate" for record in records)


@pytest.mark.parametrize("steps, reason", (
    ((), "trace_length_bound"),
    ([{"x": False}], "trace_length_bound"),
    (({"x": False},) * 4097, "trace_length_bound"),
    ((None,), "trace_row_shape"),
    (({},), "coordinate_set_mismatch"),
    (({"x": False, "peer_choice": False},), "coordinate_set_mismatch"),
    (({"x": 0},), "exact_boolean_required"),
))
def test_invalid_local_rows_reject_before_native_io(
    monkeypatch: pytest.MonkeyPatch, steps: object, reason: str,
) -> None:
    runtime = TauRuntime(Path(sys.executable))
    envelope = _one_bit_envelope(runtime)

    def forbidden_call(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("invalid rows reached native IO")

    monkeypatch.setattr(exports, "_run_subprocess_with_output_caps", forbidden_call)
    with pytest.raises(ValueError, match=reason):
        exports.replay_agent_gate(runtime, envelope, "worker", steps)  # type: ignore[arg-type]
    assert runtime.records == []


def test_single_output_batch_replays_each_original_row_without_fabrication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime = TauRuntime(Path(sys.executable))
    envelope = _one_bit_envelope(runtime)
    seen: list[tuple[str, ...]] = []
    directories: list[Path] = []

    def one_row_process(_command: list[str], **kwargs: object) -> tuple[int, str, str]:
        directory = Path(str(kwargs["cwd"]))
        directories.append(directory)
        rows = tuple((directory / "input1.txt").read_text().splitlines())
        seen.append(rows)
        (directory / "permit.txt").write_text("1\n" if rows[0] == "0" else "0\n")
        return 0, "", ""

    monkeypatch.setattr(exports, "_run_subprocess_with_output_caps", one_row_process)
    steps = ({"x": False}, {"x": True}, {"x": False})

    assert exports.replay_agent_gate(runtime, envelope, "worker", steps) == (True, False, True)
    assert seen == [("0", "1", "0"), ("0",), ("1",), ("0",)]
    assert len(runtime.records) == 4
    assert all(not directory.exists() for directory in directories)
    assert steps == ({"x": False}, {"x": True}, {"x": False})


@pytest.mark.parametrize("output, reason", (
    (None, "native_gate_output_missing_or_large"),
    (b"1\n" * 100, "native_gate_output_missing_or_large"),
    (b"", "native_gate_trace_shape"),
    (b"1", "native_gate_trace_shape"),
    (b"1\n0\n", "native_gate_trace_shape"),
    (b"1\n0\n1\n0\n", "native_gate_trace_shape"),
    (b"1\nmaybe\n1\n", "native_gate_trace_shape"),
    (b"\xff\n", "native_gate_trace_shape"),
    (b"0\n0\n0\n", "native_gate_replay_disagreement"),
))
def test_missing_truncated_or_nonboolean_native_output_never_permits(
    monkeypatch: pytest.MonkeyPatch, output: bytes | None, reason: str,
) -> None:
    runtime = TauRuntime(Path(sys.executable))
    envelope = _one_bit_envelope(runtime)
    directories: list[Path] = []

    def malformed_process(_command: list[str], **kwargs: object) -> tuple[int, str, str]:
        directory = Path(str(kwargs["cwd"]))
        directories.append(directory)
        if output is not None:
            (directory / "permit.txt").write_bytes(output)
        return 0, "", ""

    monkeypatch.setattr(exports, "_run_subprocess_with_output_caps", malformed_process)
    with pytest.raises(TauQueryError, match=reason):
        exports.replay_agent_gate(runtime, envelope, "worker", ({"x": False},) * 3)
    assert len(runtime.records) == 1
    assert all(not directory.exists() for directory in directories)


def test_native_timeout_is_unknown_and_keeps_no_output_artifact(monkeypatch: pytest.MonkeyPatch) -> None:
    runtime = TauRuntime(Path(sys.executable))
    envelope = _one_bit_envelope(runtime)
    directories: list[Path] = []

    def timed_out(_command: list[str], **kwargs: object) -> tuple[int, str, str]:
        directories.append(Path(str(kwargs["cwd"])))
        return 1, "", "subprocess timed out"

    monkeypatch.setattr(exports, "_run_subprocess_with_output_caps", timed_out)
    with pytest.raises(TauQueryError, match="native_timeout"):
        exports.replay_agent_gate(runtime, envelope, "worker", ({"x": False},))
    assert len(runtime.records) == 1
    assert all(not directory.exists() for directory in directories)


def test_row_replay_respects_native_query_budget_without_partial_success(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime = TauRuntime(Path(sys.executable), max_queries=2)
    envelope = _one_bit_envelope(runtime)
    directories: list[Path] = []

    def constant_process(_command: list[str], **kwargs: object) -> tuple[int, str, str]:
        directory = Path(str(kwargs["cwd"]))
        directories.append(directory)
        (directory / "permit.txt").write_text("1\n")
        return 0, "", ""

    monkeypatch.setattr(exports, "_run_subprocess_with_output_caps", constant_process)
    with pytest.raises(TauQueryError, match="native_query_budget"):
        exports.replay_agent_gate(runtime, envelope, "worker", ({"x": False},) * 3)
    assert len(runtime.records) == 2
    assert len(directories) == 2
    assert all(not directory.exists() for directory in directories)


def test_unknown_agent_name_rejects_before_source_generation() -> None:
    runtime = TauRuntime(Path(sys.executable))
    with pytest.raises(ValueError, match="unknown_agent_block"):
        exports.export_agent_gate(_one_bit_envelope(runtime), "unowned")
