"""Independent obligations for the bounded Tau composition research surface."""

from __future__ import annotations

import json
import os
import sys
from itertools import permutations, product

import pytest

from src.tau_composition import runtime as runtime_module
from src.tau_composition.codec import SCHEMA, decode_contract, encode_contract, export_tau
from src.tau_composition.compiler import CompiledRepair, RepairCompiler, _solution_map
from src.tau_composition.examples import changed_chain, coupled_recovery, permission_chain
from src.tau_composition.models import Contract, RepairMap, compose_maps
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.scheduling import strongly_connected_groups, topological_order
from src.tau_composition.terms import constant, meet, variable


def _coupled_legal(paused: bool, debit: bool, credit: bool) -> bool:
    """Independent host-domain rule for coupled_recovery."""

    return not (paused and debit) and debit == credit


def _chain_legal(bits: tuple[bool, ...], *, changed: bool) -> bool:
    forward = all(not bits[index] or bits[index + 1] for index in range(len(bits) - 1))
    return forward and (not changed or not bits[-1] or bits[-2])


def _values_for(names: tuple[str, ...]):
    for bits in product((False, True), repeat=len(names)):
        yield dict(zip(names, bits, strict=True))


def _control_bits(values: dict[str, bool], controls: tuple[str, ...]) -> tuple[bool, ...]:
    return tuple(values[name] for name in controls)


def _native_runtime(binary: str) -> TauRuntime:
    return TauRuntime(binary, timeout_seconds=8.0)


@pytest.fixture
def native_binary() -> str:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if binary is None:
        pytest.skip("set TAU_COMPOSITION_BIN to run native Tau composition obligations")
    return binary


def test_native_coupled_recovery_is_a_retraction_and_scc_closes_the_unsafe_order(
    native_binary: str,
) -> None:
    """Given every host bit-vector, compiled output is exactly the legal image."""

    contract = coupled_recovery()
    runtime = _native_runtime(native_binary)
    compiler = RepairCompiler(runtime)
    local_groups = tuple(
        Contract(contract.name, contract.environment, contract.controls, (requirement,))
        for requirement in contract.requirements
    )
    local_repairs = tuple(compiler.native_repair(group) for group in local_groups)
    naive = compose_maps(local_repairs, contract.controls)
    witness = {"paused": True, "debit": False, "credit": True}

    naive_witness = naive.apply(witness)
    assert naive_witness == {"paused": True, "debit": True, "credit": True}
    assert not _coupled_legal(**naive_witness)

    analysis = compiler.analyze_order(contract, naive)
    assert analysis.safe_environment.evaluate({"paused": False}) is True
    assert analysis.safe_environment.evaluate({"paused": True}) is False
    assert analysis.feasible_environment.evaluate({"paused": False}) is True
    assert analysis.feasible_environment.evaluate({"paused": True}) is True
    assert analysis.covers_feasible_environment is False

    compiled = compiler.compile(contract)
    assert compiled.merge_rounds == 1
    assert compiled.propose(witness) == {"paused": True, "debit": False, "credit": False}

    for paused in (False, True):
        observed_image: set[tuple[bool, bool]] = set()
        expected_image = {
            (debit, credit)
            for debit, credit in product((False, True), repeat=2)
            if _coupled_legal(paused, debit, credit)
        }
        for debit, credit in product((False, True), repeat=2):
            original = {"paused": paused, "debit": debit, "credit": credit}
            before = dict(original)
            proposed = compiled.propose(original)
            repeated = compiled.propose(proposed)

            assert original == before
            assert _coupled_legal(**proposed)
            assert repeated == proposed
            if _coupled_legal(paused, debit, credit):
                assert proposed == original
            observed_image.add((proposed["debit"], proposed["credit"]))
        assert observed_image == expected_image


def test_native_permission_chain_orders_acyclic_groups_and_reuses_only_matching_templates(
    native_binary: str,
) -> None:
    """Given a chain and one changed edge, warm replay reaches the fresh legal image."""

    base = permission_chain(3)
    runtime = _native_runtime(native_binary)
    compiler = RepairCompiler(runtime)
    first = compiler.compile(base)
    records_after_first = len(runtime.records)
    second = compiler.compile(base)

    assert first.merge_rounds == 0
    assert len(first.groups) == len(base.requirements)
    assert all(len(group) == 1 for group in first.groups)
    schedule_position = {group: index for index, group in enumerate(first.schedule)}
    assert all(schedule_position[source] < schedule_position[target] for source, target in first.dependency_edges)
    assert second.native_queries == 0
    assert len(runtime.records) == records_after_first
    assert second.cache_hits > 0

    legal_image = {
        bits for bits in product((False, True), repeat=len(base.controls)) if _chain_legal(bits, changed=False)
    }
    observed_image: set[tuple[bool, ...]] = set()
    for original in _values_for(base.controls):
        proposed = first.propose(original)
        original_bits = _control_bits(original, base.controls)
        proposed_bits = _control_bits(proposed, base.controls)

        assert _chain_legal(proposed_bits, changed=False)
        if _chain_legal(original_bits, changed=False):
            assert proposed == original
        observed_image.add(proposed_bits)
    assert observed_image == legal_image

    changed = changed_chain(base)
    old_legal_new_illegal = dict(zip(changed.controls, (False, False, False, True), strict=True))
    assert first.propose(old_legal_new_illegal) == old_legal_new_illegal
    records_before_changed = len(runtime.records)
    warm = compiler.compile(changed)
    fresh = RepairCompiler(_native_runtime(native_binary)).compile(changed)

    assert len(runtime.records) > records_before_changed
    assert warm.propose(old_legal_new_illegal) != old_legal_new_illegal

    changed_legal_image = {
        bits for bits in product((False, True), repeat=len(changed.controls)) if _chain_legal(bits, changed=True)
    }
    warm_image = {
        _control_bits(warm.propose(values), changed.controls) for values in _values_for(changed.controls)
    }
    fresh_image = {
        _control_bits(fresh.propose(values), changed.controls) for values in _values_for(changed.controls)
    }
    assert warm_image == changed_legal_image
    assert fresh_image == changed_legal_image


def test_scope_disjoint_mutation_needs_no_native_preservation_query() -> None:
    class CountingRuntime:
        def __init__(self) -> None:
            self.calls = 0

        def valid(self, _query: str) -> bool:
            self.calls += 1
            return False

    runtime = CountingRuntime()
    compiler = RepairCompiler(runtime)  # type: ignore[arg-type]
    repair = RepairMap((("debit", constant(False)),))
    requirement = meet(variable("paused"), variable("credit"))

    assert compiler.preserves(repair, requirement) is True
    assert runtime.calls == 0


def test_scheduler_matches_an_independent_permutation_oracle_for_all_three_node_graphs() -> None:
    nodes = tuple(range(3))
    possible_edges = tuple(product(nodes, repeat=2))
    for mask in range(1 << len(possible_edges)):
        edges = frozenset(
            edge for index, edge in enumerate(possible_edges) if mask & (1 << index)
        )
        legal_orders = [
            order
            for order in permutations(nodes)
            if all(order.index(source) < order.index(target) for source, target in edges)
        ]
        actual = topological_order(len(nodes), edges)

        assert (actual is None) is (not legal_orders)
        if actual is not None:
            assert actual in legal_orders


def test_scheduler_preserves_edge_orientation_and_returns_cycle_partitions() -> None:
    assert topological_order(3, frozenset({(2, 1), (1, 0)})) == (2, 1, 0)
    edges = frozenset({(0, 1), (1, 0), (1, 2), (2, 3), (3, 2), (3, 4)})

    assert strongly_connected_groups(5, edges) == ((0, 1), (2, 3), (4,))


def _codec_payload() -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "name": "codec_case",
        "environment": ["paused"],
        "controls": ["debit"],
        "requirements": [
            {
                "name": "paused_blocks_debit",
                "residual": {
                    "kind": "meet",
                    "operands": [
                        {"kind": "variable", "value": "paused"},
                        {"kind": "variable", "value": "debit"},
                    ],
                },
            }
        ],
    }


def test_codec_accepts_closed_contracts_and_export_is_data_only(capsys: pytest.CaptureFixture[str]) -> None:
    payload = _codec_payload()
    contract = decode_contract(json.dumps(payload))
    repair = RepairMap((("debit", constant(False)),))
    compiled = CompiledRepair(
        contract=contract,
        repair=repair,
        groups=(("paused_blocks_debit",),),
        dependency_edges=(),
        schedule=(0,),
        merge_rounds=0,
        native_queries=0,
        cache_hits=0,
        binary_sha256="test-only",
    )
    before_contract = encode_contract(contract)

    generated = export_tau(compiled)

    assert encode_contract(contract) == before_contract == payload
    assert compiled.repair == repair
    assert "repair0" in generated
    assert "always (" in generated
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""


def test_codec_rejects_closed_shape_duplicates_bool_lookalikes_and_domain_violations() -> None:
    payload = _codec_payload()
    payload["unexpected"] = True
    with pytest.raises(ValueError, match="closed_object_shape"):
        decode_contract(json.dumps(payload))

    duplicate = (
        '{"schema":"tau-composition/contract-v1",'
        '"schema":"tau-composition/contract-v1",'
        '"name":"codec_case","environment":[],"controls":["debit"],'
        '"requirements":[{"name":"r","residual":{"kind":"constant","value":false}}]}'
    )
    with pytest.raises(ValueError, match="duplicate_json_key"):
        decode_contract(duplicate)

    for lookalike in (1, "true"):
        bool_payload = _codec_payload()
        bool_payload["requirements"] = [
            {"name": "bool_only", "residual": {"kind": "constant", "value": lookalike}}
        ]
        with pytest.raises(ValueError, match="constant value must be bool"):
            decode_contract(json.dumps(bool_payload))

    duplicate_coordinate = _codec_payload()
    duplicate_coordinate["controls"] = ["debit", "debit"]
    with pytest.raises(ValueError, match="duplicate_coordinate"):
        decode_contract(json.dumps(duplicate_coordinate))

    undeclared = _codec_payload()
    undeclared["requirements"] = [
        {"name": "outside", "residual": {"kind": "variable", "value": "outside"}}
    ]
    with pytest.raises(ValueError, match="undeclared_coordinate"):
        decode_contract(json.dumps(undeclared))


def test_native_solution_parser_keeps_coefficients_read_only_and_controls_owned() -> None:
    aliases = {"a": "paused", "v0": "debit", "v1": "credit"}
    native_solution = "solution: {\nv0 := { a' }:sbf v0\nv1 := v1\n}"

    repair = _solution_map(native_solution, aliases, ("debit", "credit"))
    proposed = repair.apply({"paused": True, "debit": True, "credit": False})

    assert tuple(name for name, _term in repair.assignments) == ("debit", "credit")
    assert proposed == {"paused": True, "debit": False, "credit": False}
    with pytest.raises(TauQueryError, match="native_assignment_target"):
        _solution_map("solution: {\na := v0\nv0 := v0\nv1 := v1\n}", aliases, ("debit", "credit"))


@pytest.mark.parametrize(
    ("subprocess_result", "expected_code"),
    [
        ((1, "", "timed out"), "native_timeout"),
        ((0, "garbled native output", ""), "native_result_shape"),
        ((0, "%1: T", "Engine Error"), "native_error"),
    ],
)
def test_runtime_failures_are_unknown_and_never_logical_false(
    monkeypatch: pytest.MonkeyPatch,
    subprocess_result: tuple[int, str, str],
    expected_code: str,
) -> None:
    runtime = TauRuntime(sys.executable, timeout_seconds=1.0)

    def fake_run(*_args: object, **_kwargs: object) -> tuple[int, str, str]:
        return subprocess_result

    monkeypatch.setattr(runtime_module, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(TauQueryError) as raised:
        runtime.valid("v0:sbf = 0:sbf")
    assert raised.value.code == expected_code
    assert len(runtime.records) == 1
