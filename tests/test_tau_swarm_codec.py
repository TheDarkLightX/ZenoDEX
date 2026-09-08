"""Closed-schema decoding rejects malformed advisory swarm problems locally."""

import json

import pytest

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.terms import Term, constant, join, variable
from src.tau_swarm.codec import SCHEMA, decode_problem, encode_problem
from src.tau_swarm.examples import (
    asymmetric_choices,
    balanced_anchor,
    planning_swarm,
    triangle_choices,
)
from src.tau_swarm.models import AgentBlock, SwarmProblem

FALSE_TERM = '{"kind": "constant", "value": false}'


def _balanced_triangle() -> SwarmProblem:
    problem = triangle_choices()
    return SwarmProblem(problem.contract, problem.blocks, balanced_anchor(problem))


def _text(problem: SwarmProblem, **overrides: object) -> str:
    payload = encode_problem(problem)
    payload.update(overrides)
    return json.dumps(payload)


@pytest.mark.parametrize("factory", [
    planning_swarm, asymmetric_choices, triangle_choices, _balanced_triangle])
def test_encoded_problems_round_trip_to_equal_values(factory) -> None:
    problem = factory()
    encoded = encode_problem(problem)
    assert set(encoded) == {"schema", "contract", "blocks", "anchor"}
    assert encoded["schema"] == SCHEMA == "tau-swarm/problem-v1"
    decoded = decode_problem(json.dumps(encoded))
    assert decoded == problem
    assert encode_problem(decoded) == encoded


def test_encoded_constants_are_exact_booleans_not_integers() -> None:
    anchor = encode_problem(planning_swarm())["anchor"]
    values = [term["value"] for term in anchor.values()]
    assert values and all(type(value) is bool for value in values)


def test_anchor_is_canonicalised_by_contract_control_order() -> None:
    problem = planning_swarm()
    payload = encode_problem(problem)
    payload["anchor"] = dict(reversed(list(payload["anchor"].items())))
    decoded = decode_problem(json.dumps(payload))
    assert tuple(name for name, _ in decoded.anchor.assignments) == problem.contract.controls
    assert decoded == problem


@pytest.mark.parametrize("mutate", [
    lambda text: "{" + '"schema": "tau-swarm/problem-v1", ' + text[1:],
    lambda text: text.replace('"name": "asymmetric_choices"',
                              '"name": "asymmetric_choices", "name": "x"', 1),
    lambda text: text.replace('"controls": ["a"]',
                              '"controls": ["a"], "controls": ["a"]', 1),
    lambda text: text.replace('"anchor": {', '"anchor": {"a": ' + FALSE_TERM + ", ", 1),
    lambda text: text.replace(FALSE_TERM,
                              '{"kind": "constant", "kind": "constant", "value": false}', 1),
])
def test_duplicate_json_keys_are_rejected_at_every_depth(mutate) -> None:
    text = mutate(_text(asymmetric_choices()))
    with pytest.raises(ValueError, match="duplicate_json_key"):
        decode_problem(text)


@pytest.mark.parametrize("payload,code", [
    ('[]', "closed_object_shape"),
    ('{"schema": "tau-swarm/problem-v1"}', "closed_object_shape"),
    ('{"schema": "tau-swarm/problem-v1", "contract": {}, "blocks": [], '
     '"anchor": {}, "extra": 1}', "closed_object_shape"),
    ('"text"', "closed_object_shape"),
    ('{}', "closed_object_shape"),
])
def test_root_object_is_closed(payload, code) -> None:
    with pytest.raises(ValueError, match=code):
        decode_problem(payload)


@pytest.mark.parametrize("overrides,code", [
    ({"schema": "tau-swarm/problem-v2"}, "problem_schema"),
    ({"schema": 1}, "problem_schema"),
    ({"contract": []}, "contract_object_shape"),
    ({"contract": "x"}, "contract_object_shape"),
    ({"blocks": {}}, "blocks_list_shape"),
    ({"blocks": []}, "problem_block_bound"),
    ({"blocks": [{"name": "A"}]}, "closed_object_shape"),
    ({"blocks": [{"name": 1, "controls": ["a"]}]}, "block_name_type"),
    ({"blocks": [{"name": "A", "controls": "a"}]}, "block_control_list"),
    ({"blocks": [{"name": "A", "controls": [1]}]}, "block_control_name_type"),
    ({"anchor": []}, "anchor_object_shape"),
    ({"anchor": {"a": {"kind": "constant", "value": False}}}, "anchor_control_coverage"),
])
def test_wrong_containers_and_types_are_typed_rejections(overrides, code) -> None:
    with pytest.raises(ValueError, match=code):
        decode_problem(_text(asymmetric_choices(), **overrides))


def test_foreign_and_nonbool_and_leaking_anchor_entries_are_rejected() -> None:
    problem = asymmetric_choices()
    foreign = encode_problem(problem)
    foreign["anchor"]["zz"] = {"kind": "constant", "value": False}
    with pytest.raises(ValueError, match="anchor_control_coverage"):
        decode_problem(json.dumps(foreign))
    nonbool = encode_problem(problem)
    nonbool["anchor"]["a"] = {"kind": "constant", "value": 1}
    with pytest.raises(ValueError):
        decode_problem(json.dumps(nonbool))
    leak = encode_problem(problem)
    leak["anchor"]["a"] = {"kind": "variable", "value": "b"}
    with pytest.raises(ValueError, match="anchor_reads_non_environment"):
        decode_problem(json.dumps(leak))


def test_partition_and_block_bounds_are_enforced() -> None:
    problem = asymmetric_choices()
    overlap = encode_problem(problem)
    overlap["blocks"] = [{"name": "A", "controls": ["a", "b"]},
                         {"name": "B", "controls": ["b", "c"]}]
    with pytest.raises(ValueError, match="block_control_overlap"):
        decode_problem(json.dumps(overlap))
    missing = encode_problem(problem)
    missing["blocks"] = [{"name": "A", "controls": ["a"]}]
    with pytest.raises(ValueError, match="block_control_partition"):
        decode_problem(json.dumps(missing))
    names = [f"x{index}" for index in range(17)]
    wide = {
        "schema": SCHEMA,
        "contract": {"schema": "tau-composition/contract-v1", "name": "wide",
                     "environment": [], "controls": names,
                     "requirements": [{"name": "zero",
                                       "residual": {"kind": "constant", "value": False}}]},
        "blocks": [{"name": f"b{index}", "controls": [name]}
                   for index, name in enumerate(names)],
        "anchor": {name: {"kind": "constant", "value": False} for name in names},
    }
    with pytest.raises(ValueError, match="problem_block_bound"):
        decode_problem(json.dumps(wide))


def test_anchor_key_bound_precedes_coverage_comparison() -> None:
    payload = encode_problem(asymmetric_choices())
    payload["anchor"] = {f"k{index}": {"kind": "constant", "value": False}
                         for index in range(257)}
    with pytest.raises(ValueError, match="anchor_key_bound"):
        decode_problem(json.dumps(payload))


def _wide_term(groups: int, width: int) -> dict[str, object]:
    leaf = {"kind": "variable", "value": "e"}
    group = {"kind": "join", "operands": [leaf] * width}
    return {"kind": "join", "operands": [group] * groups}


def test_aggregate_anchor_term_budget_is_shared_across_assignments() -> None:
    payload = {
        "schema": SCHEMA,
        "contract": {"schema": "tau-composition/contract-v1", "name": "budget",
                     "environment": ["e"], "controls": ["c0", "c1"],
                     "requirements": [{"name": "zero",
                                       "residual": {"kind": "constant", "value": False}}]},
        "blocks": [{"name": "only", "controls": ["c0", "c1"]}],
        "anchor": {"c0": _wide_term(20, 105), "c1": _wide_term(20, 105)},
    }
    with pytest.raises(ValueError, match="term_budget"):
        decode_problem(json.dumps(payload))


@pytest.mark.parametrize("text", [b"{}", None, 12, ["{}"]])
def test_input_must_be_exact_text(text) -> None:
    with pytest.raises(ValueError, match="problem_text_type"):
        decode_problem(text)


def test_oversized_text_is_rejected_before_parsing() -> None:
    with pytest.raises(ValueError, match="problem_byte_bound"):
        decode_problem('{"schema": "' + "x" * 512_001 + '"}')


@pytest.mark.parametrize("text,code", [
    ('{"schema": "\ud800"}', "malformed_problem_data"),
    ('{"schema": NaN, "contract": {}, "blocks": [], "anchor": {}}', "json_constant"),
    ("{not json", ""),
    ('{"schema": ' + '[' * 6000 + ']' * 6000 + '}', ""),
])
def test_malformed_data_is_normalised_to_value_error(text, code) -> None:
    with pytest.raises(ValueError, match=code):
        decode_problem(text)


def test_encode_rejects_foreign_objects() -> None:
    with pytest.raises(ValueError, match="swarm_problem_type"):
        encode_problem({"schema": SCHEMA})


@pytest.mark.parametrize("kind", [[], {}, None, True, 123])
def test_malformed_term_operator_is_a_typed_rejection(kind) -> None:
    payload = encode_problem(asymmetric_choices())
    payload["anchor"]["a"] = {
        "kind": kind, "operands": [{"kind": "constant", "value": False}],
    }
    code = "malformed_problem_data" if isinstance(kind, (list, dict)) else "term_operator_or_arity"
    with pytest.raises(ValueError, match=code):
        decode_problem(json.dumps(payload))


def test_encoder_rejects_a_model_outside_the_wire_profile() -> None:
    environment = tuple(f"e{i}" for i in range(129))
    problem = SwarmProblem(
        Contract("wide", environment, ("c",), (Requirement("zero", constant(False)),)),
        (AgentBlock("agent", ("c",)),),
        RepairMap((("c", join(*(variable(name) for name in environment))),)),
    )
    with pytest.raises(ValueError, match="term_operand_bound"):
        encode_problem(problem)


def test_encoder_rejects_terms_that_would_change_on_wire_round_trip() -> None:
    problem = SwarmProblem(
        Contract("raw", (), ("c",), (Requirement("zero", constant(False)),)),
        (AgentBlock("agent", ("c",)),),
        RepairMap((("c", Term("negate", operands=(constant(False),))),)),
    )
    with pytest.raises(ValueError, match="problem_noncanonical_term"):
        encode_problem(problem)
