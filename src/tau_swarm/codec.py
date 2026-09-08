"""Closed JSON schema for bounded, advisory Tau Swarm problems.

Decoding is local data validation over exact host booleans. It mounts no
runtime, confers no credential and authorizes no execution of any proposal.
The contract sub-object is delegated to the existing composition codec so that
both tools accept exactly one term grammar and one term budget.
"""

from __future__ import annotations

import json

from src.tau_composition.codec import (
    _object,
    _term,
    _unique_object,
    decode_contract,
    encode_contract,
)
from src.tau_composition.models import Contract, RepairMap

from .models import AgentBlock, SwarmProblem

SCHEMA = "tau-swarm/problem-v1"
MAX_PROBLEM_BYTES = 512_000
MAX_BLOCKS = 16
MAX_ANCHOR_KEYS = 256
ANCHOR_TERM_BUDGET = 4096
_ROOT_FIELDS = {"schema", "contract", "blocks", "anchor"}
_BLOCK_FIELDS = {"name", "controls"}


def _reject_constant(_name: str) -> object:
    """Refuse the nonstandard JSON tokens NaN, Infinity and -Infinity."""
    raise ValueError("json_constant")


def encode_problem(problem: SwarmProblem) -> dict[str, object]:
    """Render a representable problem, rejecting lossy or over-budget values."""
    if not isinstance(problem, SwarmProblem):
        raise ValueError("swarm_problem_type")
    payload: dict[str, object] = {
        "schema": SCHEMA,
        "contract": encode_contract(problem.contract),
        "blocks": [{"name": block.name, "controls": list(block.controls)}
                   for block in problem.blocks],
        "anchor": {name: term.canonical_data()
                   for name, term in problem.anchor.assignments},
    }
    decoded = decode_problem(json.dumps(payload, separators=(",", ":"), ensure_ascii=True))
    if decoded != problem:
        raise ValueError("problem_noncanonical_term")
    return payload


def decode_problem(text: str) -> SwarmProblem:
    """Validate closed problem text; malformed data is always a ValueError."""
    if type(text) is not str:
        raise ValueError("problem_text_type")
    try:
        return _decode(text)
    except (TypeError, RecursionError, UnicodeError) as exc:
        raise ValueError("malformed_problem_data") from exc


def _decode(text: str) -> SwarmProblem:
    if len(text.encode("utf-8")) > MAX_PROBLEM_BYTES:
        raise ValueError("problem_byte_bound")
    data = _object(
        json.loads(text, object_pairs_hook=_unique_object,
                   parse_constant=_reject_constant),
        _ROOT_FIELDS,
    )
    if data["schema"] != SCHEMA:
        raise ValueError("problem_schema")
    contract = _contract(data["contract"])
    blocks = _blocks(data["blocks"])
    anchor = _anchor(data["anchor"], contract.controls)
    # SwarmProblem owns the partition and environment-only anchor checks.
    return SwarmProblem(contract, blocks, anchor)


def _contract(value: object) -> Contract:
    if type(value) is not dict:
        raise ValueError("contract_object_shape")
    # Duplicate keys at every depth were already rejected by the outer parse.
    return decode_contract(json.dumps(value, separators=(",", ":")))


def _blocks(value: object) -> tuple[AgentBlock, ...]:
    if type(value) is not list:
        raise ValueError("blocks_list_shape")
    if not 1 <= len(value) <= MAX_BLOCKS:
        raise ValueError("problem_block_bound")
    blocks = []
    for raw in value:
        node = _object(raw, _BLOCK_FIELDS)
        if type(node["name"]) is not str:
            raise ValueError("block_name_type")
        controls = node["controls"]
        if type(controls) is not list:
            raise ValueError("block_control_list")
        if any(type(name) is not str for name in controls):
            raise ValueError("block_control_name_type")
        blocks.append(AgentBlock(node["name"], tuple(controls)))
    return tuple(blocks)


def _anchor(value: object, controls: tuple[str, ...]) -> RepairMap:
    if type(value) is not dict:
        raise ValueError("anchor_object_shape")
    if len(value) > MAX_ANCHOR_KEYS:
        raise ValueError("anchor_key_bound")
    if set(value) != set(controls):
        raise ValueError("anchor_control_coverage")
    budget = [ANCHOR_TERM_BUDGET]
    # Canonical assignment order is the contract's, never the JSON key order.
    return RepairMap(tuple((name, _term(value[name], budget)) for name in controls))
