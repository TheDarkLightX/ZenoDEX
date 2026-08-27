"""FORMAL-MODEL-001: executable bounded model and ESSO evidence for
``src/kernels/dex/global_settlement_core_v1.yaml``.

Evidence families (Test Hygiene Contract V1 vocabulary):

- ``formal``: ``python3 -m ESSO validate`` and ``python3 -m ESSO verify-multi``
  against the private toolchain, which is external to this checkout
  (``PYTHONPATH=/path/to/ESSO`` or an ``external/ESSO`` checkout).  The
  durable status ``BOUNDED_ESSO_VERIFIED_RESEARCH_ONLY`` rests on the exact
  replay recorded in the blueprint; the tests below bind the recorded IR hash,
  fingerprint, and obligation set to the tool output whenever the toolchain is
  present.  When it is absent those tests SKIP and that host's run is
  INCOMPLETE.  A skip is never a pass.
- ``stateful``, ``boundary``, ``negative_regression``, ``mutation``, ``replay``:
  a pure-Python interpreter of the same YAML (the executable bounded model)
  drives AAA scenarios, BVA cases, reject-is-exact-no-op cases, bounded sweeps,
  and named semantic mutants with RIPR (reach, infect, propagate, reveal)
  evidence.  The interpreter evaluates updates simultaneously over the
  pre-state and effects over the post-state.

Blueprint: ``docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md``.

Nothing here grants production, settlement, release, or value-moving
authority, and nothing here is a whole-DEX safety claim.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import itertools
import json
import os
import random
import re
import subprocess
import sys
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "global_settlement_core_v1.yaml"
BLUEPRINT = ROOT / "docs" / "research" / "ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md"
TYPES_SOURCE = ROOT / "src" / "core" / "global_settlement_types_v1.py"
EXTERNAL_ESSO = ROOT / "external" / "ESSO"
BASE_COMMIT = "f7e851565e063fb3e74b060a9c45f27b8621a8d7"
INITIAL_CANDIDATE_COMMIT = "f04bf4760a941966bf19e8c3c289b3c0d6c1feeb"
DURABLE_STATUS = "BOUNDED_ESSO_VERIFIED_RESEARCH_ONLY"
RETIRED_STATUS = "FORMAL_VERDICT_INCOMPLETE_ESSO_ABSENT"

# Exact replay facts recorded in the blueprint.  The IR hash covers the model
# file including ``meta``; the fingerprint covers the verified semantics.
RECORDED_IR_HASH = "sha256:ec6a4c4518b6c5655082e487e816f4bd1411dfb74479afcd656783916d34090a"
REVIEW_IR_HASH = "sha256:872a813305f2f34429c1f028918eb3e1bb5c5ce378c723501645c77b9098056b"
RECORDED_FINGERPRINT = "58a1a345fed1f25c7d98e22452764b9dccfc2df82ac66217b7b109dc58389c43"
RECORDED_ESSO_CODE_HASH = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"
RECORDED_OBLIGATIONS = frozenset({"init_implies_inv", "inductive_step"})

# Enforced source pins: blueprint row, this table, and the file must agree.
# Claim grade is source-pin evidence, never refinement evidence.
ENFORCED_PINS = {
    "src/core/global_settlement_types_v1.py": (
        "df06cbff2800ed7e2a1a296766cd132a86fdcce51c5d8a9da3a01791344c16b0"
    ),
    "src/core/global_economic_state_effect_refinement_v1.py": (
        "9e70b85ffc24e77fd7abf7a7a1e6aed8017f0f6ceac8d61e6c45e6f6dece7338"
    ),
    "zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs": (
        "81dfe788c02767d080c3a2dc1cadd814ad3e489cbbc2b6fbf66ecf21ee77ee01"
    ),
    "src/core/epoch_effect_composition_v1.py": (
        "a678e459c3d57462c20fb787160c5e1ef9ed0706e62c293449b21a978efdd045"
    ),
    "src/kernels/dex/global_settlement_core_v1.yaml": (
        "f3ede1340db83376d10b7d473fb58df20f9185e5ef4dc773acbf3fe40f0365b6"
    ),
}

GAP_IDS = tuple(f"GAP-{index:02d}" for index in range(1, 9))

ESSO_SKIP_REASON = (
    "ESSO toolchain absent (no external/ESSO checkout, no importable ESSO): "
    "formal verdict INCOMPLETE; a skip is not a pass"
)

# Closed command-kind encoding of the model (documented in meta.notes).
KIND_TRANSFER = 0
KIND_ISSUE = 1
KIND_BURN = 2
KIND_OPEN = 3
KIND_DRAIN = 4
KIND_UNKNOWN = 5
ASSET_A = 0
ASSET_B = 1

PARTITIONS = ("payer", "rest", "fee_alloc", "fee_residue", "obligation")
CORE_A = tuple(f"{name}_a" for name in (*PARTITIONS, "supply"))
CORE_B = tuple(f"{name}_b" for name in (*PARTITIONS, "supply"))
CONTROL = ("height", "consumed_0", "consumed_1", "consumed_2")
OBSERVED = CORE_A + CORE_B + CONTROL
ROWS = ("issue", "burn", "fee_charged", "fee_alloc", "fee_residue")

REJECT_CODES = (
    "RC_UNKNOWN_LANE",
    "RC_UNKNOWN_COMMAND",
    "RC_DUPLICATE_OCCURRENCE",
    "RC_STALE_REPLAY",
    "RC_UNAUTHORIZED",
    "RC_MISSING_TERMINAL_OBLIGATION",
    "RC_ZERO_AMOUNT",
    "RC_FEE_RECONCILIATION",
    "RC_INSUFFICIENT",
    "RC_UNREPRESENTABLE",
)

INVARIANT_IDS = (
    "inv_core_bounds",
    "inv_owned_equals_supply_a",
    "inv_owned_equals_supply_b",
    "inv_owned_step_a",
    "inv_owned_step_b",
    "inv_supply_step_a",
    "inv_supply_step_b",
    "inv_fee_step_a",
    "inv_fee_step_b",
    "inv_step_rows_nonnegative",
    "inv_reject_exact_noop",
    "inv_accept_advances_one",
    "inv_consumed_monotone",
)


# --------------------------------------------------------------------------- #
# Minimal interpreter for the esso-ir/v1 subset used by the model.
# --------------------------------------------------------------------------- #


class ModelError(AssertionError):
    """The executable bounded model rejected an input, a type, or an evaluation."""


_Fn = Callable[[dict[str, Any], dict[str, Any], dict[int, Any]], Any]


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _ints(values: list[Any], op: str) -> list[int]:
    if not values or any(not _is_int(value) for value in values):
        raise ModelError(f"{op} expects integer operands, got {values!r}")
    return values


def _bools(values: list[Any], op: str) -> list[bool]:
    if not values or any(not isinstance(value, bool) for value in values):
        raise ModelError(f"{op} expects boolean operands, got {values!r}")
    return values


def _pair(values: list[Any], op: str) -> tuple[Any, Any]:
    if len(values) != 2:
        raise ModelError(f"{op} expects two operands, got {len(values)}")
    return values[0], values[1]


def _euclid_div(n: int, d: int) -> int:
    if d == 0:
        return 0
    quotient = n // d
    if n - quotient * d < 0:
        quotient += 1
    return quotient


def _euclid_mod(n: int, d: int) -> int:
    return 0 if d == 0 else n % abs(d)


def _same_kind(a: Any, b: Any, op: str) -> None:
    if _is_int(a) != _is_int(b) or isinstance(a, bool) != isinstance(b, bool):
        raise ModelError(f"{op} compares values of different kinds: {a!r} vs {b!r}")


def _eq(values: list[Any]) -> bool:
    a, b = _pair(values, "=")
    _same_kind(a, b, "=")
    return a == b


def _ne(values: list[Any]) -> bool:
    a, b = _pair(values, "!=")
    _same_kind(a, b, "!=")
    return a != b


def _ordered(op: str, test: Callable[[int, int], bool]) -> Callable[[list[Any]], bool]:
    def run(values: list[Any]) -> bool:
        a, b = _pair(_ints(values, op), op)
        return test(a, b)

    return run


def _sub(values: list[Any]) -> int:
    a, b = _pair(_ints(values, "-"), "-")
    return a - b


def _product(values: list[Any]) -> int:
    result = 1
    for value in _ints(values, "*"):
        result *= value
    return result


def _div(values: list[Any]) -> int:
    a, b = _pair(_ints(values, "div"), "div")
    return _euclid_div(a, b)


def _mod(values: list[Any]) -> int:
    a, b = _pair(_ints(values, "mod"), "mod")
    return _euclid_mod(a, b)


def _not(values: list[Any]) -> bool:
    if len(values) != 1:
        raise ModelError(f"not expects one operand, got {len(values)}")
    return not _bools(values, "not")[0]


def _xor(values: list[Any]) -> bool:
    a, b = _pair(_bools(values, "xor"), "xor")
    return a != b


def _implies(values: list[Any]) -> bool:
    a, b = _pair(_bools(values, "=>"), "=>")
    return (not a) or b


_OPS: dict[str, Callable[[list[Any]], Any]] = {
    "and": lambda values: all(_bools(values, "and")),
    "or": lambda values: any(_bools(values, "or")),
    "not": _not,
    "xor": _xor,
    "=>": _implies,
    "=": _eq,
    "!=": _ne,
    "<": _ordered("<", lambda a, b: a < b),
    "<=": _ordered("<=", lambda a, b: a <= b),
    ">": _ordered(">", lambda a, b: a > b),
    ">=": _ordered(">=", lambda a, b: a >= b),
    "+": lambda values: sum(_ints(values, "+")),
    "-": _sub,
    "*": _product,
    "min": lambda values: min(_ints(values, "min")),
    "max": lambda values: max(_ints(values, "max")),
    "div": _div,
    "mod": _mod,
}


def _compile(node: Any) -> _Fn:
    """Compile one IR expression into a closure over (state, params, memo)."""

    if not isinstance(node, dict):
        raise ModelError(f"expression node must be a mapping, got {node!r}")
    if "const" in node:
        const = node["const"]
        if not _is_int(const):
            raise ModelError(f"const must be an integer, got {const!r}")
        return lambda state, params, memo: const
    if "bool" in node:
        flag = node["bool"]
        if not isinstance(flag, bool):
            raise ModelError(f"bool literal must be a boolean, got {flag!r}")
        return lambda state, params, memo: flag
    if "enum" in node:
        symbol = str(node["enum"])
        return lambda state, params, memo: symbol
    if "var" in node:
        name = str(node["var"])

        def read_var(state: dict[str, Any], params: dict[str, Any], memo: dict[int, Any]) -> Any:
            if name not in state:
                raise ModelError(f"unknown state var {name!r}")
            return state[name]

        return read_var
    if "param" in node:
        name = str(node["param"])

        def read_param(state: dict[str, Any], params: dict[str, Any], memo: dict[int, Any]) -> Any:
            if name not in params:
                raise ModelError(f"unknown param {name!r}")
            return params[name]

        return read_param
    if "op" not in node:
        raise ModelError(f"unsupported expression node {node!r}")
    key = id(node)
    op = str(node["op"])
    if op == "ite":
        cond = _compile(node["cond"])
        then = _compile(node["then"])
        other = _compile(node["else"])

        def ite(state: dict[str, Any], params: dict[str, Any], memo: dict[int, Any]) -> Any:
            if key in memo:
                return memo[key]
            chosen = _bools([cond(state, params, memo)], "ite")[0]
            value = then(state, params, memo) if chosen else other(state, params, memo)
            memo[key] = value
            return value

        return ite
    if op not in _OPS:
        raise ModelError(f"unsupported op {op!r}")
    impl = _OPS[op]
    args = [_compile(arg) for arg in node.get("args", [])]

    def apply(state: dict[str, Any], params: dict[str, Any], memo: dict[int, Any]) -> Any:
        if key in memo:
            return memo[key]
        value = impl([arg(state, params, memo) for arg in args])
        memo[key] = value
        return value

    return apply


@dataclass(frozen=True)
class Domain:
    kind: str
    lo: int = 0
    hi: int = 0
    symbols: tuple[str, ...] = ()

    def check(self, value: Any, name: str) -> None:
        if self.kind == "bool":
            if not isinstance(value, bool):
                raise ModelError(f"{name} must be a boolean, got {value!r}")
        elif self.kind == "int":
            if not _is_int(value) or not self.lo <= value <= self.hi:
                raise ModelError(f"{name} must be an int in [{self.lo}, {self.hi}], got {value!r}")
        elif self.kind == "enum":
            if value not in self.symbols:
                raise ModelError(f"{name} must be one of {self.symbols}, got {value!r}")
        else:
            raise ModelError(f"{name} has unsupported domain kind {self.kind!r}")

    def values(self) -> list[Any]:
        if self.kind == "bool":
            return [False, True]
        if self.kind == "int":
            return list(range(self.lo, self.hi + 1))
        return list(self.symbols)


class BoundedModel:
    """Executable bounded model: the YAML interpreted by a strict evaluator."""

    def __init__(self, doc: dict[str, Any]) -> None:
        self.doc = doc
        self.enums = {item["id"]: tuple(item["type"]["symbols"]) for item in doc["types"]}
        self.state_vars = tuple(item["id"] for item in doc["state_vars"])
        self.domains = {item["id"]: self._domain(item["type"]) for item in doc["state_vars"]}
        self.roles = {item["id"]: item["role"] for item in doc["state_vars"]}
        self.init_exprs = {item["var"]: _compile(item["expr"]) for item in doc["init"]}
        self.invariants = tuple((item["id"], _compile(item["expr"])) for item in doc["invariants"])
        actions = doc["actions"]
        if len(actions) != 1:
            raise ModelError("the structural core is one total step action")
        action = actions[0]
        self.action_id = str(action["id"])
        self.param_domains = {item["id"]: self._domain(item["type"]) for item in action["params"]}
        self.guard = _compile(action["guard"])
        self.updates = tuple((item["var"], _compile(item["expr"])) for item in action["updates"])
        self.effects = tuple((name, _compile(expr)) for name, expr in action["effects"].items())

    def _domain(self, node: dict[str, Any]) -> Domain:
        if "ref" in node:
            return Domain("enum", symbols=self.enums[node["ref"]])
        kind = node["kind"]
        if kind == "int":
            return Domain("int", int(node["min"]), int(node["max"]))
        if kind == "bool":
            return Domain("bool")
        if kind == "enum":
            return Domain("enum", symbols=tuple(node["symbols"]))
        raise ModelError(f"unsupported type {node!r}")

    def init_state(self) -> dict[str, Any]:
        state = {name: fn({}, {}, {}) for name, fn in self.init_exprs.items()}
        self.check_state(state)
        return state

    def check_state(self, state: dict[str, Any]) -> None:
        if set(state) != set(self.state_vars):
            raise ModelError("state does not bind exactly the declared state vars")
        for name, domain in self.domains.items():
            domain.check(state[name], name)

    def check_params(self, params: dict[str, Any]) -> None:
        if set(params) != set(self.param_domains):
            raise ModelError("params do not bind exactly the declared parameters")
        for name, domain in self.param_domains.items():
            domain.check(params[name], name)

    def step(self, state: dict[str, Any], params: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
        self.check_state(state)
        self.check_params(params)
        memo: dict[int, Any] = {}
        if self.guard(state, params, memo) is not True:
            raise ModelError("guard failed for the total step action")
        post = dict(state)
        for name, fn in self.updates:
            post[name] = fn(state, params, memo)
        self.check_state(post)
        effects = {name: fn(post, params, {}) for name, fn in self.effects}
        return post, effects

    def failing_invariants(self, state: dict[str, Any]) -> list[str]:
        failing = []
        for name, fn in self.invariants:
            if _bools([fn(state, {}, {})], name)[0] is not True:
                failing.append(name)
        return failing


def _load_doc() -> dict[str, Any]:
    doc = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    assert isinstance(doc, dict)
    return doc


@pytest.fixture(scope="module")
def doc() -> dict[str, Any]:
    return _load_doc()


@pytest.fixture(scope="module")
def model(doc: dict[str, Any]) -> BoundedModel:
    return BoundedModel(doc)


# --------------------------------------------------------------------------- #
# Helpers shared by scenarios, sweeps, and mutants.
# --------------------------------------------------------------------------- #


def owned(state: dict[str, Any], asset: str) -> int:
    return sum(int(state[f"{name}_{asset}"]) for name in PARTITIONS)


def root(state: dict[str, Any], asset: str) -> int:
    """Mixed-radix (base 5) image of the six asset quantities, as in the model."""

    return sum(int(state[f"{name}_{asset}"]) * 5**i for i, name in enumerate((*PARTITIONS, "supply")))


def make_state(model: BoundedModel, **overrides: Any) -> dict[str, Any]:
    state = model.init_state()
    unknown = set(overrides) - set(state)
    if unknown:
        raise ModelError(f"unknown state overrides {sorted(unknown)}")
    state.update(overrides)
    model.check_state(state)
    return state


def command(state: dict[str, Any], kind: int, **overrides: Any) -> dict[str, Any]:
    fresh = next((i for i in range(3) if state[f"consumed_{i}"] is False), 0)
    params: dict[str, Any] = {
        "command_kind": kind,
        "asset": ASSET_A,
        "lane_index": 0,
        "bound_height": state["height"],
        "occurrence": fresh,
        "amount": 1,
        "fee_charged": 0,
        "fee_alloc": 0,
        "authority_ok": True,
    }
    unknown = set(overrides) - set(params)
    if unknown:
        raise ModelError(f"unknown command overrides {sorted(unknown)}")
    params.update(overrides)
    return params


def spec_failures(
    pre: dict[str, Any],
    params: dict[str, Any],
    post: dict[str, Any],
    effects: dict[str, Any],
) -> list[str]:
    """Direct specification checks that do not depend on the YAML invariants."""

    failures: list[str] = []
    decision = post["g_decision"]
    if decision not in {"DEC_ACCEPTED", "DEC_REJECTED"}:
        return [f"totality:{decision}"]
    accepted = decision == "DEC_ACCEPTED"
    if effects["accepted"] is not accepted:
        failures.append("effects.accepted disagrees with the decision")
    if not accepted:
        for name in OBSERVED:
            if post[name] != pre[name]:
                failures.append(f"reject mutated {name}")
        for asset in ("a", "b"):
            for row in ROWS:
                if post[f"g_{row}_{asset}"] != 0:
                    failures.append(f"reject emitted row {row}_{asset}")
        if post["g_reject_code"] == "RC_NONE":
            failures.append("reject without a reject code")
        return failures
    if post["g_reject_code"] != "RC_NONE":
        failures.append("accept carries a reject code")
    if post["height"] != pre["height"] + 1:
        failures.append("accept did not advance height by one")
    for i in range(3):
        expected = pre[f"consumed_{i}"] or params["occurrence"] == i
        if post[f"consumed_{i}"] is not expected:
            failures.append(f"consumed_{i} is not the exact union with the occurrence")
    if pre[f"consumed_{params['occurrence']}"]:
        failures.append("accepted a consumed occurrence")
    touched = "a" if params["asset"] == ASSET_A else "b"
    for asset in ("a", "b"):
        issue = post[f"g_issue_{asset}"]
        burn = post[f"g_burn_{asset}"]
        fee_charged = post[f"g_fee_charged_{asset}"]
        fee_alloc = post[f"g_fee_alloc_{asset}"]
        fee_residue = post[f"g_fee_residue_{asset}"]
        if owned(post, asset) != owned(pre, asset) + issue - burn:
            failures.append(f"owned_{asset} conservation")
        if post[f"supply_{asset}"] != pre[f"supply_{asset}"] + issue - burn:
            failures.append(f"supply_{asset} conservation")
        if fee_charged != fee_alloc + fee_residue:
            failures.append(f"fee_{asset} reconciliation")
        if asset != touched:
            if (issue, burn, fee_charged, fee_alloc, fee_residue) != (0, 0, 0, 0, 0):
                failures.append(f"untouched asset {asset} has rows")
            for name in PARTITIONS:
                if post[f"{name}_{asset}"] != pre[f"{name}_{asset}"]:
                    failures.append(f"untouched partition {name}_{asset} moved")
            continue
        kind = params["command_kind"]
        if issue != (params["amount"] if kind == KIND_ISSUE else 0):
            failures.append("issue row is not the explicit issued amount")
        if burn != (params["amount"] if kind == KIND_BURN else 0):
            failures.append("burn row is not the explicit burned amount")
        if (fee_charged, fee_alloc) != (params["fee_charged"], params["fee_alloc"]):
            failures.append("fee row does not match the charged and allocated atoms")
        if fee_residue != params["fee_charged"] - params["fee_alloc"]:
            failures.append("carried residue is not the exact remainder")
    return failures


def check_step(
    model: BoundedModel,
    pre: dict[str, Any],
    params: dict[str, Any],
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, list[str]]:
    """Step and return (post, effects, failures) with invariant and spec failures."""

    try:
        post, effects = model.step(pre, params)
    except ModelError as exc:
        return None, None, [f"domain:{exc}"]
    failures = [f"invariant:{name}" for name in model.failing_invariants(post)]
    failures.extend(spec_failures(pre, params, post, effects))
    return post, effects, failures


def compositions(total: int, parts: int) -> Iterator[tuple[int, ...]]:
    if parts == 1:
        yield (total,)
        return
    for head in range(total + 1):
        for tail in compositions(total - head, parts - 1):
            yield (head, *tail)


def asset_states(max_supply: int) -> list[tuple[int, ...]]:
    """Every partition of ``supply`` atoms over the five buckets, supply <= max."""

    states = []
    for supply in range(max_supply + 1):
        for parts in compositions(supply, len(PARTITIONS)):
            states.append((*parts, supply))
    return states


B_FIXTURES = ((0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 1), (0, 1, 1, 1, 0, 3))


def bind_asset(state: dict[str, Any], asset: str, values: tuple[int, ...]) -> None:
    for name, value in zip((*PARTITIONS, "supply"), values, strict=True):
        state[f"{name}_{asset}"] = value


def accept_box(model: BoundedModel) -> Iterator[tuple[dict[str, Any], dict[str, Any]]]:
    """Exhaustive box: current context, every kind/asset, amounts and fees 0..2."""

    base = model.init_state()
    for a_values in asset_states(2):
        for b_values in B_FIXTURES:
            state = dict(base)
            bind_asset(state, "a", a_values)
            bind_asset(state, "b", b_values)
            for kind, asset in itertools.product(range(KIND_DRAIN + 1), (ASSET_A, ASSET_B)):
                for amount, fee_charged, fee_alloc in itertools.product(range(3), repeat=3):
                    params = command(
                        state,
                        kind,
                        asset=asset,
                        amount=amount,
                        fee_charged=fee_charged,
                        fee_alloc=fee_alloc,
                    )
                    yield state, params


def random_box(
    model: BoundedModel,
    *,
    seed: int,
    samples: int,
) -> Iterator[tuple[dict[str, Any], dict[str, Any]]]:
    """Deterministic pseudo-random box over the full declared domain."""

    rng = random.Random(seed)
    cap = model.domains["supply_a"].hi
    base = model.init_state()
    for _ in range(samples):
        state = dict(base)
        for asset in ("a", "b"):
            supply = rng.randint(0, cap)
            cuts = sorted(rng.randint(0, supply) for _ in range(len(PARTITIONS) - 1))
            bounds = [0, *cuts, supply]
            parts = tuple(bounds[i + 1] - bounds[i] for i in range(len(PARTITIONS)))
            bind_asset(state, asset, (*parts, supply))
        state["height"] = rng.randint(0, model.domains["height"].hi)
        for i in range(3):
            state[f"consumed_{i}"] = rng.random() < 0.5
        params = {name: rng.choice(domain.values()) for name, domain in model.param_domains.items()}
        yield state, params


def violations(
    model: BoundedModel,
    box: Iterator[tuple[dict[str, Any], dict[str, Any]]],
    *,
    limit: int,
) -> list[dict[str, Any]]:
    found: list[dict[str, Any]] = []
    steps = 0
    for pre, params in box:
        steps += 1
        post, effects, failures = check_step(model, pre, params)
        if failures:
            found.append({"pre": pre, "params": params, "post": post, "failures": failures})
            if len(found) >= limit:
                break
    assert steps > 0, "empty box"
    return found


# --------------------------------------------------------------------------- #
# Semantic mutants (structure-preserving single-defect edits of the YAML).
# --------------------------------------------------------------------------- #


def _var(name: str) -> dict[str, Any]:
    return {"var": name}


def _param(name: str) -> dict[str, Any]:
    return {"param": name}


def _const(value: int) -> dict[str, Any]:
    return {"const": value}


def _op(op: str, *args: dict[str, Any]) -> dict[str, Any]:
    return {"op": op, "args": list(args)}


def _ite(cond: dict[str, Any], then: dict[str, Any], other: dict[str, Any]) -> dict[str, Any]:
    return {"op": "ite", "cond": cond, "then": then, "else": other}


def _update(doc: dict[str, Any], var: str) -> dict[str, Any]:
    for item in doc["actions"][0]["updates"]:
        if item["var"] == var:
            return item
    raise KeyError(var)


def _is_kind(kind: int) -> dict[str, Any]:
    return _op("=", _param("command_kind"), _const(kind))


def _is_asset(asset: int) -> dict[str, Any]:
    return _op("=", _param("asset"), _const(asset))


def _accept(doc: dict[str, Any]) -> dict[str, Any]:
    return _update(doc, "g_decision")["expr"]["cond"]


def mutant_cross_asset_scalar_sum(doc: dict[str, Any]) -> None:
    """Issue of asset a credits the supply of asset b.

    The cross-asset scalar identity owned_a + owned_b = supply_a + supply_b still
    holds, so a scalar summation cannot reveal the defect; only the per-asset
    equations do.
    """

    touch_a = _op("and", _accept(doc), _is_asset(ASSET_A))
    _update(doc, "supply_a")["expr"]["then"] = _op(
        "+",
        _var("supply_a"),
        _ite(_is_kind(KIND_BURN), _op("-", _const(0), _param("amount")), _const(0)),
    )
    _update(doc, "supply_b")["expr"]["else"] = _op(
        "+",
        _var("supply_b"),
        _ite(_op("and", touch_a, _is_kind(KIND_ISSUE)), _param("amount"), _const(0)),
    )


def mutant_omitted_burn(doc: dict[str, Any]) -> None:
    """Burn debits holdings but the supply decrement is omitted (implicit burn)."""

    _update(doc, "supply_a")["expr"]["then"] = _op(
        "+",
        _var("supply_a"),
        _ite(_is_kind(KIND_ISSUE), _param("amount"), _const(0)),
    )


def mutant_omitted_burn_row(doc: dict[str, Any]) -> None:
    """Holdings and supply decrease on burn but the explicit BURN row is omitted."""

    _update(doc, "g_burn_a")["expr"] = _const(0)


def mutant_omitted_residue(doc: dict[str, Any]) -> None:
    """The unallocated fee remainder is neither allocated nor carried: atoms vanish."""

    _update(doc, "fee_residue_a")["expr"]["then"] = _var("fee_residue_a")


def mutant_omitted_residue_row(doc: dict[str, Any]) -> None:
    """Residue atoms reach the residue accounting location but the fee row omits them."""

    _update(doc, "g_fee_residue_a")["expr"] = _const(0)


def mutant_reject_with_effects(doc: dict[str, Any]) -> None:
    """A rejected step still moves the fee from the payer into the fee-allocation location.

    Holdings and supply stay equal, so conservation alone cannot reveal it; the
    exact pre-root no-op invariant does.
    """

    fee = _ite(_is_asset(ASSET_A), _param("fee_charged"), _const(0))
    _update(doc, "payer_a")["expr"]["else"] = _op("-", _var("payer_a"), fee)
    _update(doc, "fee_alloc_a")["expr"]["else"] = _op("+", _var("fee_alloc_a"), fee)


MUTANTS: dict[str, Callable[[dict[str, Any]], None]] = {
    "MUT_CROSS_ASSET_SCALAR_SUM": mutant_cross_asset_scalar_sum,
    "MUT_OMITTED_BURN": mutant_omitted_burn,
    "MUT_OMITTED_BURN_ROW": mutant_omitted_burn_row,
    "MUT_OMITTED_RESIDUE": mutant_omitted_residue,
    "MUT_OMITTED_RESIDUE_ROW": mutant_omitted_residue_row,
    "MUT_REJECT_WITH_EFFECTS": mutant_reject_with_effects,
}


def mutant_model(doc: dict[str, Any], name: str) -> BoundedModel:
    mutated = copy.deepcopy(doc)
    MUTANTS[name](mutated)
    return BoundedModel(mutated)


def ripr(
    honest: BoundedModel,
    mutant: BoundedModel,
    pre: dict[str, Any],
    params: dict[str, Any],
    *,
    revealed_by: set[str],
) -> dict[str, Any]:
    """Assert reach, infect, propagate, and reveal for one minimal witness."""

    honest_post, _, honest_failures = check_step(honest, pre, params)
    assert honest_failures == [], honest_failures
    mutant_post, _, mutant_failures = check_step(mutant, pre, params)
    assert mutant_post is not None, mutant_failures
    infected = {name for name in honest_post if honest_post[name] != mutant_post[name]}
    assert infected, "the mutant did not infect the post-state on the witness"
    assert revealed_by <= set(mutant_failures), (revealed_by, mutant_failures)
    return mutant_post


# --------------------------------------------------------------------------- #
# Structure and source pins.
# --------------------------------------------------------------------------- #


def test_model_declares_exactly_the_twelve_stable_lane_ids_in_canonical_order(
    model: BoundedModel,
) -> None:
    from src.core.global_settlement_types_v1 import ALL_LANE_IDS_V1

    # Arrange
    expected = tuple(lane.value for lane in ALL_LANE_IDS_V1)

    # Act
    declared = model.enums["LaneId"]

    # Assert
    assert len(expected) == 12
    assert declared == expected
    assert model.param_domains["lane_index"].hi == 12, "index 12 is the only unregistered lane"
    assert model.domains["g_lane"].symbols == expected


def test_model_is_one_total_deterministic_step_action(doc: dict[str, Any], model: BoundedModel) -> None:
    assert doc["ir_version"] == "esso-ir/v1"
    assert doc["meta"]["model_id"] == "global_settlement_core_v1"
    assert model.action_id == "step"
    assert doc["actions"][0]["guard"] == {"bool": True}
    assert set(model.param_domains) == {
        "command_kind",
        "asset",
        "lane_index",
        "bound_height",
        "occurrence",
        "amount",
        "fee_charged",
        "fee_alloc",
        "authority_ok",
    }
    assert model.enums["RejectCode"] == ("RC_NONE", *REJECT_CODES)
    assert tuple(name for name, _ in model.invariants) == INVARIANT_IDS
    assert all(item["kind"] == "safety" for item in doc["invariants"])


def test_every_state_var_is_initialised_observed_and_updated_consistently(
    doc: dict[str, Any], model: BoundedModel
) -> None:
    updates = [item["var"] for item in doc["actions"][0]["updates"]]
    inits = [item["var"] for item in doc["init"]]
    assert sorted(inits) == sorted(model.state_vars)
    assert len(inits) == len(set(inits))
    assert sorted(updates) == sorted(model.state_vars), "every state var has exactly one update"
    assert tuple(doc["observables"]["state_vars"]) == model.state_vars
    assert tuple(doc["observables"]["effects"]) == tuple(name for name, _ in model.effects)
    assert set(OBSERVED) <= set(model.state_vars)
    assert all(model.roles[name] == "data" for name in CORE_A + CORE_B)


def _referenced_vars(node: Any, found: set[str]) -> None:
    if isinstance(node, dict):
        if "var" in node:
            found.add(str(node["var"]))
        for value in node.values():
            _referenced_vars(value, found)
    elif isinstance(node, list):
        for value in node:
            _referenced_vars(value, found)


def test_ghost_journal_is_write_only_for_the_transition(doc: dict[str, Any]) -> None:
    for item in doc["actions"][0]["updates"]:
        found: set[str] = set()
        _referenced_vars(item["expr"], found)
        ghosts = {name for name in found if name.startswith("g_")}
        allowed = {"g_lane"} if item["var"] == "g_lane" else set()
        assert ghosts <= allowed, (item["var"], ghosts)


def test_blueprint_pins_base_commit_and_semantic_source_hashes() -> None:
    text = BLUEPRINT.read_text(encoding="utf-8")
    assert BASE_COMMIT in text and INITIAL_CANDIDATE_COMMIT in text
    assert TYPES_SOURCE.as_posix().endswith(next(iter(ENFORCED_PINS)))
    for relative, expected in ENFORCED_PINS.items():
        row = re.search(r"`" + re.escape(relative) + r"`[^|\n]*\|\s*`([0-9a-f]{64})`", text)
        assert row is not None, f"blueprint must pin {relative}"
        assert row.group(1) == expected, (relative, "blueprint pin differs from the test pin")
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        assert actual == expected, (
            relative,
            "semantic source drift: re-review FORMAL-MODEL-001 before trusting the blueprint",
        )
    assert "tests/formal/test_esso_global_settlement_core_v1.py" in text


def test_blueprint_names_every_lane_invariant_reject_code_and_mutant(model: BoundedModel) -> None:
    text = BLUEPRINT.read_text(encoding="utf-8")
    for lane in model.enums["LaneId"]:
        assert lane in text
    for invariant in INVARIANT_IDS:
        assert invariant in text
    for code in REJECT_CODES:
        assert code in text
    for mutant in MUTANTS:
        assert mutant in text
    assert "INCOMPLETE" in text and "ESSO" in text


def _durable_texts() -> dict[str, str]:
    return {
        "blueprint": BLUEPRINT.read_text(encoding="utf-8"),
        "model": MODEL.read_text(encoding="utf-8"),
        "tests": Path(__file__).read_text(encoding="utf-8"),
    }


def _prose(body: str) -> str:
    """Collapse line wrapping so multi-word phrases match across line breaks."""

    return " ".join(body.split())


def test_blueprint_records_the_durable_status_and_no_authority() -> None:
    text = BLUEPRINT.read_text(encoding="utf-8")
    status_line = next(line for line in text.splitlines() if line.startswith("Status:"))
    assert "RESEARCH_ONLY_UNMOUNTED" in status_line and DURABLE_STATUS in status_line
    assert RETIRED_STATUS not in text
    for authority in ("Production", "Settlement", "Release", "Value-moving"):
        assert f"{authority} authority: `NONE`" in text, authority
    assert "external to this checkout" in _prose(text) and "/path/to/ESSO" in text
    machine_specific = "/" + "home/"
    for name, body in _durable_texts().items():
        assert machine_specific not in body, name


def test_blueprint_records_the_exact_esso_replay_facts() -> None:
    text = BLUEPRINT.read_text(encoding="utf-8")
    facts = (
        RECORDED_IR_HASH,
        REVIEW_IR_HASH,
        RECORDED_FINGERPRINT,
        RECORDED_ESSO_CODE_HASH,
        *sorted(RECORDED_OBLIGATIONS),
        "Inductive(k=1)",
    )
    for fact in facts:
        assert fact in text, fact
    assert RECORDED_IR_HASH not in MODEL.read_text(encoding="utf-8"), (
        "the IR hash covers the model file and must never be recorded inside it"
    )


def test_durable_artifacts_use_legally_neutral_accounting_language() -> None:
    word = "cust" + "ody"
    forbidden = (
        f"named {word}",
        f"{word} holding",
        f"{word} backing",
        f"in {word}",
        f"takes {word}",
        f"has {word}",
        "cust" + "odied",
        "cust" + "odial",
        "cust" + "odian",
    )
    texts = {name: _prose(body) for name, body in _durable_texts().items()}
    for name, body in texts.items():
        # Serialized ABI identifiers and code spans may be quoted as field names only.
        prose = re.sub(r"`[^`]*`", "", body).lower()
        hits = [phrase for phrase in forbidden if phrase in prose]
        assert hits == [], (name, hits)
    for name in ("blueprint", "model"):
        assert "Practical custody follows key control" in texts[name], name
        assert "no custody or title claim" in texts[name], name


def test_authority_ok_is_an_abstract_authorization_premise(model: BoundedModel) -> None:
    texts = {name: _prose(body) for name, body in _durable_texts().items()}
    for name in ("blueprint", "model"):
        for phrase in ("abstract authorization premise", "not an opaque witness", "not caller authority"):
            assert phrase in texts[name], (name, phrase)
    assert model.param_domains["authority_ok"] == Domain("bool")
    # GAP-03: nothing but the bare Boolean decides authorization.
    for name, pre, params in _accept_cases(model):
        _, granted, granted_failures = check_step(model, pre, params)
        _, denied, denied_failures = check_step(model, pre, dict(params, authority_ok=False))
        assert granted_failures == [] and granted["accepted"] is True, name
        assert denied_failures == [] and denied["reject_code"] == "RC_UNAUTHORIZED", name


def test_blueprint_gap_table_lists_every_known_divergence() -> None:
    text = _prose(BLUEPRINT.read_text(encoding="utf-8"))
    for gap_id in GAP_IDS:
        assert gap_id in text, gap_id
    for phrase in (
        "route compatibility",
        "AllowedRoute",
        "unknown-asset",
        "unconstrained Boolean",
        "aggregate atoms",
        "u128",
        "epoch",
        "injective",
        "canonical runtime hash",
        "no state-bearing mapping",
        "known GAP, not a runtime-refinement pass",
        "invariant conjunction",
        "No per-invariant obligation was run",
    ):
        assert phrase in text, phrase


def test_gap_01_every_modeled_command_accepts_on_every_registered_lane(model: BoundedModel) -> None:
    lanes = model.enums["LaneId"]
    for name, pre, params in _accept_cases(model):
        for index, lane in enumerate(lanes):
            _, effects, failures = check_step(model, pre, dict(params, lane_index=index))
            assert failures == [] and effects["accepted"] is True, (name, lane)
            assert effects["lane"] == lane
        _, effects, failures = check_step(model, pre, dict(params, lane_index=len(lanes)))
        assert failures == [] and effects["reject_code"] == "RC_UNKNOWN_LANE", name


def test_gap_02_asset_domain_is_exactly_a_and_b(model: BoundedModel) -> None:
    assert model.param_domains["asset"] == Domain("int", 0, 1)
    assert not any(code.endswith("_ASSET") for code in model.enums["RejectCode"])
    assert {name[-1] for name in CORE_A + CORE_B} == {"a", "b"}


def test_gap_04_terminal_obligations_are_aggregate_atoms_only(model: BoundedModel) -> None:
    obligation_vars = [name for name in model.state_vars if "obligation" in name]
    assert obligation_vars == ["obligation_a", "obligation_b"]
    assert all(model.domains[name].kind == "int" for name in obligation_vars)
    foreign = ("claimant", "obligation_id", "release", "status", "tombstone")
    assert not any(token in name for name in model.state_vars for token in foreign)
    empty = model.init_state()
    _, missing, missing_failures = check_step(model, empty, command(empty, KIND_DRAIN, amount=1))
    assert missing_failures == [] and missing["reject_code"] == "RC_MISSING_TERMINAL_OBLIGATION"
    obliged = make_state(model, obligation_a=2, supply_a=2)
    post, partial, partial_failures = check_step(model, obliged, command(obliged, KIND_DRAIN, amount=1))
    assert partial_failures == [] and partial["accepted"] is True
    assert (post["obligation_a"], post["payer_a"]) == (1, 1), "aggregate atoms drain without object identity"


def test_gap_05_finite_widths_are_model_bounds_not_production_widths(model: BoundedModel) -> None:
    from src.core.global_settlement_types_v1 import (
        MAX_ATOMS_V1,
        MAX_DELTA_ATOMS_V1,
        MAX_EPOCH_COMMANDS_V1,
        MAX_U64_V1,
    )

    width = model.domains["supply_a"].hi
    horizon = model.domains["height"].hi
    identities = model.param_domains["occurrence"].hi + 1
    assert (width, horizon, identities) == (4, 3, 3)
    assert all(model.domains[name].hi == width for name in CORE_A + CORE_B)
    assert model.param_domains["amount"].hi == width
    assert width < MAX_DELTA_ATOMS_V1 < MAX_ATOMS_V1
    assert horizon < MAX_U64_V1 and identities < MAX_EPOCH_COMMANDS_V1


def test_gap_06_base5_pre_state_image_is_injective_only_over_the_bounded_tuple(
    model: BoundedModel,
) -> None:
    width = model.domains["supply_a"].hi
    names = tuple(f"{name}_a" for name in (*PARTITIONS, "supply"))
    images: dict[int, tuple[int, ...]] = {}
    for values in itertools.product(range(width + 1), repeat=len(names)):
        image = root(dict(zip(names, values, strict=True)), "a")
        assert image not in images, (values, images.get(image))
        images[image] = values
    assert len(images) == (width + 1) ** len(names)
    assert max(images) == model.domains["g_pre_root_a"].hi
    # One atom past the width collides with one atom in the next location, so
    # the image is not injective outside the bounded tuple and is not a hash.
    overflow = dict(zip(names, (width + 1, 0, 0, 0, 0, 0), strict=True))
    neighbour = dict(zip(names, (0, 1, 0, 0, 0, 0), strict=True))
    assert root(overflow, "a") == root(neighbour, "a")


def test_gap_07_model_accepts_carried_residue_that_source_refinement_rejects(
    model: BoundedModel,
) -> None:
    from src.core.global_economic_state_effect_refinement_v1 import _require_fee_mirror_v1
    from src.core.global_settlement_types_v1 import (
        EconomicEffectKindV1,
        EconomicEffectRowV1,
        FeeConservationRowV1,
        GlobalEconomicEffectPlanV1,
    )

    # Model side: carried residue is an accepted accounting location.
    pre = make_state(model, payer_a=2, supply_a=2)
    params = command(pre, KIND_TRANSFER, amount=1, fee_charged=1, fee_alloc=0)
    post, effects, failures = check_step(model, pre, params)
    assert failures == [] and effects["accepted"] is True
    assert post["fee_residue_a"] == 1 and effects["fee_residue_a"] == 1

    # Source side: the pinned refinement check (refinement_v1.py:249-252)
    # rejects the same nonzero residue as unmapped.  Zero residue with a
    # mirrored allocation passes the same check.
    residue_plan = GlobalEconomicEffectPlanV1(
        rows=(),
        asset_conservation=(),
        fee_conservation=(FeeConservationRowV1("A", 1, 0, 1),),
        lane_writes=(),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    with pytest.raises(ValueError, match="fee residue has no state-bearing mapping"):
        _require_fee_mirror_v1(residue_plan)
    mirrored_rows = tuple(
        EconomicEffectRowV1(kind, "fee-vault", "A", "protocol", 1)
        for kind in (EconomicEffectKindV1.ACCOUNT_MOVEMENT, EconomicEffectKindV1.FEE_ALLOCATION)
    )
    mirrored_plan = GlobalEconomicEffectPlanV1(
        rows=mirrored_rows,
        asset_conservation=(),
        fee_conservation=(FeeConservationRowV1("A", 1, 1, 0),),
        lane_writes=(),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    _require_fee_mirror_v1(mirrored_plan)


# --------------------------------------------------------------------------- #
# ESSO evidence (skipped = INCOMPLETE on this host, never a pass).
# --------------------------------------------------------------------------- #


def _esso_available() -> bool:
    if os.environ.get("ZENO_SKIP_ESSO") == "1":
        return False
    if (EXTERNAL_ESSO / "ESSO" / "__init__.py").is_file():
        return True
    return importlib.util.find_spec("ESSO") is not None


def _esso_env() -> dict[str, str]:
    env = dict(os.environ)
    if EXTERNAL_ESSO.is_dir():
        entries = [str(EXTERNAL_ESSO), env.get("PYTHONPATH", "")]
        env["PYTHONPATH"] = os.pathsep.join(entry for entry in entries if entry)
    return env


def _run_esso(*args: str, timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "ESSO", *args],
        cwd=str(ROOT),
        env=_esso_env(),
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
    )


@pytest.mark.skipif(not _esso_available(), reason=ESSO_SKIP_REASON)
def test_esso_validate_reports_ok_or_evidence_is_incomplete() -> None:
    result = _run_esso("validate", str(MODEL), timeout=120)
    assert result.returncode == 0, result.stderr or result.stdout
    payload = json.loads(result.stdout)
    assert payload["ok"] is True, payload
    assert payload["ir_hash"] == RECORDED_IR_HASH, (
        "IR hash drift: the model changed since the recorded replay; update the blueprint",
        payload,
    )


@pytest.mark.skipif(not _esso_available(), reason=ESSO_SKIP_REASON)
def test_esso_verify_multi_reports_verified_or_evidence_is_incomplete(model: BoundedModel) -> None:
    result = _run_esso(
        "verify-multi",
        str(MODEL),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "5000",
        timeout=600,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    payload = json.loads(result.stdout)
    assert payload["ok"] is True, payload
    assert payload["determinism"] is True, payload
    report = payload["report"]
    assert report["verdict"] == "VERIFIED", report
    assert report["solvers_agreed"] is True, report
    assert report["failed_queries"] == 0, report
    assert report["inconclusive_queries"] == 0, report
    assert payload["model"]["ir_hash"] == RECORDED_IR_HASH, payload["model"]
    # GAP-08: exactly two obligations over the invariant conjunction.
    queries = payload["queries"]
    assert set(queries) == set(RECORDED_OBLIGATIONS), sorted(queries)
    assert f"inductive_{model.action_id}" in queries
    for name in RECORDED_OBLIGATIONS:
        assert queries[name]["final_result"] == "unsat", (name, queries[name])
        assert queries[name]["agreed"] is True, (name, queries[name])
    scope = report["scope"]
    assert (scope["kind"], scope["k"], scope["badge"]) == ("inductive", 1, "Inductive(k=1)")
    trials = int(payload["determinism_trials"])
    fingerprints = list(payload["fingerprints"])
    assert len(fingerprints) == trials and len(set(fingerprints)) == 1, fingerprints
    if report["tool_versions"]["esso_code_hash"] == RECORDED_ESSO_CODE_HASH:
        assert fingerprints == [RECORDED_FINGERPRINT] * trials, fingerprints


# --------------------------------------------------------------------------- #
# Executable bounded model: AAA scenarios.
# --------------------------------------------------------------------------- #


def test_init_state_satisfies_every_invariant(model: BoundedModel) -> None:
    state = model.init_state()
    assert model.failing_invariants(state) == []
    assert state["g_decision"] == "DEC_GENESIS"
    assert owned(state, "a") == state["supply_a"] == 0


def test_issue_credits_holdings_and_supply_with_an_explicit_issue_row(model: BoundedModel) -> None:
    # Arrange
    pre = model.init_state()
    params = command(pre, KIND_ISSUE, amount=2, lane_index=3)

    # Act
    post, effects, failures = check_step(model, pre, params)

    # Assert
    assert failures == []
    assert effects["accepted"] is True and effects["reject_code"] == "RC_NONE"
    assert effects["command"] == "CMD_ISSUE" and effects["lane"] == "ZDEX_TOKENOMICS"
    assert post["payer_a"] == 2 and post["supply_a"] == 2 and owned(post, "a") == 2
    assert (effects["issue_a"], effects["burn_a"]) == (2, 0)
    assert post["height"] == 1 and post["consumed_0"] is True
    assert (post["g_owned_pre_a"], post["g_supply_pre_a"]) == (0, 0)


def test_transfer_fee_charged_equals_allocations_plus_carried_residue(model: BoundedModel) -> None:
    # Arrange
    pre = make_state(model, payer_a=4, supply_a=4)
    params = command(pre, KIND_TRANSFER, amount=1, fee_charged=3, fee_alloc=2)

    # Act
    post, effects, failures = check_step(model, pre, params)

    # Assert
    assert failures == []
    assert (post["payer_a"], post["rest_a"]) == (0, 1)
    assert (post["fee_alloc_a"], post["fee_residue_a"]) == (2, 1)
    assert effects["fee_charged_a"] == effects["fee_alloc_a"] + effects["fee_residue_a"] == 3
    assert owned(post, "a") == post["supply_a"] == 4, "a fee moves atoms; it never creates or destroys them"


def test_burn_debits_holdings_and_supply_with_an_explicit_burn_row(model: BoundedModel) -> None:
    # Arrange
    pre = make_state(model, payer_a=3, rest_a=1, supply_a=4)
    params = command(pre, KIND_BURN, amount=3)

    # Act
    post, effects, failures = check_step(model, pre, params)

    # Assert
    assert failures == []
    assert (post["payer_a"], post["supply_a"], owned(post, "a")) == (0, 1, 1)
    assert (effects["issue_a"], effects["burn_a"]) == (0, 3)
    assert post["supply_a"] == post["g_supply_pre_a"] + effects["issue_a"] - effects["burn_a"]


def test_open_then_drain_terminal_obligation_conserves_holdings(model: BoundedModel) -> None:
    # Arrange
    pre = make_state(model, payer_a=2, supply_a=2)

    # Act
    opened, open_effects, open_failures = check_step(model, pre, command(pre, KIND_OPEN, amount=2))
    drained, drain_effects, drain_failures = check_step(
        model, opened, command(opened, KIND_DRAIN, amount=2, lane_index=5)
    )

    # Assert
    assert open_failures == [] and drain_failures == []
    assert (opened["payer_a"], opened["obligation_a"]) == (0, 2)
    assert (drained["payer_a"], drained["obligation_a"]) == (2, 0)
    assert open_effects["lane"] == "ASSET_TRANSFER" and drain_effects["lane"] == "PERPS_MARKET"
    assert owned(pre, "a") == owned(opened, "a") == owned(drained, "a") == 2
    assert drained["height"] == 2 and drained["consumed_0"] and drained["consumed_1"]


def test_commands_on_asset_b_touch_only_asset_b(model: BoundedModel) -> None:
    # Arrange
    pre = make_state(model, payer_a=1, supply_a=1, payer_b=1, supply_b=1)
    params = command(pre, KIND_ISSUE, asset=ASSET_B, amount=3)

    # Act
    post, effects, failures = check_step(model, pre, params)

    # Assert
    assert failures == []
    assert (post["payer_b"], post["supply_b"]) == (4, 4)
    assert all(post[name] == pre[name] for name in CORE_A)
    assert effects["issue_b"] == 3 and effects["issue_a"] == 0


def _reject_cases(model: BoundedModel) -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    funded = make_state(model, payer_a=2, supply_a=2)
    consumed = make_state(model, payer_a=2, supply_a=2, consumed_0=True)
    horizon = make_state(model, payer_a=2, supply_a=2, height=3)
    return [
        ("RC_UNKNOWN_LANE", funded, command(funded, KIND_TRANSFER, lane_index=12)),
        ("RC_UNKNOWN_COMMAND", funded, command(funded, KIND_UNKNOWN)),
        ("RC_DUPLICATE_OCCURRENCE", consumed, command(consumed, KIND_TRANSFER, occurrence=0)),
        ("RC_STALE_REPLAY", funded, command(funded, KIND_TRANSFER, bound_height=1)),
        ("RC_UNAUTHORIZED", funded, command(funded, KIND_ISSUE, authority_ok=False)),
        ("RC_MISSING_TERMINAL_OBLIGATION", funded, command(funded, KIND_DRAIN, amount=1)),
        ("RC_ZERO_AMOUNT", funded, command(funded, KIND_TRANSFER, amount=0)),
        ("RC_FEE_RECONCILIATION", funded, command(funded, KIND_TRANSFER, fee_charged=1, fee_alloc=2)),
        ("RC_INSUFFICIENT", funded, command(funded, KIND_BURN, amount=3)),
        ("RC_UNREPRESENTABLE", horizon, command(horizon, KIND_TRANSFER, amount=1)),
    ]


@pytest.mark.parametrize("code", REJECT_CODES)
def test_each_reject_class_is_an_exact_noop_with_empty_rows(model: BoundedModel, code: str) -> None:
    # Arrange
    cases = {name: (pre, params) for name, pre, params in _reject_cases(model)}
    pre, params = cases[code]

    # Act
    post, effects, failures = check_step(model, pre, params)

    # Assert
    assert failures == []
    assert effects["accepted"] is False and effects["reject_code"] == code
    assert {name: post[name] for name in OBSERVED} == {name: pre[name] for name in OBSERVED}
    assert all(effects[f"{row}_{asset}"] == 0 for row in ROWS for asset in ("a", "b"))
    assert post["g_decision"] == "DEC_REJECTED"
    assert post["g_pre_root_a"] == root(pre, "a") == root(post, "a")
    assert post["g_pre_root_b"] == root(pre, "b") == root(post, "b")


def test_reject_priority_is_stable_when_several_conditions_fail(model: BoundedModel) -> None:
    # Arrange: unknown lane, unknown command, consumed occurrence, stale height,
    # missing authority, missing obligation, zero amount, and an unreconciled
    # fee all fail together.
    pre = make_state(model, payer_a=1, supply_a=1, consumed_0=True, height=1)
    worst = command(
        pre,
        KIND_UNKNOWN,
        lane_index=12,
        occurrence=0,
        bound_height=0,
        authority_ok=False,
        amount=0,
        fee_charged=0,
        fee_alloc=1,
    )
    expected_order = [
        ("lane_index", 0, "RC_UNKNOWN_LANE"),
        ("command_kind", KIND_DRAIN, "RC_UNKNOWN_COMMAND"),
        ("occurrence", 1, "RC_DUPLICATE_OCCURRENCE"),
        ("bound_height", 1, "RC_STALE_REPLAY"),
        ("authority_ok", True, "RC_UNAUTHORIZED"),
        ("command_kind", KIND_TRANSFER, "RC_MISSING_TERMINAL_OBLIGATION"),
        ("amount", 1, "RC_ZERO_AMOUNT"),
        ("fee_alloc", 0, "RC_FEE_RECONCILIATION"),
    ]

    # Act / Assert: repairing the highest-priority failure exposes the next one,
    # and repairing the last one yields acceptance.
    params = dict(worst)
    for field, repaired, code in expected_order:
        _, effects, failures = check_step(model, pre, params)
        assert failures == [] and effects["reject_code"] == code, (field, effects)
        params[field] = repaired
    post, effects, failures = check_step(model, pre, params)
    assert failures == [] and effects["accepted"] is True
    assert (post["payer_a"], post["rest_a"], post["height"]) == (0, 1, 2)


# --------------------------------------------------------------------------- #
# Boundary-value analysis.
# --------------------------------------------------------------------------- #


def test_bva_amount_zero_rejects_and_one_atom_accepts(model: BoundedModel) -> None:
    pre = make_state(model, payer_a=1, supply_a=1)
    _, zero, zero_failures = check_step(model, pre, command(pre, KIND_TRANSFER, amount=0))
    post, one, one_failures = check_step(model, pre, command(pre, KIND_TRANSFER, amount=1))
    assert zero_failures == [] and zero["reject_code"] == "RC_ZERO_AMOUNT"
    assert one_failures == [] and one["accepted"] is True
    assert (post["payer_a"], post["rest_a"]) == (0, 1)


def test_bva_payer_balance_at_exact_boundary_and_one_atom_short(model: BoundedModel) -> None:
    exact = make_state(model, payer_a=3, supply_a=3)
    short = make_state(model, payer_a=2, rest_a=1, supply_a=3)
    params = {"amount": 2, "fee_charged": 1, "fee_alloc": 1}
    post, ok, ok_failures = check_step(model, exact, command(exact, KIND_TRANSFER, **params))
    _, no, no_failures = check_step(model, short, command(short, KIND_TRANSFER, **params))
    assert ok_failures == [] and ok["accepted"] is True and post["payer_a"] == 0
    assert no_failures == [] and no["reject_code"] == "RC_INSUFFICIENT"


def test_bva_maximum_neighbour_accepts_and_overflow_rejects(model: BoundedModel) -> None:
    cap = model.domains["supply_a"].hi
    neighbour = make_state(model, payer_a=cap - 1, supply_a=cap - 1)
    full = make_state(model, payer_a=cap, supply_a=cap)
    post, ok, ok_failures = check_step(model, neighbour, command(neighbour, KIND_ISSUE, amount=1))
    _, no, no_failures = check_step(model, full, command(full, KIND_ISSUE, amount=1))
    assert ok_failures == [] and ok["accepted"] is True and post["supply_a"] == cap
    assert no_failures == [] and no["reject_code"] == "RC_UNREPRESENTABLE"


def test_bva_rest_partition_reaches_the_width_exactly(model: BoundedModel) -> None:
    cap = model.domains["rest_a"].hi
    pre = make_state(model, payer_a=1, rest_a=cap - 1, supply_a=cap)
    post, ok, ok_failures = check_step(model, pre, command(pre, KIND_TRANSFER, amount=1))
    _, no, no_failures = check_step(model, pre, command(pre, KIND_TRANSFER, amount=2))
    assert ok_failures == [] and ok["accepted"] is True
    assert (post["payer_a"], post["rest_a"]) == (0, cap)
    assert no_failures == [] and no["reject_code"] == "RC_INSUFFICIENT"


def test_bva_height_horizon_neighbour_accepts_and_horizon_rejects(model: BoundedModel) -> None:
    horizon = model.domains["height"].hi
    below = make_state(model, payer_a=1, supply_a=1, height=horizon - 1)
    at = make_state(model, payer_a=1, supply_a=1, height=horizon)
    post, ok, ok_failures = check_step(model, below, command(below, KIND_TRANSFER))
    _, no, no_failures = check_step(model, at, command(at, KIND_TRANSFER))
    assert ok_failures == [] and ok["accepted"] is True and post["height"] == horizon
    assert no_failures == [] and no["reject_code"] == "RC_UNREPRESENTABLE"


def test_bva_duplicate_occurrence_and_last_fresh_identity(model: BoundedModel) -> None:
    pre = make_state(model, payer_a=1, supply_a=1, consumed_0=True, consumed_1=True)
    _, duplicate, dup_failures = check_step(model, pre, command(pre, KIND_TRANSFER, occurrence=1))
    post, fresh, fresh_failures = check_step(model, pre, command(pre, KIND_TRANSFER, occurrence=2))
    assert dup_failures == [] and duplicate["reject_code"] == "RC_DUPLICATE_OCCURRENCE"
    assert fresh_failures == [] and fresh["accepted"] is True and post["consumed_2"] is True
    again, replay, replay_failures = check_step(model, post, command(post, KIND_TRANSFER, occurrence=2))
    assert replay_failures == [] and replay["reject_code"] == "RC_DUPLICATE_OCCURRENCE"
    assert again is not None and {n: again[n] for n in OBSERVED} == {n: post[n] for n in OBSERVED}


def test_bva_stale_replay_identity_in_both_directions(model: BoundedModel) -> None:
    pre = make_state(model, payer_a=1, supply_a=1, height=1)
    _, behind, behind_failures = check_step(model, pre, command(pre, KIND_TRANSFER, bound_height=0))
    _, ahead, ahead_failures = check_step(model, pre, command(pre, KIND_TRANSFER, bound_height=2))
    _, current, current_failures = check_step(model, pre, command(pre, KIND_TRANSFER, bound_height=1))
    assert behind_failures == [] and behind["reject_code"] == "RC_STALE_REPLAY"
    assert ahead_failures == [] and ahead["reject_code"] == "RC_STALE_REPLAY"
    assert current_failures == [] and current["accepted"] is True


# --------------------------------------------------------------------------- #
# Sequential composition, sweeps, liveness, determinism.
# --------------------------------------------------------------------------- #


def test_sequential_composition_preserves_per_asset_equations(model: BoundedModel) -> None:
    # Arrange
    state = model.init_state()
    totals = {asset: dict.fromkeys(ROWS, 0) for asset in "ab"}
    start = {asset: (owned(state, asset), state[f"supply_{asset}"]) for asset in "ab"}
    steps = [
        lambda s: command(s, KIND_ISSUE, asset=ASSET_A, amount=4, lane_index=3),
        lambda s: command(s, KIND_TRANSFER, asset=ASSET_A, amount=1, fee_charged=2, fee_alloc=1),
        lambda s: command(s, KIND_BURN, asset=ASSET_A, amount=1, fee_charged=0),
    ]

    # Act
    for build in steps:
        params = build(state)
        post, effects, failures = check_step(model, state, params)
        assert failures == [], failures
        assert effects["accepted"] is True
        for asset in "ab":
            for row in ROWS:
                totals[asset][row] += effects[f"{row}_{asset}"]
        state = post

    # Assert: cumulative per-asset equations hold across the composed steps.
    for asset in "ab":
        owned_start, supply_start = start[asset]
        assert owned(state, asset) == owned_start + totals[asset]["issue"] - totals[asset]["burn"]
        assert state[f"supply_{asset}"] == supply_start + totals[asset]["issue"] - totals[asset]["burn"]
        assert totals[asset]["fee_charged"] == totals[asset]["fee_alloc"] + totals[asset]["fee_residue"]
    assert (state["payer_a"], state["rest_a"], state["fee_alloc_a"], state["fee_residue_a"]) == (0, 1, 1, 1)
    assert state["supply_a"] == owned(state, "a") == 3
    assert state["height"] == 3 and all(state[f"consumed_{i}"] for i in range(3))
    assert model.failing_invariants(state) == []


def test_bounded_accept_box_preserves_every_invariant_and_spec_equation(model: BoundedModel) -> None:
    found = violations(model, accept_box(model), limit=1)
    assert found == [], found[:1]


def test_bounded_random_box_is_total_and_rejects_are_exact_noops(model: BoundedModel) -> None:
    box = random_box(model, seed=20260826, samples=4000)
    found = violations(model, box, limit=1)
    assert found == [], found[:1]


def _accept_cases(model: BoundedModel) -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    funded = make_state(model, payer_a=2, supply_a=2)
    obliged = make_state(model, obligation_a=1, supply_a=1)
    return [
        ("CMD_TRANSFER", funded, command(funded, KIND_TRANSFER, amount=1)),
        ("CMD_ISSUE", funded, command(funded, KIND_ISSUE, amount=1)),
        ("CMD_BURN", funded, command(funded, KIND_BURN, amount=1)),
        ("CMD_OPEN_OBLIGATION", funded, command(funded, KIND_OPEN, amount=1)),
        ("CMD_DRAIN_OBLIGATION", obliged, command(obliged, KIND_DRAIN, amount=1)),
    ]


def test_every_command_kind_and_every_reject_class_is_reachable(model: BoundedModel) -> None:
    """Non-vacuity: the accept and reject tables are both inhabited."""

    seen_commands: set[str] = set()
    for name, pre, params in _accept_cases(model):
        _, effects, failures = check_step(model, pre, params)
        assert failures == [] and effects["accepted"] is True, (name, effects)
        assert effects["command"] == name
        seen_commands.add(effects["command"])
    seen_codes: set[str] = set()
    for name, pre, params in _reject_cases(model):
        _, effects, failures = check_step(model, pre, params)
        assert failures == [] and effects["reject_code"] == name, (name, effects)
        seen_codes.add(effects["reject_code"])
    assert seen_commands == set(model.enums["CommandKind"]) - {"CMD_UNKNOWN"}
    assert seen_codes == set(REJECT_CODES)


def test_bounded_progress_reaches_the_horizon_then_every_command_rejects_totally(
    model: BoundedModel,
) -> None:
    state = model.init_state()
    horizon = model.domains["height"].hi
    for _ in range(horizon):
        state, effects, failures = _accepted(model, state, command(state, KIND_ISSUE, amount=1))
        assert failures == [] and effects["accepted"] is True
    assert state["height"] == horizon and model.failing_invariants(state) == []
    for kind in range(KIND_UNKNOWN + 1):
        params = command(state, kind, amount=1, occurrence=0)
        post, effects, failures = check_step(model, state, params)
        assert failures == [] and effects["accepted"] is False
        assert {n: post[n] for n in OBSERVED} == {n: state[n] for n in OBSERVED}


def _accepted(
    model: BoundedModel, state: dict[str, Any], params: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any], list[str]]:
    post, effects, failures = check_step(model, state, params)
    assert post is not None and effects is not None, failures
    return post, effects, failures


def test_step_is_deterministic_for_identical_inputs(model: BoundedModel) -> None:
    pre = make_state(model, payer_a=2, supply_a=2, payer_b=1, supply_b=1, height=1)
    params = command(pre, KIND_TRANSFER, amount=1, fee_charged=1, fee_alloc=1)
    first = model.step(pre, params)
    second = model.step(dict(pre), dict(params))
    assert first == second


# --------------------------------------------------------------------------- #
# Semantic mutants with minimal counterexamples (RIPR).
# --------------------------------------------------------------------------- #


def test_mutant_cross_asset_scalar_summation_is_revealed_only_per_asset(
    doc: dict[str, Any], model: BoundedModel
) -> None:
    mutant = mutant_model(doc, "MUT_CROSS_ASSET_SCALAR_SUM")
    pre = model.init_state()
    params = command(pre, KIND_ISSUE, amount=1)
    post = ripr(
        model,
        mutant,
        pre,
        params,
        revealed_by={"invariant:inv_owned_equals_supply_a", "invariant:inv_supply_step_a"},
    )
    assert (owned(post, "a"), post["supply_a"], post["supply_b"]) == (1, 0, 1)
    scalar_identity_holds = owned(post, "a") + owned(post, "b") == post["supply_a"] + post["supply_b"]
    assert scalar_identity_holds, "a cross-asset scalar sum cannot reveal the defect"


def test_mutant_omitted_burn_breaks_supply_conservation(doc: dict[str, Any], model: BoundedModel) -> None:
    mutant = mutant_model(doc, "MUT_OMITTED_BURN")
    pre = make_state(model, payer_a=1, supply_a=1)
    params = command(pre, KIND_BURN, amount=1)
    post = ripr(
        model,
        mutant,
        pre,
        params,
        revealed_by={"invariant:inv_owned_equals_supply_a", "invariant:inv_supply_step_a"},
    )
    assert (owned(post, "a"), post["supply_a"]) == (0, 1)


def test_mutant_omitted_burn_row_breaks_the_step_equations(doc: dict[str, Any], model: BoundedModel) -> None:
    mutant = mutant_model(doc, "MUT_OMITTED_BURN_ROW")
    pre = make_state(model, payer_a=1, supply_a=1)
    params = command(pre, KIND_BURN, amount=1)
    post = ripr(
        model,
        mutant,
        pre,
        params,
        revealed_by={"invariant:inv_owned_step_a", "invariant:inv_supply_step_a"},
    )
    assert post["g_burn_a"] == 0 and owned(post, "a") == post["supply_a"] == 0


def test_mutant_omitted_residue_destroys_atoms(doc: dict[str, Any], model: BoundedModel) -> None:
    mutant = mutant_model(doc, "MUT_OMITTED_RESIDUE")
    pre = make_state(model, payer_a=2, supply_a=2)
    params = command(pre, KIND_TRANSFER, amount=1, fee_charged=1, fee_alloc=0)
    post = ripr(
        model,
        mutant,
        pre,
        params,
        revealed_by={"invariant:inv_owned_equals_supply_a", "invariant:inv_owned_step_a"},
    )
    assert (owned(post, "a"), post["supply_a"], post["fee_residue_a"]) == (1, 2, 0)
    assert post["g_fee_charged_a"] == post["g_fee_alloc_a"] + post["g_fee_residue_a"], (
        "the fee row alone still reconciles; only holdings conservation reveals the loss"
    )


def test_mutant_omitted_residue_row_breaks_fee_reconciliation(
    doc: dict[str, Any], model: BoundedModel
) -> None:
    mutant = mutant_model(doc, "MUT_OMITTED_RESIDUE_ROW")
    pre = make_state(model, payer_a=2, supply_a=2)
    params = command(pre, KIND_TRANSFER, amount=1, fee_charged=1, fee_alloc=0)
    post = ripr(model, mutant, pre, params, revealed_by={"invariant:inv_fee_step_a"})
    assert post["fee_residue_a"] == 1 and post["g_fee_residue_a"] == 0


def test_mutant_reject_with_effects_breaks_exact_noop_but_not_scalar_conservation(
    doc: dict[str, Any], model: BoundedModel
) -> None:
    mutant = mutant_model(doc, "MUT_REJECT_WITH_EFFECTS")
    pre = make_state(model, payer_a=1, supply_a=1)
    params = command(pre, KIND_TRANSFER, amount=0, fee_charged=1, fee_alloc=0)
    post = ripr(model, mutant, pre, params, revealed_by={"invariant:inv_reject_exact_noop"})
    assert post["g_decision"] == "DEC_REJECTED" and post["g_reject_code"] == "RC_ZERO_AMOUNT"
    assert (post["payer_a"], post["fee_alloc_a"]) == (0, 1)
    assert owned(post, "a") == post["supply_a"] == 1, "conservation alone cannot reveal this defect"
    assert "invariant:inv_owned_equals_supply_a" not in check_step(mutant, pre, params)[2]


def test_every_named_mutant_is_killed_by_the_bounded_accept_box(doc: dict[str, Any]) -> None:
    """The honest model survives the same box in
    ``test_bounded_accept_box_preserves_every_invariant_and_spec_equation``."""

    killed: dict[str, list[str]] = {}
    for name in MUTANTS:
        mutant = mutant_model(doc, name)
        found = violations(mutant, accept_box(mutant), limit=1)
        assert found, name
        killed[name] = sorted(found[0]["failures"])
    assert set(killed) == set(MUTANTS)
    # A kill is revealed either by a named invariant or by the post-state
    # leaving the declared domain (for example a reject that drives payer_a
    # below zero under MUT_REJECT_WITH_EFFECTS).
    revealing = ("invariant:", "domain:")
    assert all(
        any(label.startswith(revealing) for label in labels) for labels in killed.values()
    ), killed
