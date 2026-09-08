"""Independent obligations for environment-only common-anchor repairs."""

from __future__ import annotations

import os
import sys
from collections.abc import Callable, Mapping
from itertools import product

import pytest

from src.tau_composition.anchor import AnchorCompiler, AnchoredRepair, zero_anchor
from src.tau_composition.compiler import RepairCompiler
from src.tau_composition.examples import conditional_cycle, permission_chain
from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.terms import constant, negate, variable, xor


def _native_runtime(binary: str) -> TauRuntime:
    return TauRuntime(binary, timeout_seconds=8.0)


@pytest.fixture
def native_binary() -> str:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if binary is None:
        pytest.skip("set TAU_COMPOSITION_BIN to run native Tau common-anchor obligations")
    return binary


def _values(contract: Contract):
    names = contract.environment + contract.controls
    for bits in product((False, True), repeat=len(names)):
        yield dict(zip(names, bits, strict=True))


def _control_values(values: Mapping[str, bool], contract: Contract) -> tuple[bool, ...]:
    return tuple(values[name] for name in contract.controls)


def _environment_values(values: Mapping[str, bool], contract: Contract) -> tuple[bool, ...]:
    return tuple(values[name] for name in contract.environment)


def _assert_retraction(
    repair: AnchoredRepair, legal: Callable[[Mapping[str, bool]], bool]
) -> None:
    """Check the host retraction law without reusing Contract.satisfied."""

    expected_image: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    observed_image: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    for original in _values(repair.contract):
        environment = _environment_values(original, repair.contract)
        expected_image.setdefault(environment, set())
        observed_image.setdefault(environment, set())
        if legal(original):
            expected_image[environment].add(_control_values(original, repair.contract))

        before = dict(original)
        proposed = repair.propose(original)

        assert original == before
        assert _environment_values(proposed, repair.contract) == environment
        assert legal(proposed)
        assert repair.propose(proposed) == proposed
        if legal(original):
            assert proposed == original
        observed_image[environment].add(_control_values(proposed, repair.contract))

    assert observed_image == expected_image


def _chain_legal(values: Mapping[str, bool]) -> bool:
    bits = tuple(values[f"action{index:03d}"] for index in range(4))
    return all(not bits[index] or bits[index + 1] for index in range(len(bits) - 1))


def _conditional_cycle_legal(values: Mapping[str, bool]) -> bool:
    return values["left"] is False and values["right"] is True


def _environment_anchor_contract() -> Contract:
    mode, left, right = map(variable, ("mode", "left", "right"))
    return Contract("environment_anchor", ("mode",), ("left", "right"), (
        Requirement("left_matches_mode", xor(left, mode)),
        Requirement("right_matches_mode", xor(right, mode)),
    ))


def _environment_anchor() -> RepairMap:
    return RepairMap((("left", variable("mode")), ("right", variable("mode"))))


def _environment_anchor_legal(values: Mapping[str, bool]) -> bool:
    return values["left"] is values["mode"] and values["right"] is values["mode"]


def test_native_zero_anchor_permission_chain_is_a_cached_retraction(native_binary: str) -> None:
    contract = permission_chain(3)
    runtime = _native_runtime(native_binary)
    compiler = AnchorCompiler(runtime)

    first = compiler.compile(contract, zero_anchor(contract))
    records_after_first = len(runtime.records)
    second = compiler.compile(contract, zero_anchor(contract))

    assert tuple(name for name, _term in first.anchor.assignments) == contract.controls
    assert first.native_queries > 0
    assert first.cache_hits > 0
    assert second.native_queries == 0
    assert second.cache_hits > 0
    assert len(runtime.records) == records_after_first
    _assert_retraction(first, _chain_legal)


def test_native_conditional_cycle_constant_anchor_is_a_retraction(native_binary: str) -> None:
    contract = conditional_cycle()
    anchor = RepairMap((("left", constant(False)), ("right", constant(True))))
    repair = AnchorCompiler(_native_runtime(native_binary)).compile(contract, anchor)

    _assert_retraction(repair, _conditional_cycle_legal)


def test_native_environment_anchor_and_polynomial_map_match_host_and_tau(native_binary: str) -> None:
    contract = _environment_anchor_contract()
    runtime = _native_runtime(native_binary)
    repair = AnchorCompiler(runtime).compile(contract, _environment_anchor())
    polynomial = repair.polynomial_map()

    _assert_retraction(repair, _environment_anchor_legal)
    for values in _values(contract):
        assert polynomial.apply(values) == repair.propose(values)

    # This is a native arbitrary-Boolean-algebra check, not a host truth table.
    RepairCompiler(runtime)._check_reproductive(contract.residual, polynomial)


def test_polynomial_map_uses_or_residual_and_retains_valid_non_anchor_values() -> None:
    cycle = conditional_cycle()
    constant_anchor = RepairMap((("left", constant(False)), ("right", constant(True))))
    polynomial = AnchoredRepair(cycle, constant_anchor, 0, 0, "host-only").polynomial_map()
    simultaneous_failures = {"mode": False, "left": True, "right": False}

    assert _conditional_cycle_legal(polynomial.apply(simultaneous_failures))

    chain = permission_chain(3)
    valid_non_anchor = {name: True for name in chain.controls}
    preserved = AnchoredRepair(chain, zero_anchor(chain), 0, 0, "host-only").polynomial_map()

    assert preserved.apply(valid_non_anchor) == valid_non_anchor


def test_anchor_compiler_rejects_invalid_different_role_and_incomplete_anchors(
    native_binary: str,
) -> None:
    contract = conditional_cycle()
    runtime = _native_runtime(native_binary)
    compiler = AnchorCompiler(runtime)
    valid = RepairMap((("left", constant(False)), ("right", constant(True))))
    invalid = RepairMap((("left", constant(False)), ("right", constant(False))))

    compiler.compile(contract, valid)
    records_before_invalid = len(runtime.records)
    with pytest.raises(TauQueryError) as raised:
        compiler.compile(contract, invalid)
    assert raised.value.code == "anchor_not_valid"
    assert len(runtime.records) > records_before_invalid

    records_before_shape_rejections = len(runtime.records)
    with pytest.raises(ValueError, match="anchor_reads_non_environment"):
        compiler.compile(
            contract,
            RepairMap((("left", variable("mode")), ("right", variable("right")))),
        )
    with pytest.raises(ValueError, match="anchor_control_coverage"):
        compiler.compile(contract, RepairMap((("left", constant(False)),)))
    with pytest.raises(ValueError, match="anchor_control_coverage"):
        compiler.compile(contract, RepairMap((("right", constant(True)), ("left", constant(False)))))
    assert len(runtime.records) == records_before_shape_rejections


def test_native_anchor_reuse_rechecks_every_edited_clause(native_binary: str) -> None:
    original = _environment_anchor_contract()
    mode, right = variable("mode"), variable("right")
    edited = Contract("environment_anchor_edited", original.environment, original.controls, (
        original.requirements[0],
        Requirement("right_now_opposes_mode", xor(right, negate(mode))),
    ))
    runtime = _native_runtime(native_binary)
    compiler = AnchorCompiler(runtime)

    compiler.compile(original, _environment_anchor())
    with pytest.raises(TauQueryError) as raised:
        compiler.compile(edited, _environment_anchor())

    assert raised.value.code == "anchor_not_valid"


def test_anchor_compiler_propagates_native_unknown(monkeypatch: pytest.MonkeyPatch) -> None:
    contract = conditional_cycle()
    runtime = TauRuntime(sys.executable, timeout_seconds=1.0)

    def unknown(_query: str) -> bool:
        raise TauQueryError("native_timeout")

    monkeypatch.setattr(runtime, "valid", unknown)
    with pytest.raises(TauQueryError) as raised:
        AnchorCompiler(runtime).compile(contract, zero_anchor(contract))

    assert raised.value.code == "native_timeout"


def test_propose_rechecks_the_original_contract_after_an_unchecked_anchor() -> None:
    contract = conditional_cycle()
    unsafe = AnchoredRepair(
        contract=contract,
        anchor=RepairMap((("left", constant(False)), ("right", constant(False)))),
        native_queries=0,
        cache_hits=0,
        binary_sha256="host-only",
    )
    valid = {"mode": True, "left": False, "right": True}

    assert unsafe.propose(valid) == valid
    with pytest.raises(ValueError, match="anchored_proposal_failed_contract"):
        unsafe.propose({"mode": False, "left": True, "right": False})
