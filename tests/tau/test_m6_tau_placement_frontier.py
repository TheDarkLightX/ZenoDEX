from __future__ import annotations

import os
from pathlib import Path
from typing import cast

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

ROOT = Path(__file__).resolve().parents[2]


def _tau_bin() -> str:
    tau_bin = os.environ.get("TAU_BIN", "").strip() or find_tau_bin(ROOT)
    if not isinstance(tau_bin, str) or tau_bin == "":
        pytest.skip("exact Tau binary not available")
    return cast(str, tau_bin)


def _run(spec_name: str, step: dict[str, int]) -> dict[str, int]:
    return _run_steps(spec_name, [step])[0]


def _run_steps(spec_name: str, steps: list[dict[str, int]]) -> dict[int, dict[str, int]]:
    return run_tau_spec_steps(
        _tau_bin(),
        ROOT / "src" / "tau_specs" / "recommended" / spec_name,
        steps,
        timeout_s=30.0,
    )


def _inputs(count: int, **overrides: int) -> dict[str, int]:
    values = {f"i{index}": 1 for index in range(1, count + 1)}
    values.update(overrides)
    return values


def test_writer_steady_guard_accepts_tau_and_ledger_without_crossing() -> None:
    tau = _inputs(16, i2=0, i3=0, i5=0, i6=0, i10=0)
    ledger = _inputs(16, i1=0, i3=0, i4=0, i6=0, i7=0, i10=0)
    direct_switch = _inputs(16, i2=0, i3=0, i4=0, i6=0)

    assert _run("m6_writer_steady_guard_v1.tau", tau)["o1"] == 1
    assert _run("m6_writer_steady_guard_v1.tau", ledger)["o1"] == 1
    assert _run("m6_writer_steady_guard_v1.tau", direct_switch)["o1"] == 0


def test_writer_handoff_requires_quiescence_before_activation() -> None:
    quiesce_tau = _inputs(19, i2=0, i3=0, i4=0, i5=0)
    activate_ledger = _inputs(21, i1=0, i2=0, i4=0, i6=0, i7=0)

    assert _run("m6_writer_quiesce_guard_v1.tau", quiesce_tau)["o1"] == 1
    assert _run("m6_writer_activate_guard_v1.tau", activate_ledger)["o1"] == 1
    assert _run("m6_writer_activate_guard_v1.tau", {**activate_ledger, "i3": 0})["o1"] == 0


def test_writer_emergency_failover_is_closed_and_revokes_old_writer() -> None:
    emergency = _inputs(24, i2=0, i3=0, i4=0, i6=0, i7=0)
    mutants = [
        {**emergency, "i11": 0},
        {**emergency, "i15": 0},
        {**emergency, "i21": 0},
        {**emergency, "i13": 0},
        {**emergency, "i24": 0},
    ]

    outputs = _run_steps("m6_writer_emergency_failover_guard_v1.tau", [emergency, *mutants])

    assert outputs[0]["o1"] == 1
    assert all(outputs[index]["o1"] == 0 for index in range(1, len(outputs)))


def test_writer_emergency_failover_has_no_ignored_input_bit() -> None:
    emergency = _inputs(24, i2=0, i3=0, i4=0, i6=0, i7=0)
    one_bit_mutants = [
        {**emergency, f"i{index}": 1 - emergency[f"i{index}"]}
        for index in range(1, 25)
    ]
    outputs = _run_steps(
        "m6_writer_emergency_failover_guard_v1.tau",
        [emergency, *one_bit_mutants],
    )

    assert outputs[0]["o1"] == 1
    assert all(outputs[index]["o1"] == 0 for index in range(1, len(outputs)))


def _tau_profile_base() -> dict[str, int]:
    return {
        "i1": 1,
        "i2": 0,
        "i3": 0,
        "i4": 0,
        "i5": 0,
        "i6": 0,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
        "i12": 1,
        "i13": 1,
    }


def test_tau_profile_gate_accepts_only_the_exact_verified_profile() -> None:
    verified_tau = _tau_profile_base()
    one_bit_mutants = [
        {**verified_tau, f"i{index}": 1 - verified_tau[f"i{index}"]}
        for index in range(1, 14)
    ]
    outputs = _run_steps("m6_tau_substrate_profile_gate_v1.tau", [verified_tau, *one_bit_mutants])

    assert outputs[0]["o1"] == 1
    assert all(outputs[index]["o1"] == 0 for index in range(1, len(outputs)))


def _disposition_base() -> dict[str, int]:
    return {
        "i1": 1,
        "i2": 1,
        "i3": 0,
        "i4": 0,
        "i5": 0,
        "i6": 0,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 0,
        "i11": 0,
        "i12": 1,
        "i13": 1,
        "i14": 1,
    }


def test_substrate_disposition_prefers_tau_and_degrades_independent_work() -> None:
    verified_tau = _disposition_base()
    use_ledger = {**verified_tau, "i1": 0, "i9": 0, "i10": 1}

    assert _run("m6_substrate_disposition_gate_v1.tau", verified_tau) == {"o1": 1, "o2": 1}
    assert _run("m6_substrate_disposition_gate_v1.tau", use_ledger) == {"o1": 1, "o2": 1}


def test_tau_native_asset_operation_requires_profile_or_safe_exit() -> None:
    reject_or_pend = {
        **_disposition_base(),
        "i1": 0,
        "i2": 0,
        "i4": 1,
        "i9": 0,
        "i11": 1,
    }
    safe_exit = {**reject_or_pend, "i6": 1, "i10": 1, "i11": 0}

    assert _run("m6_substrate_disposition_gate_v1.tau", reject_or_pend) == {"o1": 1, "o2": 0}
    assert _run("m6_substrate_disposition_gate_v1.tau", safe_exit) == {"o1": 1, "o2": 1}


def test_tau_dependent_operation_can_use_verified_portable_certificate() -> None:
    portable = {
        **_disposition_base(),
        "i1": 0,
        "i2": 0,
        "i3": 1,
        "i5": 1,
        "i9": 0,
        "i10": 1,
    }

    assert _run("m6_substrate_disposition_gate_v1.tau", portable) == {"o1": 1, "o2": 1}


def test_substrate_disposition_rejects_unsafe_or_nonpreferred_execution() -> None:
    tau_usable = _disposition_base()
    ledger_while_tau_usable = {**tau_usable, "i9": 0, "i10": 1}
    dependent_without_certificate = {
        **tau_usable,
        "i1": 0,
        "i2": 0,
        "i3": 1,
        "i9": 0,
        "i11": 1,
    }
    native_without_safe_exit_uses_ledger = {
        **tau_usable,
        "i1": 0,
        "i2": 0,
        "i4": 1,
        "i9": 0,
        "i10": 1,
    }
    independent_with_stale_ledger = {
        **tau_usable,
        "i1": 0,
        "i8": 0,
        "i9": 0,
        "i11": 1,
    }

    outputs = _run_steps(
        "m6_substrate_disposition_gate_v1.tau",
        [
            ledger_while_tau_usable,
            dependent_without_certificate,
            native_without_safe_exit_uses_ledger,
            independent_with_stale_ledger,
        ],
    )

    assert [outputs[index] for index in range(len(outputs))] == [
        {"o1": 0, "o2": 0},
        {"o1": 1, "o2": 0},
        {"o1": 0, "o2": 0},
        {"o1": 1, "o2": 0},
    ]


def test_profile_and_disposition_gates_reject_ambiguous_classes() -> None:
    ambiguous_observation = {**_tau_profile_base(), "i2": 1}
    ambiguous_operation = {**_disposition_base(), "i3": 1}

    assert _run("m6_tau_substrate_profile_gate_v1.tau", ambiguous_observation) == {"o1": 0}
    assert _run("m6_substrate_disposition_gate_v1.tau", ambiguous_operation) == {"o1": 0, "o2": 0}


def _global_certificate_base() -> dict[str, int]:
    return {f"i{index}": 1 for index in range(1, 22)}


def test_global_value_certificate_closure_requires_every_authority_fiber() -> None:
    complete = _global_certificate_base()
    missing_rows = [{**complete, f"i{index}": 0} for index in range(1, 20)]

    outputs = run_tau_spec_steps(
        _tau_bin(),
        ROOT / "src/tau_specs/recommended/m6_global_value_certificate_closure_v1.tau",
        [complete, *missing_rows],
        timeout_s=30.0,
    )

    assert outputs[0]["o6"] == 1
    assert all(outputs[index]["o6"] == 0 for index in range(1, len(outputs)))


def test_global_value_certificate_closure_requires_proof_and_binding() -> None:
    complete = _global_certificate_base()
    outputs = run_tau_spec_steps(
        _tau_bin(),
        ROOT / "src/tau_specs/recommended/m6_global_value_certificate_closure_v1.tau",
        [complete, {**complete, "i20": 0}, {**complete, "i21": 0}],
        timeout_s=30.0,
    )

    assert [outputs[index]["o6"] for index in range(3)] == [1, 0, 0]
