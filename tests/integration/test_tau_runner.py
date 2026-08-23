# [TESTER] v1

from __future__ import annotations

import os

import pytest

from src.core.cpmm import swap_exact_in
from src.integration.tau_runner import (
    build_repl_script,
    find_tau_bin,
    inline_definitions,
    normalize_spec_text,
    parse_definitions,
    run_tau_spec_steps,
    run_tau_spec_steps_with_trace,
)
from src.integration.tau_witness import (
    CPMM_V1,
    SWAP_EXACT_IN_FEE_PROOF_GATE_V1,
    SWAP_EXACT_IN_PROOF_GATE_V1,
    SWAP_EXACT_OUT_FEE_PROOF_GATE_V1,
    SWAP_EXACT_OUT_PROOF_GATE_V1,
    ZUSD_LIQUIDATION_GUARD_V3,
    ZUSD_ORACLE_COMMIT_GUARD_V3,
    ZUSD_SUPPLY_CONSERVATION_V3,
    TauSpecRef,
    build_cpmm_v1_step,
    build_swap_exact_in_fee_proof_gate_v1_step,
    build_swap_exact_in_proof_gate_v1_step,
    build_swap_exact_out_fee_proof_gate_v1_step,
    build_swap_exact_out_proof_gate_v1_step,
    build_zusd_liquidation_guard_v3_step,
    build_zusd_oracle_commit_guard_v3_step,
    build_zusd_supply_conservation_v3_step,
)


def test_normalize_spec_text_single_line_always_does_not_consume_next_line() -> None:
    spec = "always x = 1.\ny = 2\n"
    out = normalize_spec_text(spec)
    assert "always x = 1." in out
    assert "\ny = 2\n" in out


def test_normalize_spec_text_rejects_unterminated_always() -> None:
    with pytest.raises(ValueError):
        normalize_spec_text("always x = 1\ny = 2\n")


def test_build_repl_script_strips_stream_declarations_from_spec_body(tmp_path) -> None:
    spec = "\n".join(
        [
            "i1[t]:bv[16]",
            "o1[t]:bv[16]",
            "always o1[t] = 1.",
            "",
            "# some comment",
            "x = 1",
        ]
    )
    script = build_repl_script(
        spec_text=normalize_spec_text(spec),
        input_streams={"i1": "bv[16]"},
        output_streams={"o1": "bv[16]"},
        input_paths={"i1": tmp_path / "i1.in"},
        output_paths={"o1": tmp_path / "o1.out"},
        always_exprs=["o1[t] = 1"],
    )
    assert "i1[t]" not in script
    assert "o1[t]" in script  # referenced in `run (...)`


def test_inline_definitions_removes_calls_cpmm_v1() -> None:
    spec_text = normalize_spec_text(CPMM_V1.path.read_text())
    defs = parse_definitions(spec_text)
    assert "swap_constraints" in defs
    always_exprs = [line for line in spec_text.splitlines() if line.startswith("always ")]
    assert always_exprs
    expr = always_exprs[0].split("always", 1)[1].strip().removesuffix(".").strip()
    expanded = inline_definitions(expr, defs)
    assert "swap_constraints(" not in expanded
    assert "is_positive(" not in expanded


def test_run_tau_spec_steps_minimal() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    step = build_swap_exact_in_proof_gate_v1_step(
        reserve_in=1000,
        reserve_out=2000,
        amount_in=100,
        fee_bps=30,
        min_amount_out=1,
        amount_out=180,
        new_reserve_in=1100,
        new_reserve_out=1820,
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SWAP_EXACT_IN_PROOF_GATE_V1.path,
        steps=[step],
        timeout_s=20.0,
    )
    assert outputs[0]["o1"] == 1


def test_zusd_v3_boolean_guards_reject_each_false_projection() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    oracle_accept = build_zusd_oracle_commit_guard_v3_step(
        oracle_seen=1,
        pending_price_positive=1,
        pending_observation_fresh=1,
        auth_ok=1,
        commit_candidate_ok=1,
    )
    oracle_steps = [oracle_accept]
    oracle_steps.extend(
        {**oracle_accept, input_name: 0}
        for input_name in sorted(oracle_accept)
    )
    oracle_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ZUSD_ORACLE_COMMIT_GUARD_V3.path,
        steps=oracle_steps,
        timeout_s=30.0,
    )

    assert oracle_outputs[0] == {"o1": 1, "o2": 1, "o3": 1, "o4": 1}
    assert all(
        oracle_outputs[index]["o4"] == 0
        for index in range(1, len(oracle_steps))
    )

    liquidation_accept = build_zusd_liquidation_guard_v3_step(
        committed_oracle_initialized=1,
        no_uncommitted_report=1,
        committed_oracle_fresh=1,
        positive_debt=1,
        under_mcr_at_committed_price=1,
        stability_pool_can_absorb=1,
        collateral_destinations_exact=1,
        stability_pool_collateral_cap_ok=1,
        state_delta_ok=1,
    )
    liquidation_steps = [liquidation_accept]
    liquidation_steps.extend(
        {**liquidation_accept, input_name: 0}
        for input_name in sorted(liquidation_accept)
    )
    liquidation_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ZUSD_LIQUIDATION_GUARD_V3.path,
        steps=liquidation_steps,
        timeout_s=30.0,
    )

    assert liquidation_outputs[0] == {
        "o1": 1,
        "o2": 1,
        "o3": 1,
        "o4": 1,
    }
    assert all(
        liquidation_outputs[index]["o4"] == 0
        for index in range(1, len(liquidation_steps))
    )

    supply_accept = build_zusd_supply_conservation_v3_step(
        pre_conservation_ok=1,
        post_conservation_ok=1,
        transition_delta_ok=1,
    )
    supply_steps = [supply_accept]
    supply_steps.extend(
        {**supply_accept, input_name: 0}
        for input_name in sorted(supply_accept)
    )
    supply_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ZUSD_SUPPLY_CONSERVATION_V3.path,
        steps=supply_steps,
        timeout_s=30.0,
    )

    assert supply_outputs[0] == {"o1": 1, "o2": 1, "o3": 1, "o4": 1}
    assert all(
        supply_outputs[index]["o4"] == 0
        for index in range(1, len(supply_steps))
    )


@pytest.mark.parametrize(
    ("spec_ref", "steps"),
    [
        pytest.param(
            SWAP_EXACT_IN_PROOF_GATE_V1,
            [
                build_swap_exact_in_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                ),
                build_swap_exact_in_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1819,
                ),
            ],
            id="exact_in",
        ),
        pytest.param(
            SWAP_EXACT_OUT_PROOF_GATE_V1,
            [
                build_swap_exact_out_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                ),
                build_swap_exact_out_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1819,
                ),
            ],
            id="exact_out",
        ),
        pytest.param(
            SWAP_EXACT_IN_FEE_PROOF_GATE_V1,
            [
                build_swap_exact_in_fee_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                    fee_total=1,
                ),
                build_swap_exact_in_fee_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1819,
                    fee_total=1,
                ),
            ],
            id="exact_in_fee",
        ),
        pytest.param(
            SWAP_EXACT_OUT_FEE_PROOF_GATE_V1,
            [
                build_swap_exact_out_fee_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                    fee_total=1,
                ),
                build_swap_exact_out_fee_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1819,
                    fee_total=1,
                ),
            ],
            id="exact_out_fee",
        ),
    ],
)
def test_swap_proof_gates_require_reserve_transition_flag(spec_ref: TauSpecRef, steps: list[dict[str, int]]) -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_ref.path,
        steps=steps,
        timeout_s=30.0,
    )
    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 0


def test_swap_bv32_witness_builders_reject_out_of_range_values() -> None:
    with pytest.raises(ValueError, match="new_reserve_in"):
        build_swap_exact_in_proof_gate_v1_step(
            reserve_in=0xFFFFFFFF,
            reserve_out=2000,
            amount_in=1,
            fee_bps=30,
            min_amount_out=1,
            amount_out=1,
            new_reserve_in=0x100000000,
            new_reserve_out=1999,
        )

    with pytest.raises(ValueError, match="reserve_out"):
        build_swap_exact_out_proof_gate_v1_step(
            reserve_in=1000,
            reserve_out=-1,
            amount_out=1,
            fee_bps=30,
            max_amount_in=10,
            amount_in=1,
            new_reserve_in=1001,
            new_reserve_out=0,
        )


def test_run_tau_spec_steps_cpmm_v1_slow() -> None:
    if os.environ.get("TAU_SLOW_TESTS") != "1":
        pytest.skip("set TAU_SLOW_TESTS=1 to run Tau spec integration tests")

    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    reserve_in = 1_000_000
    reserve_out = 2_000_000
    amount_in = 50_000
    fee_bps = 30
    amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    assert new_reserve_in == reserve_in + amount_in
    assert new_reserve_out == reserve_out - amount_out

    step = build_cpmm_v1_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        amount_out=amount_out,
    )
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=CPMM_V1.path, steps=[step], timeout_s=60.0)
    assert outputs[0][CPMM_V1.gate_output] == 1


def test_tau_python_bindings_parity_minimal(tmp_path, monkeypatch) -> None:
    """
    If Tau Python bindings are available, they must match the subprocess runner.

    BVA notes:
    - bv[16] domain: exercise {0, 1, max-1, max}
    """
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found (need subprocess runner for parity check)")

    spec_path = tmp_path / "parity_bv16_copy.tau"
    spec_path.write_text("i1[t]:bv[16]\no1[t]:bv[16]\nalways (o1[t]:bv[16] = i1[t]:bv[16]).\n")

    steps = [{"i1": v} for v in (0, 1, 65534, 65535)]

    try:
        monkeypatch.setenv("TAU_USE_PY_BINDINGS", "1")
        out_bindings = run_tau_spec_steps(tau_bin=None, spec_path=spec_path, steps=steps, timeout_s=2.0)
    except Exception:
        pytest.skip("Tau Python bindings not available (build with -DTAU_BUILD_BINDING_PYTHON=ON)")

    out_subprocess = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=2.0)
    assert out_bindings == out_subprocess


def test_run_tau_spec_steps_falls_back_to_spec_mode_when_repl_creates_no_outputs(tmp_path, monkeypatch) -> None:
    spec_path = tmp_path / "fallback_copy.tau"
    spec_path.write_text("i1[t]:bv[16]\no1[t]:bv[16]\nalways (o1[t]:bv[16] = i1[t]:bv[16]).\n")

    fake_tau = tmp_path / "fake_tau"
    fake_tau.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    fake_tau.chmod(0o755)

    def _fake_run_subprocess_with_output_caps(*args, **kwargs):
        return 0, "", ""

    def _fake_spec_mode(**kwargs):
        return {0: {"o1": 7}}

    monkeypatch.setattr("src.integration.tau_runner._run_subprocess_with_output_caps", _fake_run_subprocess_with_output_caps)
    monkeypatch.setattr("src.integration.tau_runner.run_tau_spec_steps_spec_mode", _fake_spec_mode)

    outputs = run_tau_spec_steps(
        tau_bin=str(fake_tau),
        spec_path=spec_path,
        steps=[{"i1": 7}],
        timeout_s=2.0,
    )
    assert outputs == {0: {"o1": 7}}


def test_run_tau_spec_steps_with_trace_falls_back_to_spec_mode_when_repl_creates_no_outputs(tmp_path, monkeypatch) -> None:
    spec_path = tmp_path / "fallback_trace_copy.tau"
    spec_path.write_text("i1[t]:bv[16]\no1[t]:bv[16]\nalways (o1[t]:bv[16] = i1[t]:bv[16]).\n")

    fake_tau = tmp_path / "fake_tau"
    fake_tau.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    fake_tau.chmod(0o755)

    def _fake_run_subprocess_with_output_caps(*args, **kwargs):
        return 0, "repl-out", ""

    def _fake_spec_mode_with_trace(**kwargs):
        return ({0: {"o1": 9}}, "spec-out", "", "spec-text", "spec-input")

    monkeypatch.setattr("src.integration.tau_runner._run_subprocess_with_output_caps", _fake_run_subprocess_with_output_caps)
    monkeypatch.setattr("src.integration.tau_runner.run_tau_spec_steps_spec_mode_with_trace", _fake_spec_mode_with_trace)

    outputs, out, err, repl = run_tau_spec_steps_with_trace(
        tau_bin=str(fake_tau),
        spec_path=spec_path,
        steps=[{"i1": 9}],
        timeout_s=2.0,
    )
    assert outputs == {0: {"o1": 9}}
    assert "repl->spec fallback" in out
    assert "r (" in repl


def test_spec_mode_normalization_strips_multiline_helper_definitions(tmp_path, monkeypatch) -> None:
    spec_path = tmp_path / "multiline_defs.tau"
    spec_path.write_text(
        "\n".join(
            [
                "set charvar off",
                "helper(x : sbf, y : sbf) :=",
                "  (x = 1:sbf) ||",
                "  (y = 1:sbf).",
                "i1[t]:sbf",
                "o1[t]:sbf",
                "always (o1[t]:sbf = 1:sbf <-> helper(i1[t]:sbf, i1[t]:sbf)).",
                "",
            ]
        ),
        encoding="utf-8",
    )

    fake_tau = tmp_path / "fake_tau"
    fake_tau.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
    fake_tau.chmod(0o755)

    def _fake_run_subprocess_with_output_caps(cmd, *, input_text, cwd, timeout_s, max_stdout_bytes, max_stderr_bytes):
        return 1, "boom", "boom"

    monkeypatch.setattr("src.integration.tau_runner._run_subprocess_with_output_caps", _fake_run_subprocess_with_output_caps)

    with pytest.raises(Exception) as excinfo:
        from src.integration.tau_runner import run_tau_spec_steps_spec_mode_with_trace

        run_tau_spec_steps_spec_mode_with_trace(
            tau_bin=str(fake_tau),
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
        )

    exc = excinfo.value
    normalized = getattr(exc, "spec_text", "")
    assert "helper(x : sbf, y : sbf) :=" not in normalized
    assert "always (o1[t]:sbf = 1:sbf <->" in normalized
