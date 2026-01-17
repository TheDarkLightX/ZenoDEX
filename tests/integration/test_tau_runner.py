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
)
from src.integration.tau_witness import CPMM_V1, build_cpmm_v1_step


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


def test_run_tau_spec_steps_minimal(tmp_path) -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = tmp_path / "minimal_sbf_copy.tau"
    spec_path.write_text("i1[t]:sbf\no1[t]:sbf\nalways (o1[t]:sbf = i1[t]:sbf).\n")
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=[{"i1": 1}], timeout_s=2.0)
    assert outputs[0]["o1"] == 1


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
