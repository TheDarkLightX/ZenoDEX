from __future__ import annotations

import pytest

from src.fire.compiler.object_compiler_v1 import (
    cap_expr,
    capped_call_expr,
    capped_index_note_expr,
    clamp_expr,
    compile_interval_expression_certificate,
    const_expr,
    exact_param_expr,
    infer_fire_expr_unit,
    lp_loss_cover_expr,
    parse_fire_unit,
    source_bound_expr,
    sub_expr,
)
from src.fire.verifier.cert_v1 import FireCertEnv, FireInterval, verify_interval_certificate


def test_compile_interval_expression_certificate_for_capped_call() -> None:
    expr = capped_call_expr(
        underlying=source_bound_expr("burn_final"),
        strike=exact_param_expr("strike_index"),
        cap=exact_param_expr("cap_index"),
        notional=exact_param_expr("n_notional"),
    )
    env = FireCertEnv(
        exact_values={"n_notional": 10, "strike_index": 4, "cap_index": 3},
        source_bounds={"burn_final": FireInterval(lower=0, upper=9)},
    )

    certificate = compile_interval_expression_certificate(expr, env)
    ok, err, interval = verify_interval_certificate(certificate, env)

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=30)


def test_compile_interval_expression_certificate_for_capped_index_note() -> None:
    expr = capped_index_note_expr(
        underlying=source_bound_expr("fee_final"),
        cap=exact_param_expr("cap_index"),
        notional=exact_param_expr("n_notional"),
    )
    env = FireCertEnv(
        exact_values={"n_notional": 10, "cap_index": 7},
        source_bounds={"fee_final": FireInterval(lower=0, upper=2)},
    )

    certificate = compile_interval_expression_certificate(expr, env)
    ok, err, interval = verify_interval_certificate(certificate, env)

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=20)


def test_compile_interval_expression_certificate_for_lp_loss_cover() -> None:
    expr = lp_loss_cover_expr(
        hodl_value=source_bound_expr("hodl_final"),
        lp_value=source_bound_expr("lpv_final"),
        deductible=exact_param_expr("deductible"),
        cap=exact_param_expr("cap_amount"),
        notional=exact_param_expr("n_notional"),
    )
    env = FireCertEnv(
        exact_values={"n_notional": 2, "deductible": 5, "cap_amount": 40},
        source_bounds={
            "hodl_final": FireInterval(lower=30, upper=80),
            "lpv_final": FireInterval(lower=10, upper=60),
        },
    )

    certificate = compile_interval_expression_certificate(expr, env)
    ok, err, interval = verify_interval_certificate(certificate, env)

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=80)


def test_clamp_expr_compiles_to_expected_interval() -> None:
    expr = clamp_expr(
        sub_expr(source_bound_expr("x"), exact_param_expr("k")),
        const_expr(0),
        exact_param_expr("cap"),
    )
    env = FireCertEnv(
        exact_values={"k": 4, "cap": 3},
        source_bounds={"x": FireInterval(lower=0, upper=9)},
    )

    certificate = compile_interval_expression_certificate(expr, env)
    ok, err, interval = verify_interval_certificate(certificate, env)

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=3)


def test_compile_interval_expression_certificate_rejects_missing_binding() -> None:
    expr = cap_expr(source_bound_expr("fee_final"), exact_param_expr("cap_index"))
    env = FireCertEnv(
        exact_values={},
        source_bounds={"fee_final": FireInterval(lower=0, upper=2)},
    )

    with pytest.raises(KeyError, match="missing exact value: cap_index"):
        compile_interval_expression_certificate(expr, env)


def test_infer_fire_expr_unit_for_burn_call_returns_amount() -> None:
    expr = capped_call_expr(
        underlying=source_bound_expr("burn_final"),
        strike=exact_param_expr("strike_index"),
        cap=exact_param_expr("cap_index"),
        notional=exact_param_expr("n_notional"),
    )

    unit = infer_fire_expr_unit(
        expr,
        exact_units={
            "n_notional": "Amount[zUSD]",
            "strike_index": "Index",
            "cap_index": "Index",
        },
        source_units={"burn_final": "Index"},
    )

    assert unit == "Amount[zUSD]"


def test_infer_fire_expr_unit_rejects_adding_amount_and_index() -> None:
    expr = sub_expr(source_bound_expr("burn_final"), exact_param_expr("n_notional"))

    with pytest.raises(ValueError, match="sub requires matching units"):
        infer_fire_expr_unit(
            expr,
            exact_units={"n_notional": "Amount[zUSD]"},
            source_units={"burn_final": "Index"},
        )


def test_parse_fire_unit_accepts_price_syntax() -> None:
    unit = parse_fire_unit("Price[ETH/zUSD]")

    assert unit.label == "Price[ETH/zUSD]"
    assert unit.dims == (("ETH", -1), ("zUSD", 1))
