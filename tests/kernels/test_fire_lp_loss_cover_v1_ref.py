from __future__ import annotations

from src.fire.kernel import fire_lp_loss_cover_v1_ref as ref


def _compile(
    *,
    n: int,
    deductible: int,
    cap: int,
    hodl_lower: int,
    hodl_upper: int,
    lpv_lower: int,
    lpv_upper: int,
) -> ref.State:
    result = ref.step(
        ref.init_state(),
        ref.Command(
            tag="compile_lp_loss_cover",
            args={
                "n_in": n,
                "deductible_in": deductible,
                "cap_in": cap,
                "hodl_lower_in": hodl_lower,
                "hodl_upper_in": hodl_upper,
                "lpv_lower_in": lpv_lower,
                "lpv_upper_in": lpv_upper,
            },
        ),
    )
    assert result.ok is True
    assert result.state is not None
    return result.state


def _manual_payoff(*, n: int, deductible: int, cap: int, hodl_final: int, lpv_final: int) -> int:
    return n * min(max(hodl_final - lpv_final - deductible, 0), cap)


def test_fire_lp_loss_cover_compile_emits_expected_interval() -> None:
    state = _compile(n=10, deductible=2, cap=5, hodl_lower=10, hodl_upper=20, lpv_lower=7, lpv_upper=12)

    assert state.phase == "Compiled"
    assert state.artifact_lower == 0
    assert state.artifact_upper == 50
    assert state.hodl_lower == 10
    assert state.hodl_upper == 20
    assert state.lpv_lower == 7
    assert state.lpv_upper == 12

    ok, failed = ref.check_invariants(state)
    assert ok is True, failed


def test_fire_lp_loss_cover_rejects_bad_interval_order() -> None:
    result = ref.step(
        ref.init_state(),
        ref.Command(
            tag="compile_lp_loss_cover",
            args={
                "n_in": 10,
                "deductible_in": 2,
                "cap_in": 5,
                "hodl_lower_in": 20,
                "hodl_upper_in": 10,
                "lpv_lower_in": 7,
                "lpv_upper_in": 12,
            },
        ),
    )

    assert result.ok is False
    assert result.error is not None
    assert "guard failed" in result.error


def test_fire_lp_loss_cover_rejects_undercollateralized_writer() -> None:
    state = _compile(n=10, deductible=2, cap=5, hodl_lower=10, hodl_upper=20, lpv_lower=7, lpv_upper=12)
    result = ref.step(
        state,
        ref.Command(
            tag="firev_accept_and_settle",
            args={
                "witness_hodl_final_in": 20,
                "witness_lpv_final_in": 7,
                "holder_posted_in": 0,
                "writer_posted_in": 49,
            },
        ),
    )

    assert result.ok is False
    assert result.error is not None
    assert "guard failed" in result.error


def test_fire_lp_loss_cover_boundary_payoffs() -> None:
    state = _compile(n=10, deductible=2, cap=5, hodl_lower=10, hodl_upper=20, lpv_lower=7, lpv_upper=12)

    for hodl_final, lpv_final in [(10, 12), (15, 12), (20, 12), (20, 7)]:
        result = ref.step(
            state,
            ref.Command(
                tag="firev_accept_and_settle",
                args={
                    "witness_hodl_final_in": hodl_final,
                    "witness_lpv_final_in": lpv_final,
                    "holder_posted_in": 0,
                    "writer_posted_in": 50,
                },
            ),
        )

        assert result.ok is True
        assert result.state is not None
        payoff = _manual_payoff(n=10, deductible=2, cap=5, hodl_final=hodl_final, lpv_final=lpv_final)

        assert result.state.phase == "Settled"
        assert result.state.holder_delta == payoff
        assert result.state.writer_delta == -payoff
        assert result.state.holder_delta + result.state.writer_delta == 0
        assert 0 <= result.state.holder_delta <= 50
        assert result.effects is not None
        assert result.effects["firev_accept"] is True
        assert result.effects["payoff_out"] == payoff

        ok, failed = ref.check_invariants(result.state)
        assert ok is True, failed
