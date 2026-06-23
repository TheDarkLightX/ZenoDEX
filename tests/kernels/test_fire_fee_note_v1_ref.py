from __future__ import annotations

from src.fire.kernel import fire_fee_note_v1_ref as ref


def _compile(*, n: int, cap: int, source_upper: int) -> ref.State:
    result = ref.step(
        ref.init_state(),
        ref.Command(
            tag="compile_fee_note",
            args={
                "n_in": n,
                "cap_in": cap,
                "source_upper_in": source_upper,
            },
        ),
    )
    assert result.ok is True
    assert result.state is not None
    return result.state


def _manual_payoff(*, n: int, cap: int, witness_final: int) -> int:
    return n * min(witness_final, cap)


def test_fire_fee_note_compile_emits_expected_interval_when_cap_binds() -> None:
    state = _compile(n=10, cap=3, source_upper=9)

    assert state.phase == "Compiled"
    assert state.artifact_lower == 0
    assert state.artifact_upper == 30
    assert state.n_notional == 10
    assert state.cap_index == 3
    assert state.source_upper == 9

    ok, failed = ref.check_invariants(state)
    assert ok is True, failed


def test_fire_fee_note_compile_emits_expected_interval_when_source_binds() -> None:
    state = _compile(n=10, cap=7, source_upper=2)

    assert state.phase == "Compiled"
    assert state.artifact_lower == 0
    assert state.artifact_upper == 20

    ok, failed = ref.check_invariants(state)
    assert ok is True, failed


def test_fire_fee_note_rejects_undercollateralized_writer() -> None:
    state = _compile(n=10, cap=7, source_upper=2)
    result = ref.step(
        state,
        ref.Command(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 19,
            },
        ),
    )

    assert result.ok is False
    assert result.error is not None
    assert "guard failed" in result.error


def test_fire_fee_note_rejects_witness_above_source_bound() -> None:
    state = _compile(n=10, cap=7, source_upper=2)
    result = ref.step(
        state,
        ref.Command(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 3,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
            },
        ),
    )

    assert result.ok is False
    assert result.error is not None
    assert "guard failed" in result.error


def test_fire_fee_note_boundary_payoffs() -> None:
    state = _compile(n=10, cap=3, source_upper=9)

    for witness_final in [0, 1, 3, 5, 9]:
        result = ref.step(
            state,
            ref.Command(
                tag="firev_accept_and_settle",
                args={
                    "witness_final_in": witness_final,
                    "holder_posted_in": 0,
                    "writer_posted_in": 30,
                },
            ),
        )

        assert result.ok is True
        assert result.state is not None
        payoff = _manual_payoff(n=10, cap=3, witness_final=witness_final)

        assert result.state.phase == "Settled"
        assert result.state.holder_delta == payoff
        assert result.state.writer_delta == -payoff
        assert result.state.holder_delta + result.state.writer_delta == 0
        assert 0 <= result.state.holder_delta <= 30
        assert result.effects is not None
        assert result.effects["firev_accept"] is True
        assert result.effects["payoff_out"] == payoff

        ok, failed = ref.check_invariants(result.state)
        assert ok is True, failed


def test_fire_fee_note_small_grid_matches_manual_formula() -> None:
    for n in range(0, 4):
        for cap in range(0, 4):
            for source_upper in range(0, 4):
                state = _compile(n=n, cap=cap, source_upper=source_upper)
                for witness_final in range(0, source_upper + 1):
                    result = ref.step(
                        state,
                        ref.Command(
                            tag="firev_accept_and_settle",
                            args={
                                "witness_final_in": witness_final,
                                "holder_posted_in": 0,
                                "writer_posted_in": n * min(cap, source_upper),
                            },
                        ),
                    )

                    assert result.ok is True
                    assert result.state is not None
                    expected = _manual_payoff(
                        n=n,
                        cap=cap,
                        witness_final=witness_final,
                    )
                    assert result.state.holder_delta == expected
                    assert result.state.writer_delta == -expected
                    assert 0 <= expected <= n * min(cap, source_upper)
