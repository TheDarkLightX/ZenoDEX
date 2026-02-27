from __future__ import annotations


def _henon_step_mod_m(x: int, y: int, *, a: int, b: int, m: int) -> tuple[int, int]:
    # A tiny "Hénon-like" map over integers modulo m:
    #   x_{t+1} = 1 - a*x_t^2 + y_t  (mod m)
    #   y_{t+1} = b*x_t              (mod m)
    #
    # This is only used as a toy counterexample for the "chaos implies unpredictability"
    # claim in deterministic, finite-state execution.
    x1 = (1 - a * (x * x) + y) % m
    y1 = (b * x) % m
    return x1, y1


def test_deterministic_chaotic_fee_update_is_predictable_one_step_ahead() -> None:
    # Falsifier for the strong claim that "chaos makes next-block fee unpredictable
    # to MEV simulators" in a deterministic protocol.
    #
    # If the fee update is a deterministic function of the public state, anyone
    # can compute fee_{t+1} exactly in O(1) time by evaluating the function once.
    #
    # This test is intentionally minimal: it asserts the update is a pure function.
    a, b, m = 1, 3, 10_000
    x0, y0 = 123, 456
    x1a, y1a = _henon_step_mod_m(x0, y0, a=a, b=b, m=m)
    x1b, y1b = _henon_step_mod_m(x0, y0, a=a, b=b, m=m)
    assert (x1a, y1a) == (x1b, y1b)


def test_finite_state_deterministic_fee_system_has_cycles() -> None:
    # Any deterministic update on a finite state space eventually repeats => cycles exist.
    # This undermines "infinite novelty" narratives and matches the falsification spirit
    # of "find short cycles" in finite-precision execution.
    a, b, m = 5, 7, 97  # small modulus to force tiny state space
    x, y = 1, 1

    seen: dict[tuple[int, int], int] = {}
    steps = 0
    while (x, y) not in seen:
        seen[(x, y)] = steps
        x, y = _henon_step_mod_m(x, y, a=a, b=b, m=m)
        steps += 1
        # Safety cap: we must see a repeat by pigeonhole in <= m^2 + 1 steps.
        assert steps <= m * m + 1

    cycle_len = steps - seen[(x, y)]
    assert cycle_len >= 1

