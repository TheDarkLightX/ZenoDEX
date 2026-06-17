import pytest

from src.core.fixed_width import (
    add_checked,
    add_wrap,
    mul_checked,
    mul_wrap,
    uN_max,
    uN_mod,
    will_add_overflow,
    will_mul_overflow,
)


@pytest.mark.parametrize(
    "call",
    [
        lambda: uN_max(True),
        lambda: uN_mod(True),
        lambda: will_add_overflow(True, 0, 0),
        lambda: will_mul_overflow(True, 0, 0),
        lambda: add_checked(True, 0, 0),
        lambda: mul_checked(True, 0, 0),
        lambda: add_wrap(True, 0, 0),
        lambda: mul_wrap(True, 0, 0),
    ],
)
def test_fixed_width_rejects_bool_bit_width(call) -> None:
    with pytest.raises(TypeError, match="bits must be an int"):
        call()


@pytest.mark.parametrize(
    "call",
    [
        lambda: will_add_overflow(8, True, 0),
        lambda: will_mul_overflow(8, 0, False),
        lambda: add_checked(8, True, 0),
        lambda: mul_checked(8, 0, False),
        lambda: add_wrap(8, True, 0),
        lambda: mul_wrap(8, 0, False),
    ],
)
def test_fixed_width_rejects_bool_values(call) -> None:
    with pytest.raises(TypeError, match="value must be an int"):
        call()


def test_fixed_width_valid_integer_behavior_is_unchanged() -> None:
    assert uN_max(8) == 255
    assert uN_mod(8) == 256
    assert will_add_overflow(8, 200, 55) is False
    assert will_add_overflow(8, 200, 56) is True
    assert will_mul_overflow(8, 15, 17) is False
    assert will_mul_overflow(8, 16, 17) is True
    assert add_checked(8, 2, 3) == 5
    assert mul_checked(8, 7, 9) == 63
    assert add_wrap(8, 255, 1) == 0
    assert mul_wrap(8, 128, 2) == 0
