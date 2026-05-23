from __future__ import annotations

from fractions import Fraction


def test_constant_product_is_not_a_rotation_in_reserve_space() -> None:
    # Falsifier for the strong "multi-asset constant-product swaps are pure rotations"
    # (Clifford rotor / isometry) claim when the state is represented as the reserve
    # vector (x,y,...) and the swap is an isometry in that vector space.
    #
    # Any rotor/isometry preserves an inner-product norm (in Euclidean R^n: sum of squares).
    # The constant-product manifold x*y=k does not have constant Euclidean norm, so an
    # isometry cannot realize generic swaps that move between two valid reserve states.
    k = 4
    p = (1, 4)
    q = (2, 2)

    assert p[0] * p[1] == k
    assert q[0] * q[1] == k

    norm2_p = p[0] * p[0] + p[1] * p[1]  # 17
    norm2_q = q[0] * q[0] + q[1] * q[1]  # 8
    assert norm2_p != norm2_q


def test_constant_product_swap_generically_changes_euclidean_norm() -> None:
    # Same idea, but phrased as: the (continuous) CPMM swap map changes Euclidean norm
    # for generic dx, so it cannot be implemented as a norm-preserving rotation.
    #
    # fee=0, K=x*y fixed. Start at (x,y)=(10,10), K=100. After dx=1, the new state is:
    #   x' = 11, y' = K/x' = 100/11
    # Norm^2 initial = 200, Norm^2 final = 11^2 + (100/11)^2 != 200.
    x = 10
    y = 10
    k = x * y
    dx = 1

    x1 = x + dx
    y1 = Fraction(k, x1)

    norm2_0 = Fraction(x * x + y * y, 1)
    norm2_1 = Fraction(x1 * x1, 1) + y1 * y1
    assert norm2_0 == Fraction(200, 1)
    assert norm2_1 != norm2_0

