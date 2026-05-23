from __future__ import annotations


def test_integer_i_projection_need_not_be_unique_even_if_continuous_projection_is() -> None:
    # Falsifier for the strong "I-projection yields a unique post-state" claim
    # once you require *integer* reserves.
    #
    # Project z=(1,2) onto the manifold x=y with squared Euclidean distance.
    # Continuous unique projection is (1.5, 1.5).
    # Integer feasible points are (k,k); the minimizers tie at k=1 and k=2.
    z = (1, 2)

    def dist2(k: int) -> int:
        return (k - z[0]) * (k - z[0]) + (k - z[1]) * (k - z[1])

    d1 = dist2(1)
    d2 = dist2(2)
    assert d1 == d2
    assert (1, 1) != (2, 2)

