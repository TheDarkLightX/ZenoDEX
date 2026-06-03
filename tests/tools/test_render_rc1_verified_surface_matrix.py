from __future__ import annotations


def test_render_rc1_verified_surface_matrix_is_current() -> None:
    from tools.render_rc1_verified_surface_matrix import main

    assert main(["--check"]) == 0
