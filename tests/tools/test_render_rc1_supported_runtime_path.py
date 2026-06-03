from __future__ import annotations


def test_render_rc1_supported_runtime_path_is_current() -> None:
    from tools.render_rc1_supported_runtime_path import main

    assert main(["--check"]) == 0
