from __future__ import annotations

from pathlib import Path

from tests.integration.vite_test_server import vite_dev_command

ROOT = Path(__file__).resolve().parents[2]


def test_vite_dev_command_execs_vite_without_npm_wrapper() -> None:
    argv = vite_dev_command(Path("/tmp/dex-ui"), 12345)

    assert argv == [
        "/tmp/dex-ui/node_modules/.bin/vite",
        "--host",
        "127.0.0.1",
        "--port",
        "12345",
    ]
    assert "npm" not in argv


def test_integration_ui_tests_do_not_launch_vite_through_npm_wrapper() -> None:
    tuple_literal = '"npm", "run", ' + '"dev"'
    shell_text = "npm run " + "dev"
    offenders = []
    for path in sorted((ROOT / "tests" / "integration").glob("test*.py")):
        text = path.read_text(encoding="utf-8")
        if tuple_literal in text or shell_text in text:
            offenders.append(path.relative_to(ROOT).as_posix())

    assert offenders == []
