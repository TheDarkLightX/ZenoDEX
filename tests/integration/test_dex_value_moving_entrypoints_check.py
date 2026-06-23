from __future__ import annotations

import json
from pathlib import Path

from tools import check_dex_value_moving_entrypoints as checker


def test_value_moving_entrypoint_checker_accepts_current_tree(capsys) -> None:
    assert checker.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True
    assert payload["issues"] == []


def test_value_moving_entrypoint_checker_rejects_direct_apply(
    tmp_path: Path,
    monkeypatch,
    capsys,
) -> None:
    root = tmp_path
    bad = root / "src" / "integration" / "bad_runtime_path.py"
    bad.parent.mkdir(parents=True)
    bad.write_text(
        "from src.core.batch_clearing import apply_settlement_pure\n"
        "\n"
        "def bypass():\n"
        "    return apply_settlement_pure()\n",
        encoding="utf-8",
    )

    monkeypatch.setattr(checker, "ROOT", root)
    monkeypatch.setattr(checker, "WATCH_ROOTS", (root / "src",))

    assert checker.main() == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is False
    assert payload["issues"][0]["kind"] == "direct_value_moving_call"
    assert payload["issues"][0]["detail"] == "apply_settlement_pure"
