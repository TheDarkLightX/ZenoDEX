from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from typing import Mapping, Sequence

import pytest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "tools" / "dex-ui" / "scripts" / "check-ui-contract.mjs"
QUARANTINED_UI_FIELDS = (
    "perpsWalletUiEnabled",
    "zusdTauWalletUiEnabled",
    "zusdMonetaryWalletUiEnabled",
)


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + "\n", encoding="utf-8")


def _run_checker(
    tmp_path: Path,
    runtime_config: Mapping[str, object],
    *,
    quarantine_fields: Sequence[str] = QUARANTINED_UI_FIELDS,
) -> subprocess.CompletedProcess[str]:
    ui_root = tmp_path / "dex-ui"
    script = ui_root / "scripts" / CHECKER.name
    script.parent.mkdir(parents=True)
    shutil.copyfile(CHECKER, script)
    _write_json(
        ui_root / "public" / "zenodex-ui-contract.json",
        {
            "schema": "zenodex.dex_ui.surface_contract.v1",
            "version": "quarantine-mutant-test-v1",
            "current_quarantined_value_route_ui_flags": list(quarantine_fields),
            "source_markers": [],
            "forbidden_source_markers": [],
        },
    )
    _write_json(ui_root / "public" / "zenodex-config.json", runtime_config)
    _write_json(ui_root / "package.json", {"dependencies": {}, "devDependencies": {}})
    return subprocess.run(
        ["node", str(script)],
        check=False,
        capture_output=True,
        text=True,
    )


def test_ui_contract_accepts_exact_false_quarantine_flags(tmp_path: Path) -> None:
    runtime_config: dict[str, object] = {field: False for field in QUARANTINED_UI_FIELDS}

    result = _run_checker(tmp_path, runtime_config)

    assert result.returncode == 0, result.stderr
    assert "quarantine-mutant-test-v1 ok" in result.stdout


@pytest.mark.parametrize("mutant", [True, "false", 0, None])
def test_ui_contract_kills_non_false_quarantine_flag_mutants(
    tmp_path: Path,
    mutant: object,
) -> None:
    runtime_config: dict[str, object] = {field: False for field in QUARANTINED_UI_FIELDS}
    runtime_config["perpsWalletUiEnabled"] = mutant

    result = _run_checker(tmp_path, runtime_config)

    assert result.returncode == 1
    assert "must keep perpsWalletUiEnabled exactly false" in result.stderr


def test_ui_contract_rejects_missing_quarantine_flag(tmp_path: Path) -> None:
    runtime_config: dict[str, object] = {field: False for field in QUARANTINED_UI_FIELDS}
    del runtime_config["zusdMonetaryWalletUiEnabled"]

    result = _run_checker(tmp_path, runtime_config)

    assert result.returncode == 1
    assert "missing quarantined value-route UI flag: zusdMonetaryWalletUiEnabled" in result.stderr


def test_ui_contract_rejects_registry_omission(tmp_path: Path) -> None:
    runtime_config: dict[str, object] = {field: False for field in QUARANTINED_UI_FIELDS}

    result = _run_checker(
        tmp_path,
        runtime_config,
        quarantine_fields=QUARANTINED_UI_FIELDS[:-1],
    )

    assert result.returncode == 1
    assert "must equal the exact closed current-profile registry" in result.stderr
