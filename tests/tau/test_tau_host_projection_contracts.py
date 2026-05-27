from __future__ import annotations

from pathlib import Path

from tools.check_tau_host_projection_contracts import lint_host_projection_contracts


ROOT = Path(__file__).resolve().parents[2]


def test_tau_host_projection_contracts_lint_clean() -> None:
    errors = lint_host_projection_contracts(ROOT / "src" / "tau_specs" / "recommended" / "host_projection_contracts.json")
    assert errors == []
