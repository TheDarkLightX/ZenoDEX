from __future__ import annotations

import pytest

from src.core import vault
from src.core.vault import VaultCommand, init_vault_state


def test_vault_step_returns_domain_errors_as_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_harvest(_state: object, _args: object) -> object:
        raise ValueError("domain reject")

    monkeypatch.setattr(vault, "_harvest", reject_harvest)

    result = vault.step(init_vault_state(), VaultCommand(tag="harvest", args={"entry_acc": 0}))

    assert result.ok is False
    assert result.error == "domain reject"


def test_vault_step_does_not_swallow_helper_bugs(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_harvest(_state: object, _args: object) -> object:
        raise RuntimeError("vault helper bug")

    monkeypatch.setattr(vault, "_harvest", broken_harvest)

    with pytest.raises(RuntimeError, match="vault helper bug"):
        vault.step(init_vault_state(), VaultCommand(tag="harvest", args={"entry_acc": 0}))
