from __future__ import annotations

from src.core.vault import LEGACY_AGGREGATE_VAULT_MULTI_USER_AUTHORITY


def test_legacy_aggregate_vault_is_not_multi_user_authority() -> None:
    assert LEGACY_AGGREGATE_VAULT_MULTI_USER_AUTHORITY is False
