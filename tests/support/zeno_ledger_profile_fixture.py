"""Test-only mutations for ZenoLedger profile validation cases."""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping

from src.integration.zeno_ledger_profile import profile_content_hash_v0


def clone_profile_with_new_id_v0(
    profile: Mapping[str, Any],
    **updates: Any,
) -> dict[str, Any]:
    updated = deepcopy(dict(profile))
    updated.update(updates)
    updated["profile_id"] = profile_content_hash_v0(updated)
    return updated
