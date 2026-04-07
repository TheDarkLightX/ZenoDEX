from __future__ import annotations

from tools.render_tla_claim_summary import REPO_ROOT, _claim_index_by_cfg, _load_supported_tla_claims
from tools.run_tla_models import _discover_models


def test_supported_tla_claims_match_discovered_models() -> None:
    claims = _load_supported_tla_claims()
    claim_index = _claim_index_by_cfg(claims)
    discovered = {name for name, _cfg, _tla in _discover_models(REPO_ROOT / "formal" / "tla")}
    assert discovered == set(claim_index)
