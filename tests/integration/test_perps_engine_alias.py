from __future__ import annotations

from src.integration import perp_engine as canonical
from src.integration.perps import engine as alias


def test_perps_engine_alias_reexports_canonical_symbols() -> None:
    assert alias.apply_perp_ops is canonical.apply_perp_ops
    assert alias.parse_perp_ops is canonical.parse_perp_ops
    assert alias.PerpEngineConfig is canonical.PerpEngineConfig
    assert alias.PerpOp is canonical.PerpOp
    assert alias.PerpTxResult is canonical.PerpTxResult

