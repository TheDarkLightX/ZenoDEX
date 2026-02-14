"""Compatibility re-export for the canonical perps engine.

Historically this package contained a full copy of the perps adapter logic,
which drifted from `src.integration.perp_engine`. Keep a single source of
truth by re-exporting the canonical implementation here.
"""

from __future__ import annotations

from ..perp_engine import PerpEngineConfig, PerpOp, PerpTxResult, apply_perp_ops, parse_perp_ops

__all__ = [
    "PerpEngineConfig",
    "PerpOp",
    "PerpTxResult",
    "apply_perp_ops",
    "parse_perp_ops",
]
