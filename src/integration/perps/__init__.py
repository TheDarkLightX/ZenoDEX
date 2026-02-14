"""Perps integration package.

This package contains the perps imperative-shell adapter (tx ops group `"5"`)
and related helpers (parsing, auth, reference models).

Public entrypoint (re-exported by `src/integration/perp_engine.py`):
- `apply_perp_ops`
"""

from .engine import PerpEngineConfig, PerpOp, PerpTxResult, apply_perp_ops, parse_perp_ops

__all__ = [
    "PerpEngineConfig",
    "PerpOp",
    "PerpTxResult",
    "apply_perp_ops",
    "parse_perp_ops",
]

