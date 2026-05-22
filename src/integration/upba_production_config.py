"""Production-candidate UPBA engine configuration helpers."""

from __future__ import annotations

from dataclasses import replace
from typing import Optional

from .dex_engine import DexEngineConfig


def make_upba_v1_bounded_price_grid_engine_config(
    base: Optional[DexEngineConfig] = None,
) -> DexEngineConfig:
    """Return the strict UPBA v1 bounded price-grid engine posture.

    The helper is intentionally scoped to the current UPBA v1 swap surface:
    single-pool exact-in uniform batch certificates with complete bounded
    price-grid table evidence. It preserves unrelated deployment fields from
    ``base`` while forcing the safety-critical flags that make the UPBA checker
    authoritative for swap batches.
    """

    cfg = base or DexEngineConfig()
    return replace(
        cfg,
        allow_missing_settlement=False,
        require_settlement_match=True,
        require_intent_signatures=True,
        allow_external_tools=False,
        consensus_mode=True,
        allow_uniform_batch_certificate=True,
        require_uniform_batch_certificate_for_supported_swaps=True,
        require_uniform_batch_optimality_certificate=True,
        require_uniform_batch_v2_bounded_grid_optimality=True,
        require_uniform_batch_v3_exact_out_grid_optimality=True,
        enable_test_fault_injection=False,
        fault_injection=None,
    )
