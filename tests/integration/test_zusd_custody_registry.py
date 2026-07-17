from __future__ import annotations

from src.core.zusd_generic_token_admission import CanonicalZUSDCustodyClass
from src.integration.zusd_custody_registry import (
    build_live_canonical_zusd_custody_registry,
)
from src.integration.zusd_monetary_bridge import stability_pool_pubkey


def test_live_canonical_zusd_custody_registry_binds_chain_stability_pool() -> None:
    chain_id = "tau-custody-registry-binding"
    registry = build_live_canonical_zusd_custody_registry(chain_id=chain_id)
    expected_stability_pool = stability_pool_pubkey(chain_id=chain_id)

    assert len(registry.principals) == 1
    assert registry.classify(expected_stability_pool) is (
        CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW
    )
    assert registry.classify("0x" + "7f" * 48) is (
        CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT
    )


def test_live_canonical_zusd_custody_registry_is_chain_separated() -> None:
    chain_a = build_live_canonical_zusd_custody_registry(chain_id="tau-chain-a")
    chain_b_pool = stability_pool_pubkey(chain_id="tau-chain-b")

    assert chain_a.classify(chain_b_pool) is (
        CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT
    )
