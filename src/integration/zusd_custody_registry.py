from __future__ import annotations

from ..core.zusd_generic_token_admission import (
    CanonicalZUSDCustodyClass,
    CanonicalZUSDCustodyRegistry,
    ReservedCanonicalZUSDCustodyPrincipal,
)
from .zusd_monetary_bridge import stability_pool_pubkey


def build_live_canonical_zusd_custody_registry(
    *, chain_id: str
) -> CanonicalZUSDCustodyRegistry:
    """Build the exact live registry of addressable internal zUSD custody.

    The current monetary bridge exposes one deterministic balance-table
    principal: Stability Pool escrow. Gas reserve, fee pools, and perps quote
    liabilities remain internal ledgers without recipient pubkeys. Any future
    addressable custody principal must be added here before generic canonical
    zUSD transfer admission can classify it as reserved.
    """

    return CanonicalZUSDCustodyRegistry(
        principals=(
            ReservedCanonicalZUSDCustodyPrincipal(
                recipient_pubkey=stability_pool_pubkey(chain_id=chain_id),
                custody_class=CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW,
            ),
        )
    )
