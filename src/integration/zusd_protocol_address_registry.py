from __future__ import annotations

from ..core.zusd_generic_token_admission import (
    CanonicalZUSDProtocolAddressRegistry,
    CanonicalZUSDRecipientClass,
    ReservedCanonicalZUSDPrincipal,
)
from .zusd_monetary_bridge import stability_pool_pubkey


def build_live_canonical_zusd_protocol_address_registry(
    *, chain_id: str
) -> CanonicalZUSDProtocolAddressRegistry:
    """Build the exact live registry of reserved zUSD protocol addresses.

    The current monetary bridge exposes one deterministic balance-table
    principal: Stability Pool escrow. Gas reserve, fee pools, and perps quote
    liabilities remain internal ledgers without recipient pubkeys. Any future
    reserved protocol address must be added here before generic canonical
    zUSD transfer admission can classify it as reserved.
    """

    return CanonicalZUSDProtocolAddressRegistry(
        principals=(
            ReservedCanonicalZUSDPrincipal(
                recipient_pubkey=stability_pool_pubkey(chain_id=chain_id),
                recipient_class=CanonicalZUSDRecipientClass.STABILITY_POOL_ESCROW,
            ),
        )
    )
