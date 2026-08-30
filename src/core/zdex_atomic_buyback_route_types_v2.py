"""Closed successor route shape for one governed ZDEX buy-and-burn."""

from __future__ import annotations

from typing import Final

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    LaneIdV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    hash_global_v1,
)
from .zdex_atomic_buyback_quote_port_v2 import (
    ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
)
from .zdex_buyback_leaf_snapshot_v2 import (
    ZDEX_SPOT_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
    ZDEX_TOKENOMICS_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
)
from .zdex_spot_buyback_transition_v2 import (
    ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2,
    ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
    ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2,
)
from .zdex_tokenomics_buyback_transition_v2 import (
    ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V2,
    ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2,
)

ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2: Final = "SPOT_BUYBACK_LEAF_V2"
ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2: Final = "ZDEX_TOKENOMICS_BUYBACK_LEAF_V2"


def _buyback_leaf_port_schema_root_v2(
    *,
    role: str,
    snapshot_schema: str,
    private_ports_schema: str,
    journal_schema: str,
) -> str:
    return hash_global_v1(
        "zdex-atomic-buyback-leaf-port-schema-v2",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "role": role,
            "quote_port_schema": ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
            "terminal_obligation_schema": ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
            "snapshot_schema": snapshot_schema,
            "private_ports_schema": private_ports_schema,
            "journal_schema": journal_schema,
        },
    )


def zdex_spot_buyback_leaf_port_schema_root_v2() -> str:
    return _buyback_leaf_port_schema_root_v2(
        role=ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2,
        snapshot_schema=ZDEX_SPOT_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
        private_ports_schema=ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2,
        journal_schema=ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2,
    )


def zdex_tokenomics_buyback_leaf_port_schema_root_v2() -> str:
    return _buyback_leaf_port_schema_root_v2(
        role=ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2,
        snapshot_schema=ZDEX_TOKENOMICS_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
        private_ports_schema=ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V2,
        journal_schema=ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2,
    )


def require_zdex_atomic_buyback_route_shape_v2(route: RouteReleaseV1) -> None:
    """Require the exact two-lane SHADOW successor route declaration."""

    if type(route) is not RouteReleaseV1:
        raise TypeError("ZDEX atomic buyback route must be exact typed data")
    if route.status is not ReleaseStatusV1.SHADOW or route.accepts_new_objects:
        raise ValueError("ZDEX atomic buyback successor route must remain SHADOW")
    if route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1:
        raise ValueError("ZDEX atomic buyback command kind mismatch")
    if route.ordered_lanes != (
        LaneIdV1.SPOT_LIQUIDITY,
        LaneIdV1.ZDEX_TOKENOMICS,
    ):
        raise ValueError("ZDEX atomic buyback lane order mismatch")
    if route.dependency_roles != (
        ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2,
        ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2,
    ):
        raise ValueError("ZDEX atomic buyback dependency roles mismatch")
    if route.port_schema_roots != (
        zdex_spot_buyback_leaf_port_schema_root_v2(),
        zdex_tokenomics_buyback_leaf_port_schema_root_v2(),
    ):
        raise ValueError("ZDEX atomic buyback port schema roots mismatch")


__all__ = [
    "ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2",
    "ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2",
    "require_zdex_atomic_buyback_route_shape_v2",
    "zdex_spot_buyback_leaf_port_schema_root_v2",
    "zdex_tokenomics_buyback_leaf_port_schema_root_v2",
]
