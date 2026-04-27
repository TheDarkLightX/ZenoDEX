from __future__ import annotations

from typing import Mapping

from src.fire.kernel.ledger_adapter_v1 import (
    FireLedgerApplyResult,
    FireLedgerBalances,
    apply_verified_fire_settlement_effects,
    apply_verified_fire_settlement_packet,
)
from src.fire.kernel.persisted_bundle_settlement_v1 import (
    FirePersistedBundleSettlementResult,
    apply_fire_persisted_bundle_settlement,
)


def apply_fire_object_package_settlement(
    *,
    bundle_dir: str,
    holder_posted: int,
    writer_posted: int,
    holder_balance: int,
    writer_balance: int,
    witness_inputs: Mapping[str, object],
) -> tuple[bool, str | None, FirePersistedBundleSettlementResult | None]:
    """Bridge the current package-settlement path into the src/fire kernel surface."""

    return apply_fire_persisted_bundle_settlement(
        bundle_dir=bundle_dir,
        holder_posted=holder_posted,
        writer_posted=writer_posted,
        holder_balance=holder_balance,
        writer_balance=writer_balance,
        witness_inputs=witness_inputs,
    )


__all__ = [
    "FireLedgerApplyResult",
    "FireLedgerBalances",
    "FirePersistedBundleSettlementResult",
    "apply_fire_object_package_settlement",
    "apply_fire_persisted_bundle_settlement",
    "apply_verified_fire_settlement_effects",
    "apply_verified_fire_settlement_packet",
]
