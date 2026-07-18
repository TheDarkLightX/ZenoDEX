"""Bind live Tau token identities to the verified zUSD admission kernel.

This module owns classification only. It performs no balance mutation and
grants no monetary authority. Callers must authenticate and canonicalize the
wire fields before invoking it, then execute only an ``ADMITTED`` decision.
"""

from __future__ import annotations

from ..core.zusd_generic_token_admission import (
    CanonicalZUSDCustodyClass,
    GenericTokenAction,
    GenericTokenAdmissionCommand,
    GenericTokenAdmissionDecision,
    TokenAssetClass,
    TokenWriterRole,
    evaluate_generic_token_admission,
)
from .zusd_custody_registry import build_live_canonical_zusd_custody_registry


def evaluate_live_generic_token_writer_admission(
    *,
    chain_id: str,
    canonical_zusd_asset: str,
    action: GenericTokenAction | str,
    asset: str,
    recipient_pubkey: str | None,
) -> GenericTokenAdmissionDecision:
    """Classify one authenticated generic-token operation and decide admission.

    Mechanical guarantee: canonical zUSD mint, burn, and transfer into a live
    reserved custody principal are rejected by the same pure decision function
    used by Lean and generated-reference parity tests.

    Non-guarantees: this function does not authenticate the sender, validate
    amounts, mutate balances, check nonces, or commit effects.
    """

    if type(chain_id) is not str or not chain_id.strip():
        raise ValueError("chain_id must be a non-empty str")
    if type(canonical_zusd_asset) is not str or not canonical_zusd_asset:
        raise TypeError("canonical_zusd_asset must be a non-empty str")
    if type(asset) is not str or not asset:
        raise TypeError("asset must be a non-empty str")

    typed_action = action if isinstance(action, GenericTokenAction) else GenericTokenAction(action)
    asset_class = (
        TokenAssetClass.CANONICAL_ZUSD if asset == canonical_zusd_asset else TokenAssetClass.OTHER
    )
    custody_class = CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT
    if recipient_pubkey is not None:
        if type(recipient_pubkey) is not str or not recipient_pubkey:
            raise TypeError("recipient_pubkey must be a non-empty str when present")
        custody_class = build_live_canonical_zusd_custody_registry(chain_id=chain_id).classify(
            recipient_pubkey
        )

    return evaluate_generic_token_admission(
        GenericTokenAdmissionCommand(
            action=typed_action,
            asset_class=asset_class,
            writer_role=TokenWriterRole.GENERIC_TOKEN_WRITER,
            recipient_custody_class=custody_class,
        )
    )


def generic_token_admission_reject_code(
    decision: GenericTokenAdmissionDecision,
) -> str | None:
    """Return the stable lower-case reject code, or ``None`` when admitted."""

    if not isinstance(decision, GenericTokenAdmissionDecision):
        raise TypeError("decision must be a GenericTokenAdmissionDecision")
    return None if decision.admitted else decision.code.name.lower()
