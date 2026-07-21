"""Pure canonical policy for protocol-fee capture.

An accepted value recipient must be representable by the same canonical state
encoding used after settlement.  Keeping this check in the functional core
prevents an accepted transition from producing an unhashable state.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..state.canonical import canonical_hex_fixed_allow_0x

_BPS_SCALE = 10_000
_ZERO_BLS_PUBKEY = "0x" + "00" * 48


@dataclass(frozen=True, slots=True)
class ProtocolFeePolicy:
    """Canonical protocol-fee share and its reachable recipient."""

    share_bps: int = 0
    recipient_pubkey: str | None = None

    def __post_init__(self) -> None:
        if type(self.share_bps) is not int:
            raise TypeError("protocol_fee_share_bps must be an int")
        if not 0 <= self.share_bps <= _BPS_SCALE:
            raise ValueError("protocol_fee_share_bps must be in [0, 10000]")

        recipient = self.recipient_pubkey
        if recipient is None:
            if self.share_bps > 0:
                raise ValueError(
                    "protocol_fee_recipient_pubkey is required when "
                    "protocol_fee_share_bps > 0"
                )
            return
        if type(recipient) is not str:
            raise TypeError("protocol_fee_recipient_pubkey must be a string or None")

        canonical = canonical_hex_fixed_allow_0x(
            recipient,
            nbytes=48,
            name="protocol_fee_recipient_pubkey",
        )
        if canonical == _ZERO_BLS_PUBKEY:
            raise ValueError("protocol_fee_recipient_pubkey must not be all-zero")
        object.__setattr__(self, "recipient_pubkey", canonical)


def canonical_protocol_fee_policy(
    *,
    share_bps: int,
    recipient_pubkey: str | None,
) -> ProtocolFeePolicy:
    """Construct the only policy representation accepted by core settlement."""

    return ProtocolFeePolicy(
        share_bps=share_bps,
        recipient_pubkey=recipient_pubkey,
    )


__all__ = ["ProtocolFeePolicy", "canonical_protocol_fee_policy"]
