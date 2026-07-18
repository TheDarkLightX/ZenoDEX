"""Boundary tests for protocol-fee recipient authority and encodability."""

from __future__ import annotations

import pytest

from src.core.dex import DexConfig
from src.core.protocol_fee_policy import ProtocolFeePolicy
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.state_root import compute_state_root

_RECIPIENT_RAW = "41" * 48
_RECIPIENT = "0x" + _RECIPIENT_RAW
_ASSET = "0x" + "51" * 32


def test_nonzero_protocol_share_requires_reachable_recipient() -> None:
    with pytest.raises(ValueError, match="recipient_pubkey is required"):
        ProtocolFeePolicy(share_bps=1, recipient_pubkey=None)


def test_protocol_fee_policy_rejects_primitive_and_bps_boundaries() -> None:
    with pytest.raises(TypeError, match="share_bps must be an int"):
        ProtocolFeePolicy(share_bps=True, recipient_pubkey=_RECIPIENT)
    with pytest.raises(ValueError, match=r"\[0, 10000\]"):
        ProtocolFeePolicy(share_bps=-1, recipient_pubkey=_RECIPIENT)
    with pytest.raises(ValueError, match=r"\[0, 10000\]"):
        ProtocolFeePolicy(share_bps=10_001, recipient_pubkey=_RECIPIENT)
    with pytest.raises(TypeError, match="string or None"):
        ProtocolFeePolicy(share_bps=1, recipient_pubkey=1)  # type: ignore[arg-type]


@pytest.mark.parametrize("recipient", ("", " ", "not-a-key", "0x" + "00" * 48))
def test_protocol_fee_policy_rejects_unencodable_or_unreachable_recipient(
    recipient: str,
) -> None:
    with pytest.raises((TypeError, ValueError)):
        ProtocolFeePolicy(share_bps=1, recipient_pubkey=recipient)


def test_dex_config_owns_one_canonical_recipient() -> None:
    config = DexConfig(
        protocol_fee_share_bps=2_500,
        protocol_fee_recipient_pubkey=_RECIPIENT_RAW,
    )

    assert config.protocol_fee_share_bps == 2_500
    assert config.protocol_fee_recipient_pubkey == _RECIPIENT


def test_canonical_recipient_is_state_root_encodable() -> None:
    config = DexConfig(
        protocol_fee_share_bps=1,
        protocol_fee_recipient_pubkey=_RECIPIENT_RAW,
    )
    assert config.protocol_fee_recipient_pubkey is not None

    balances = BalanceTable()
    balances.set(config.protocol_fee_recipient_pubkey, _ASSET, 1)

    root = compute_state_root(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
    )

    assert root.startswith("0x")
    assert len(root) == 66


def test_zero_share_may_retain_canonical_dormant_recipient() -> None:
    config = DexConfig(
        protocol_fee_share_bps=0,
        protocol_fee_recipient_pubkey=_RECIPIENT_RAW,
    )

    assert config.protocol_fee_recipient_pubkey == _RECIPIENT
