from __future__ import annotations

from src.integration.perps_wallet_authority import (
    _active_signer_summaries,
    _guardian_signature_quorum_summary,
)


def test_perps_wallet_authority_summary_helpers_reject_bool_numerics() -> None:
    quorum = _guardian_signature_quorum_summary(
        {
            "threshold": True,
            "accepted_weight": False,
            "accepted_signatures": [
                {
                    "signer_id": "guardian-a",
                    "key_id": "perps-wallet-a",
                    "weight": True,
                    "envelope_hash": "0x" + "aa" * 32,
                }
            ],
        }
    )
    signers = _active_signer_summaries(
        [
            {
                "signer_id": "wallet-a",
                "key_id": "perps-wallet-a",
                "weight": True,
                "signer_hash": "0x" + "bb" * 32,
            }
        ]
    )

    assert quorum["threshold"] == 0
    assert quorum["accepted_weight"] == 0
    assert quorum["accepted_signatures"][0]["weight"] == 0
    assert signers[0]["weight"] == 0
