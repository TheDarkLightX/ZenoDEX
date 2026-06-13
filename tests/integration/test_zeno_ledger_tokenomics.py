from __future__ import annotations

import pytest

from src.integration.zeno_ledger_tokenomics import (
    LOCAL_TESTNET_BUYBACK_SHARE_BPS,
    build_active_participant_reward_claim_v0,
    build_protocol_token_distribution_v0,
    build_tokenomics_buyback_burn_event_v0,
    validate_active_participant_reward_claim_v0,
    validate_protocol_token_distribution_v0,
    validate_tokenomics_buyback_burn_event_v0,
)


def _pubkey(byte: str) -> str:
    return "0x" + byte * 48


def _asset(byte: str) -> str:
    return "0x" + byte * 32


def _distribution() -> dict[str, object]:
    return build_protocol_token_distribution_v0(
        chain_id="tokenomics-test-chain",
        token_symbol="ZDEX",
        token_asset_id=_asset("99"),
        role_pubkeys={"guardian_2": _pubkey("12")},
        fallback_pubkey=_pubkey("aa"),
    )


def test_protocol_token_distribution_is_hash_bound_and_fail_closed() -> None:
    distribution = _distribution()

    validate_protocol_token_distribution_v0(distribution)
    assert distribution["production_security_claim"] is False
    assert distribution["tau_policy"]["host_computed_flags"]["runtime_mutation_disabled"] is True

    tampered = dict(distribution, initial_supply=1_000_001)
    with pytest.raises(ValueError, match="allocation_total"):
        validate_protocol_token_distribution_v0(tampered)


def test_active_participant_reward_claim_rejects_replay_and_tamper() -> None:
    distribution = _distribution()
    claim = build_active_participant_reward_claim_v0(
        distribution=distribution,
        program_id="lp_liquidity_provider_rewards",
        recipient_pubkey=_pubkey("aa"),
        receipt_kind="add_liquidity",
        receipt_hash=_asset("33"),
        amount=25,
        source_height=7,
        source_tx_index=0,
        source_tx_hash=_asset("44"),
        spent_by_program={},
        claimed_keys=set(),
        reward_source_balance=1_000,
    )

    validate_active_participant_reward_claim_v0(
        claim,
        distribution=distribution,
        spent_by_program={},
        claimed_keys=set(),
        reward_source_balance=1_000,
    )
    with pytest.raises(ValueError, match="receipt_not_previously_claimed"):
        validate_active_participant_reward_claim_v0(
            claim,
            distribution=distribution,
            spent_by_program={},
            claimed_keys={str(claim["claim_key"])},
            reward_source_balance=1_000,
        )

    tampered = dict(claim, amount=26)
    with pytest.raises(ValueError):
        validate_active_participant_reward_claim_v0(
            tampered,
            distribution=distribution,
            spent_by_program={},
            claimed_keys=set(),
            reward_source_balance=1_000,
        )


def test_tokenomics_buyback_burn_event_rejects_math_and_hash_tamper() -> None:
    distribution = _distribution()
    event = build_tokenomics_buyback_burn_event_v0(
        distribution=distribution,
        chain_id="tokenomics-test-chain",
        height=9,
        tx_index=0,
        tx_hash=_asset("55"),
        total_swap_fee=50,
        carry_before=0,
        source_balance_before=100,
        current_supply_before=1_000_000,
    )

    assert event["buyback_share_bps"] == LOCAL_TESTNET_BUYBACK_SHARE_BPS
    assert event["burn_amount"] == 10
    validate_tokenomics_buyback_burn_event_v0(event, distribution=distribution)

    tampered = dict(event, carry_after=1)
    with pytest.raises(ValueError, match="math|policy|hash"):
        validate_tokenomics_buyback_burn_event_v0(tampered, distribution=distribution)
