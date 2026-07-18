from __future__ import annotations

from itertools import product

from src.core.zusd_generic_token_admission import (
    GenericTokenAction,
    GenericTokenAdmissionCode,
)
from src.integration.zusd_generic_token_admission_bridge import (
    evaluate_live_generic_token_writer_admission,
    generic_token_admission_reject_code,
)
from src.integration.zusd_monetary_bridge import stability_pool_pubkey
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id


def test_live_bridge_rejects_every_generic_canonical_zusd_supply_change() -> None:
    chain_id = "tau-live-admission-supply"
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)

    for action, recipient in product(
        (GenericTokenAction.MINT, GenericTokenAction.BURN),
        (None, "0x" + "31" * 48),
    ):
        decision = evaluate_live_generic_token_writer_admission(
            chain_id=chain_id,
            canonical_zusd_asset=zusd_asset,
            action=action,
            asset=zusd_asset,
            recipient_pubkey=recipient,
        )
        expected = (
            GenericTokenAdmissionCode.CANONICAL_ZUSD_MINT_REQUIRES_MONETARY_AUTHORITY
            if action is GenericTokenAction.MINT
            else GenericTokenAdmissionCode.CANONICAL_ZUSD_BURN_REQUIRES_MONETARY_AUTHORITY
        )
        assert decision.code is expected
        assert generic_token_admission_reject_code(decision) == expected.name.lower()


def test_live_bridge_binds_chain_specific_stability_pool_custody() -> None:
    chain_id = "tau-live-admission-sp"
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)

    rejected = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=zusd_asset,
        action=GenericTokenAction.TRANSFER,
        asset=zusd_asset,
        recipient_pubkey=stability_pool_pubkey(chain_id=chain_id),
    )
    admitted_other_chain = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=zusd_asset,
        action=GenericTokenAction.TRANSFER,
        asset=zusd_asset,
        recipient_pubkey=stability_pool_pubkey(chain_id="other-chain"),
    )

    assert rejected.code is (
        GenericTokenAdmissionCode.CANONICAL_ZUSD_RESERVED_CUSTODY_REQUIRES_MONETARY_AUTHORITY
    )
    assert admitted_other_chain.code is GenericTokenAdmissionCode.ADMITTED


def test_live_bridge_preserves_ordinary_transfer_and_other_asset_semantics() -> None:
    chain_id = "tau-live-admission-ordinary"
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    ordinary = "0x" + "41" * 48

    ordinary_zusd = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=zusd_asset,
        action="transfer",
        asset=zusd_asset,
        recipient_pubkey=ordinary,
    )
    other_asset_mint = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=zusd_asset,
        action="mint",
        asset="0x" + "42" * 32,
        recipient_pubkey=ordinary,
    )

    assert ordinary_zusd.code is GenericTokenAdmissionCode.ADMITTED
    assert generic_token_admission_reject_code(ordinary_zusd) is None
    assert other_asset_mint.code is GenericTokenAdmissionCode.ADMITTED
