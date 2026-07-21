from __future__ import annotations

from typing import Any

import pytest

from src.integration import perp_engine


ACCOUNT_A = "0x" + "11" * 48
ACCOUNT_B = "0x" + "22" * 48
ACCOUNT_C = "0x" + "33" * 48
QUOTE_ASSET = "0x" + "44" * 32


def _ctx() -> perp_engine._PerpApplyCtx:
    return perp_engine._PerpApplyCtx(
        config=perp_engine.PerpEngineConfig(
            require_oracle_adapter_for_clearinghouse_settle_epoch=True,
            require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        ),
        balances=perp_engine.BalanceTable(),
        nonces=perp_engine.NonceTable(),
        markets={},
        effects=[],
        tx_sender_pubkey=ACCOUNT_A,
        block_timestamp=0,
        perps_version=5,
    )


def _settle_op(*, version: str, market_id: str) -> perp_engine.PerpOp:
    return perp_engine.PerpOp(
        market_id=market_id,
        action="settle_epoch",
        version=version,
        data={
            "module": perp_engine.PERP_OP_MODULE,
            "version": version,
            "market_id": market_id,
            "action": "settle_epoch",
            "oracle_adapter_bridge": {"schema": "test.bridge.v1"},
            "oracle_authorization": {"schema": "test.authorization.v1"},
        },
    )


@pytest.mark.parametrize("shape", ["ch2p", "ch3p"])
def test_fixed_clearinghouse_settlement_uses_shared_typed_authorization(
    monkeypatch: pytest.MonkeyPatch,
    shape: str,
) -> None:
    observed: list[Any] = []

    monkeypatch.setattr(perp_engine, "_require_oracle_adapter_bridge", lambda _requirement: None)

    def _capture(request: Any) -> None:
        observed.append(request)
        return None

    monkeypatch.setattr(
        perp_engine,
        "_check_clearinghouse_settle_oracle_authorization",
        _capture,
    )
    monkeypatch.setattr(
        perp_engine,
        "_commit_clearinghouse_kernel_step",
        lambda _ctx, _commit: None,
    )

    ctx = _ctx()
    if shape == "ch2p":
        market_id = "perp:ch2p:oracle-parity"
        market = perp_engine.PerpClearinghouse2pMarketState(
            quote_asset=QUOTE_ASSET,
            account_a_pubkey=ACCOUNT_A,
            account_b_pubkey=ACCOUNT_B,
            state=perp_engine._ch2p_init_state_dict(),
        )
        error = perp_engine._apply_ch2p_settle_epoch(
            ctx,
            i=0,
            op=_settle_op(version=perp_engine.PERP_OP_VERSION_CH2P_V1_0, market_id=market_id),
            ch2p_market=market,
        )
        expected_kind = "clearinghouse_2p_v1"
        expected_participants = (ACCOUNT_A, ACCOUNT_B)
    else:
        market_id = "perp:ch3p:oracle-parity"
        market = perp_engine.PerpClearinghouse3pTransferMarketState(
            quote_asset=QUOTE_ASSET,
            account_a_pubkey=ACCOUNT_A,
            account_b_pubkey=ACCOUNT_B,
            account_c_pubkey=ACCOUNT_C,
            state=perp_engine._ch3p_init_state_dict(),
        )
        error = perp_engine._apply_ch3p_settle_epoch(
            ctx,
            i=0,
            op=_settle_op(version=perp_engine.PERP_OP_VERSION_CH3P_V1_1, market_id=market_id),
            ch3p_market=market,
        )
        expected_kind = "clearinghouse_3p_transfer_v1"
        expected_participants = (ACCOUNT_A, ACCOUNT_B, ACCOUNT_C)

    assert error is None
    assert len(observed) == 1
    request = observed[0]
    assert request.market_kind == expected_kind
    assert request.market_id == market_id
    assert request.participant_pubkeys == expected_participants
    assert request.data["oracle_authorization"] == {"schema": "test.authorization.v1"}


def test_shared_clearinghouse_authorization_rejects_missing_value() -> None:
    request = perp_engine._ClearinghouseSettleOracleAuthorizationRequest(
        config=perp_engine.PerpEngineConfig(
            require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        ),
        data={"oracle_adapter_bridge": {"schema": "test.bridge.v1"}},
        market_id="perp:ch2p:missing-auth",
        market_kind="clearinghouse_2p_v1",
        quote_asset=QUOTE_ASSET,
        state={"clearing_price_e8": 100_000_000},
        participant_pubkeys=(ACCOUNT_A, ACCOUNT_B),
    )

    assert (
        perp_engine._check_clearinghouse_settle_oracle_authorization(request)
        == "clearinghouse_settle_oracle_authorization_required"
    )
