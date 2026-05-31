from __future__ import annotations

import pytest

from src.integration.perp_engine import parse_perp_ops


def _op(market_id: str, *, version: str) -> dict[str, object]:
    return {
        "module": "TauPerp",
        "version": version,
        "market_id": market_id,
        "action": "advance_epoch",
        "delta": 1,
    }


def test_parse_perp_ops_rejects_ch2p_version_without_ch2p_prefix() -> None:
    with pytest.raises(ValueError, match="clearinghouse markets must start with 'perp:ch2p:'"):
        parse_perp_ops({"5": [_op("perp:demo", version="1.0")]})


def test_parse_perp_ops_rejects_ch3p_version_without_ch3p_prefix() -> None:
    with pytest.raises(ValueError, match="clearinghouse markets must start with 'perp:ch3p:'"):
        parse_perp_ops({"5": [_op("perp:demo", version="1.1")]})


def test_parse_perp_ops_rejects_isolated_version_with_clearinghouse_prefix() -> None:
    with pytest.raises(ValueError, match="isolated markets cannot start with clearinghouse prefixes"):
        parse_perp_ops({"5": [_op("perp:ch2p:bad", version="0.1")]})


def test_parse_perp_ops_accepts_matching_version_and_prefix_postures() -> None:
    parsed = parse_perp_ops(
        {
            "5": [
                _op("perp:demo", version="0.1"),
                _op("perp:ch2p:demo", version="1.0"),
                _op("perp:ch3p:demo", version="1.1"),
            ]
        }
    )
    assert [op.market_id for op in parsed] == ["perp:demo", "perp:ch2p:demo", "perp:ch3p:demo"]
