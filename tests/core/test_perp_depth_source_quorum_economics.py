from __future__ import annotations

from src.core.perp_depth_source_quorum_economics import (
    DepthSourceEconomicsRow,
    admitted_cap_overstatement_quote,
    depth_source_quorum_economics_payload_from_fields,
    min_quorum_downside_quote,
    verify_depth_source_quorum_economics_payload,
)

POLICY_HASH = "sha256:" + "77" * 32
OTHER_POLICY_HASH = "sha256:" + "78" * 32


def _rows(
    *,
    slashable_each_quote: int,
    count: int = 3,
    slash_fraction_bps: int = 10_000,
) -> tuple[DepthSourceEconomicsRow, ...]:
    return tuple(
        DepthSourceEconomicsRow(
            source_id=f"depth:source:{idx}",
            weight=1,
            bond_quote=slashable_each_quote,
            slash_fraction_bps=slash_fraction_bps,
            future_value_lost_quote=0,
        )
        for idx in range(count)
    )


def _payload(
    *,
    rows: tuple[DepthSourceEconomicsRow, ...] | None = None,
    quorum_threshold_weight: int = 2,
    true_depth_quote: int = 500_000,
    reported_depth_quote: int = 1_000_000,
    arbitrage_absorb_bps: int = 5_000,
    defect_gain_bps: int = 1_000,
    deterrence_margin_bps: int = 2_000,
    policy_hash: str = POLICY_HASH,
) -> dict[str, object]:
    return depth_source_quorum_economics_payload_from_fields(
        market_id="btc-usd",
        valid_from_epoch=1,
        valid_until_epoch=3,
        policy_hash=policy_hash,
        source_rows=rows if rows is not None else _rows(slashable_each_quote=15_000),
        quorum_threshold_weight=quorum_threshold_weight,
        true_depth_quote=true_depth_quote,
        reported_depth_quote=reported_depth_quote,
        arbitrage_absorb_bps=arbitrage_absorb_bps,
        defect_gain_bps=defect_gain_bps,
        deterrence_margin_bps=deterrence_margin_bps,
    )


def _verify(payload: dict[str, object]):
    return verify_depth_source_quorum_economics_payload(
        payload,
        expected_market_id="btc-usd",
        now_epoch=2,
        expected_policy_hash=POLICY_HASH,
    )


def test_unbonded_quorum_rejects_positive_overdepth_gain() -> None:
    verdict = _verify(_payload(rows=_rows(slashable_each_quote=0)))

    assert verdict.ok is False
    assert verdict.error == "quorum_downside_below_required"
    assert verdict.admitted_cap_overstatement_quote == 250_000
    assert verdict.attack_gain_quote == 25_000
    assert verdict.required_downside_quote == 30_000
    assert verdict.min_quorum_downside_quote == 0


def test_exact_boundary_accepts_when_min_quorum_downside_matches_required() -> None:
    verdict = _verify(_payload(rows=_rows(slashable_each_quote=15_000)))

    assert verdict.ok is True
    assert verdict.required_downside_quote == 30_000
    assert verdict.min_quorum_downside_quote == 30_000


def test_one_unit_below_boundary_rejects() -> None:
    verdict = _verify(_payload(rows=_rows(slashable_each_quote=14_999)))

    assert verdict.ok is False
    assert verdict.error == "quorum_downside_below_required"
    assert verdict.required_downside_quote == 30_000
    assert verdict.min_quorum_downside_quote == 29_998


def test_future_value_lost_counts_as_downside() -> None:
    rows = tuple(
        DepthSourceEconomicsRow(
            source_id=f"depth:source:{idx}",
            weight=1,
            bond_quote=5_000,
            slash_fraction_bps=10_000,
            future_value_lost_quote=10_000,
        )
        for idx in range(3)
    )

    verdict = _verify(_payload(rows=rows))

    assert verdict.ok is True
    assert verdict.min_quorum_downside_quote == 30_000


def test_min_quorum_downside_uses_weighted_dynamic_program_not_greedy() -> None:
    rows = (
        DepthSourceEconomicsRow(
            source_id="depth:source:a",
            weight=2,
            bond_quote=100,
            slash_fraction_bps=10_000,
            future_value_lost_quote=0,
        ),
        DepthSourceEconomicsRow(
            source_id="depth:source:b",
            weight=1,
            bond_quote=1,
            slash_fraction_bps=10_000,
            future_value_lost_quote=0,
        ),
        DepthSourceEconomicsRow(
            source_id="depth:source:c",
            weight=1,
            bond_quote=1,
            slash_fraction_bps=10_000,
            future_value_lost_quote=0,
        ),
    )

    assert min_quorum_downside_quote(rows, 2) == 2


def test_reported_depth_not_above_true_depth_has_zero_required_downside() -> None:
    verdict = _verify(
        _payload(
            rows=_rows(slashable_each_quote=0),
            true_depth_quote=1_000_000,
            reported_depth_quote=900_000,
        )
    )

    assert verdict.ok is True
    assert verdict.admitted_cap_overstatement_quote == 0
    assert verdict.required_downside_quote == 0


def test_wrong_policy_hash_rejects() -> None:
    verdict = verify_depth_source_quorum_economics_payload(
        _payload(policy_hash=OTHER_POLICY_HASH),
        expected_market_id="btc-usd",
        now_epoch=2,
        expected_policy_hash=POLICY_HASH,
    )

    assert verdict.ok is False
    assert verdict.error == "policy_hash mismatch"


def test_expected_reported_depth_mismatch_rejects_substitution() -> None:
    verdict = verify_depth_source_quorum_economics_payload(
        _payload(reported_depth_quote=900_000),
        expected_market_id="btc-usd",
        now_epoch=2,
        expected_policy_hash=POLICY_HASH,
        expected_reported_depth_quote=1_000_000,
    )

    assert verdict.ok is False
    assert verdict.error == "reported_depth_quote mismatch"


def test_expected_absorb_mismatch_rejects_substitution() -> None:
    verdict = verify_depth_source_quorum_economics_payload(
        _payload(arbitrage_absorb_bps=4_000),
        expected_market_id="btc-usd",
        now_epoch=2,
        expected_policy_hash=POLICY_HASH,
        expected_arbitrage_absorb_bps=5_000,
    )

    assert verdict.ok is False
    assert verdict.error == "arbitrage_absorb_bps mismatch"


def test_expected_source_ids_mismatch_rejects_substitution() -> None:
    verdict = verify_depth_source_quorum_economics_payload(
        _payload(rows=_rows(slashable_each_quote=15_000, count=2)),
        expected_market_id="btc-usd",
        now_epoch=2,
        expected_policy_hash=POLICY_HASH,
        expected_source_ids=(
            "depth:source:0",
            "depth:source:1",
            "depth:source:2",
        ),
    )

    assert verdict.ok is False
    assert verdict.error == "source_rows source_id mismatch"


def test_stale_epoch_rejects() -> None:
    verdict = verify_depth_source_quorum_economics_payload(
        _payload(),
        expected_market_id="btc-usd",
        now_epoch=4,
        expected_policy_hash=POLICY_HASH,
    )

    assert verdict.ok is False
    assert verdict.error == "epoch out of range"


def test_boolean_amount_rejects_at_payload_boundary() -> None:
    payload = _payload()
    payload["true_depth_quote"] = True

    verdict = _verify(payload)

    assert verdict.ok is False
    assert verdict.error == "true_depth_quote must be an int"


def test_duplicate_source_rejects() -> None:
    rows = (
        DepthSourceEconomicsRow(
            source_id="depth:source:a",
            weight=1,
            bond_quote=15_000,
            slash_fraction_bps=10_000,
            future_value_lost_quote=0,
        ),
        DepthSourceEconomicsRow(
            source_id="depth:source:a",
            weight=1,
            bond_quote=15_000,
            slash_fraction_bps=10_000,
            future_value_lost_quote=0,
        ),
    )

    try:
        _payload(rows=rows)
    except ValueError as exc:
        assert str(exc) == "source_rows source_id values must be unique"
    else:
        raise AssertionError("duplicate source rows should reject")


def test_admitted_cap_overstatement_matches_floor_caps() -> None:
    assert (
        admitted_cap_overstatement_quote(
            true_depth_quote=501,
            reported_depth_quote=1_001,
            arbitrage_absorb_bps=5_000,
        )
        == 250
    )
