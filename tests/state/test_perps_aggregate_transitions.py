from __future__ import annotations

import subprocess
import sys
from dataclasses import replace
from types import MappingProxyType
from typing import cast

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.state.perps_aggregate_transitions import (
    CanonicalPerpsMarketPatchV1,
    PerpsAggregateTransitionCodeV1,
    PerpsAggregateTransitionOkV1,
    PerpsAggregateTransitionRejectV1,
    PerpsMarketWriteV1,
    apply_canonical_perps_market_patch_v1,
    replace_perps_market_v1,
)
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionOkV1,
    apply_isolated_publish_clearing_price_v1,
)
from src.state.state_snapshot_values import (
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpMarketStateV1,
    CommittedPerpsStateV1,
)
from src.state.state_snapshots import snapshot_perps
from tests.state.test_committed_perps_readers import _committed_perps, _legacy_perps


def test_module_imports_without_prior_core_bootstrap() -> None:
    imported = subprocess.run(
        [sys.executable, "-c", "import src.state.perps_aggregate_transitions"],
        check=False,
        capture_output=True,
        text=True,
    )

    assert imported.returncode == 0, imported.stderr


def _published_market(
    pre: CommittedPerpsStateV1,
    *,
    price_e8: int = 105_000_000,
) -> CommittedPerpMarketStateV1:
    market = pre.get_market("isolated")
    assert type(market) is CommittedPerpMarketStateV1
    leaf = apply_isolated_publish_clearing_price_v1(
        market,
        price_e8=price_e8,
        mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        operator_authorized=True,
    )
    assert type(leaf) is IsolatedPerpTransitionOkV1
    return leaf.market


def test_exact_market_replacement_returns_one_owned_aggregate_candidate() -> None:
    pre = _committed_perps()
    original_entries = pre.market_entries
    original_market = cast(CommittedPerpMarketStateV1, pre.get_market("isolated"))
    replacement = _published_market(pre)

    result = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=replacement,
    )

    assert type(result) is PerpsAggregateTransitionOkV1
    assert type(result.state) is CommittedPerpsStateV1
    assert result.state.version == pre.version
    assert result.patch == CanonicalPerpsMarketPatchV1(
        (PerpsMarketWriteV1("isolated", original_market, replacement),)
    )
    assert result.state.market_entries == tuple(
        (market_id, replacement if market_id == "isolated" else market)
        for market_id, market in original_entries
    )
    assert pre.market_entries == original_entries
    assert pre.get_market("isolated") is original_market
    assert result.patch.writes[0].replacement is result.state.get_market("isolated")
    for market_id, market in original_entries:
        if market_id != "isolated":
            assert result.state.get_market(market_id) == market
            assert result.state.get_market(market_id) is not market


@pytest.mark.parametrize("market_id", ("isolated", "ch2p", "ch3p", "chnp"))
def test_market_replacement_matches_legacy_snapshot_for_every_variant(
    market_id: str,
) -> None:
    legacy_pre = _legacy_perps()
    pre = snapshot_perps(legacy_pre)
    assert type(pre) is CommittedPerpsStateV1
    current = pre.get_market(market_id)
    assert current is not None
    replacement = replace(current, quote_asset="uUSD")

    legacy_expected = _legacy_perps()
    legacy_expected.markets[market_id] = replace(
        legacy_expected.markets[market_id],
        quote_asset="uUSD",
    )
    expected = snapshot_perps(legacy_expected)
    result = replace_perps_market_v1(
        pre,
        market_id=market_id,
        replacement=replacement,
    )

    assert type(result) is PerpsAggregateTransitionOkV1
    assert result.state == expected
    assert result.patch.writes[0].replacement is result.state.get_market(market_id)


def test_v4_isolated_replacement_preserves_version_compatibility() -> None:
    legacy = _legacy_perps()
    isolated = legacy.markets["isolated"]
    pre = snapshot_perps(
        PerpsState(
            version=PERPS_STATE_VERSION_V4,
            markets={"isolated": isolated},
        )
    )
    assert type(pre) is CommittedPerpsStateV1
    current = pre.get_market("isolated")
    assert type(current) is CommittedPerpMarketStateV1

    accepted = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=replace(current, quote_asset="uUSD"),
    )
    wrong_variant = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=_committed_perps().get_market("ch2p"),
    )

    assert type(accepted) is PerpsAggregateTransitionOkV1
    assert accepted.state.version == PERPS_STATE_VERSION_V4
    assert wrong_variant == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.MARKET_VARIANT_MISMATCH,
        ("replacement",),
    )


def test_result_constructor_enforces_same_candidate_identity() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    patch = CanonicalPerpsMarketPatchV1(
        (
            PerpsMarketWriteV1(
                "isolated",
                cast(CommittedPerpMarketStateV1, pre.get_market("isolated")),
                replacement,
            ),
        )
    )

    with pytest.raises(
        ValueError,
        match="patch does not bind the returned candidate",
    ):
        PerpsAggregateTransitionOkV1(pre, patch)


def test_market_replacement_patch_replays_and_rejects_when_stale() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    built = replace_perps_market_v1(pre, market_id="isolated", replacement=replacement)
    assert type(built) is PerpsAggregateTransitionOkV1

    replay = apply_canonical_perps_market_patch_v1(pre, built.patch)
    stale = apply_canonical_perps_market_patch_v1(built.state, built.patch)

    assert replay == built
    assert stale == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.EXPECTED_OLD_MISMATCH,
        ("writes", 0, "expected"),
    )
    assert not hasattr(stale, "state")
    assert not hasattr(stale, "patch")


def test_market_replacement_rejects_missing_and_noop_without_output() -> None:
    pre = _committed_perps()
    current = cast(CommittedPerpMarketStateV1, pre.get_market("isolated"))

    missing = replace_perps_market_v1(
        pre,
        market_id="missing",
        replacement=current,
    )
    noop = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=current,
    )

    assert missing == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.MARKET_NOT_FOUND,
        ("market_id",),
    )
    assert noop == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.NO_OP_WRITE,
        ("replacement",),
    )
    for reject in (missing, noop):
        assert not hasattr(reject, "state")
        assert not hasattr(reject, "patch")
        assert not hasattr(reject, "effects")
        assert not hasattr(reject, "receipt")
        assert not hasattr(reject, "nonce")
        assert not hasattr(reject, "outbox")


def test_market_replacement_rejects_variant_change_before_candidate_construction() -> None:
    pre = _committed_perps()
    wrong_variant = pre.get_market("ch2p")
    assert type(wrong_variant) is CommittedPerpClearinghouse2pMarketStateV1

    result = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=wrong_variant,
    )

    assert result == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.MARKET_VARIANT_MISMATCH,
        ("replacement",),
    )
    assert pre.get_market("isolated") is not wrong_variant


def test_market_replacement_rejects_inexact_values_before_behavior() -> None:
    pre = _committed_perps()
    called = False

    class HostileString(str):
        def encode(self, *_args: object, **_kwargs: object) -> bytes:
            nonlocal called
            called = True
            raise AssertionError("inexact market id behavior executed")

    class HostileMarket(CommittedPerpMarketStateV1):
        def __eq__(self, _other: object) -> bool:
            nonlocal called
            called = True
            raise AssertionError("inexact market behavior executed")

    bad_id = replace_perps_market_v1(
        pre,
        market_id=HostileString("isolated"),
        replacement=cast(CommittedPerpMarketStateV1, object()),
    )
    bad_market = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=cast(CommittedPerpMarketStateV1, object.__new__(HostileMarket)),
    )

    assert bad_id == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE,
        ("market_id",),
    )
    assert bad_market == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE,
        ("replacement",),
    )
    assert called is False


def test_market_replacement_validates_prestate_before_command_fields() -> None:
    pre = _committed_perps()
    object.__setattr__(pre, "version", True)

    result = replace_perps_market_v1(
        pre,
        market_id=cast(str, object()),
        replacement=cast(CommittedPerpMarketStateV1, object()),
    )

    assert result == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.INVALID_PRESTATE,
        ("state", "version"),
    )


def test_market_patch_rejects_an_expected_value_from_another_prestate() -> None:
    pre = _committed_perps()
    expected_elsewhere = _published_market(pre, price_e8=95_000_000)
    replacement = _published_market(pre, price_e8=105_000_000)
    patch = CanonicalPerpsMarketPatchV1(
        (
            PerpsMarketWriteV1(
                "isolated",
                expected_elsewhere,
                replacement,
            ),
        )
    )

    result = apply_canonical_perps_market_patch_v1(pre, patch)

    assert result == PerpsAggregateTransitionRejectV1(
        PerpsAggregateTransitionCodeV1.EXPECTED_OLD_MISMATCH,
        ("writes", 0, "expected"),
    )


def test_market_patch_result_is_deterministic_for_equal_exact_inputs() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)

    first = replace_perps_market_v1(pre, market_id="isolated", replacement=replacement)
    second = replace_perps_market_v1(pre, market_id="isolated", replacement=replacement)

    assert first == second


def test_market_replacement_rejects_market_map_entry_index_divergence() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    original_entries = pre.market_entries
    object.__setattr__(
        pre.markets,
        "_entries",
        tuple(
            ("tampered", market) if market_id == "isolated" else (market_id, market)
            for market_id, market in original_entries
        ),
    )

    result = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=replacement,
    )

    assert type(result) is PerpsAggregateTransitionRejectV1
    assert result.code is PerpsAggregateTransitionCodeV1.INVALID_PRESTATE
    assert result.path[:1] == ("state",)
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")


def test_market_replacement_rejects_nested_market_index_divergence() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    market = pre.get_market("isolated")
    assert type(market) is CommittedPerpMarketStateV1
    object.__setattr__(market.global_state, "_index", MappingProxyType({}))

    result = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=replacement,
    )

    assert type(result) is PerpsAggregateTransitionRejectV1
    assert result.code is PerpsAggregateTransitionCodeV1.INVALID_PRESTATE
    assert result.path[:1] == ("state",)
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")


def test_market_patch_rejects_corrupt_nested_replacement_without_output() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    current = pre.get_market("isolated")
    assert type(current) is CommittedPerpMarketStateV1
    patch = CanonicalPerpsMarketPatchV1((PerpsMarketWriteV1("isolated", current, replacement),))
    object.__setattr__(replacement.global_state, "_index", MappingProxyType({}))

    result = apply_canonical_perps_market_patch_v1(pre, patch)

    assert type(result) is PerpsAggregateTransitionRejectV1
    assert result.code is PerpsAggregateTransitionCodeV1.INVALID_PATCH
    assert result.path[:3] == ("patch", "writes", 0)
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")


def test_market_replacement_rejects_corrupt_candidate_before_patch_escape() -> None:
    pre = _committed_perps()
    replacement = _published_market(pre)
    object.__setattr__(replacement.global_state, "_index", MappingProxyType({}))

    result = replace_perps_market_v1(
        pre,
        market_id="isolated",
        replacement=replacement,
    )

    assert type(result) is PerpsAggregateTransitionRejectV1
    assert result.code is PerpsAggregateTransitionCodeV1.INVALID_MARKET
    assert result.path[:1] == ("replacement",)
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")
