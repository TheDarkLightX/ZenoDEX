from __future__ import annotations

from itertools import product
from typing import Any, cast

import pytest

from src.core.settlement import LPDelta, Settlement
from src.integration.lp_position_age_gate import (
    LPDurationRiskPolicy,
    apply_lp_mint_timestamps_after_settlement,
    validate_lp_settlement_age_gate,
)
from src.state.lp import LPTable
from src.state.lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationRiskPolicyV1,
    LPDurationTransitionCodeV1,
    LPDurationTransitionOkV1,
    LPDurationTransitionRejectV1,
    apply_guarded_lp_position_events_v1,
    apply_lp_position_events_v1,
)
from src.state.state_snapshot_values import DEX_LP_AMOUNT_MAX
from src.state.state_snapshots import snapshot_lp_table
from src.state.state_transitions import (
    LPPositionPatchApplyOkV1,
    apply_canonical_lp_position_patch_v1,
)


def _policy() -> LPDurationRiskPolicyV1:
    return LPDurationRiskPolicyV1(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=86_400,
        multiplier=2,
        max_churn_tier=5,
    )


def _legacy_policy() -> LPDurationRiskPolicy:
    return LPDurationRiskPolicy(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=86_400,
        multiplier=2,
        max_churn_tier=5,
    )


def _legacy_lp(
    *,
    owner: str = "owner",
    pool_id: str = "pool",
    balance: int = 10,
    last_mint: int | None = 100,
) -> LPTable:
    state = LPTable()
    state.set(owner, pool_id, balance)
    if last_mint is not None:
        state.set_last_mint_timestamp(owner, pool_id, last_mint)
    return state


def _legacy_lp_with_metadata(
    *,
    last_mint: int | None,
    last_remove: int | None,
    churn_tier: int,
    last_churn_update: int | None,
) -> LPTable:
    state = _legacy_lp(balance=10, last_mint=last_mint)
    if last_remove is not None:
        state.set_last_remove_timestamp("owner", "pool", last_remove)
    state.set_churn_tier("owner", "pool", churn_tier)
    if last_churn_update is not None:
        state.set_last_churn_update_timestamp("owner", "pool", last_churn_update)
    return state


def _settlement(
    *,
    owner: str,
    pool_id: str,
    delta_add: int,
    delta_sub: int,
) -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[
            LPDelta(
                pubkey=owner,
                pool_id=pool_id,
                delta_add=delta_add,
                delta_sub=delta_sub,
            )
        ],
    )


def _apply_mounted_lp_event(
    state: LPTable,
    settlement: Settlement,
    *,
    now: int,
    policy: LPDurationRiskPolicy | None,
) -> None:
    delta = settlement.lp_deltas[0]
    net_delta = delta.delta_add - delta.delta_sub
    if net_delta != 0:
        state.add(delta.pubkey, delta.pool_id, net_delta)
    assert (
        apply_lp_mint_timestamps_after_settlement(
            lp_balances=state,
            settlement=settlement,
            block_timestamp=now,
            duration_risk_policy=policy,
        )
        is None
    )


def test_exact_add_returns_one_replayable_position_patch_without_mutating_prestate() -> None:
    owner = "owner"
    pool_id = "pool"
    pre = snapshot_lp_table(_legacy_lp(owner=owner, pool_id=pool_id))

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1((owner, pool_id), 5, 0),),
        now=550,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.patch is not None
    assert pre.get_last_mint_timestamp(owner, pool_id) == 100
    assert pre.get_churn_tier(owner, pool_id) == 0
    assert result.state.get(owner, pool_id) == 15
    assert result.state.get_last_mint_timestamp(owner, pool_id) == 550
    assert result.state.get_churn_tier(owner, pool_id) == 1
    assert result.state.get_last_churn_update_timestamp(owner, pool_id) == 550

    replayed = apply_canonical_lp_position_patch_v1(pre, result.patch)
    assert type(replayed) is LPPositionPatchApplyOkV1
    assert replayed.state == result.state


def test_exact_remove_then_reentry_matches_mounted_legacy_metadata_semantics() -> None:
    owner = "owner"
    pool_id = "pool"
    legacy = _legacy_lp(owner=owner, pool_id=pool_id)
    exact = snapshot_lp_table(_legacy_lp(owner=owner, pool_id=pool_id))

    remove = _settlement(owner=owner, pool_id=pool_id, delta_add=0, delta_sub=5)
    _apply_mounted_lp_event(
        legacy,
        remove,
        now=500,
        policy=_legacy_policy(),
    )
    exact_remove = apply_lp_position_events_v1(
        exact,
        (LPDurationEventV1((owner, pool_id), 0, 5),),
        now=500,
        policy=_policy(),
    )
    assert type(exact_remove) is LPDurationTransitionOkV1
    assert exact_remove.state == snapshot_lp_table(legacy)

    add = _settlement(owner=owner, pool_id=pool_id, delta_add=5, delta_sub=0)
    _apply_mounted_lp_event(
        legacy,
        add,
        now=550,
        policy=_legacy_policy(),
    )
    exact_add = apply_lp_position_events_v1(
        exact_remove.state,
        (LPDurationEventV1((owner, pool_id), 5, 0),),
        now=550,
        policy=_policy(),
    )
    assert type(exact_add) is LPDurationTransitionOkV1
    assert exact_add.state == snapshot_lp_table(legacy)


def test_exact_valid_metadata_grid_matches_mounted_legacy_semantics() -> None:
    policy_pairs = ((None, None), (_legacy_policy(), _policy()))
    event_shapes = ((1, 0), (0, 1), (1, 1))

    for last_mint, last_remove, churn_tier, last_churn_update in product(
        (None, 5),
        (None, 4),
        (0, 2),
        (None, 3),
    ):
        for legacy_policy, exact_policy in policy_pairs:
            for delta_add, delta_sub in event_shapes:
                if legacy_policy is not None and delta_add > 0 and delta_sub > 0:
                    continue
                legacy = _legacy_lp_with_metadata(
                    last_mint=last_mint,
                    last_remove=last_remove,
                    churn_tier=churn_tier,
                    last_churn_update=last_churn_update,
                )
                exact = snapshot_lp_table(legacy)
                settlement = _settlement(
                    owner="owner",
                    pool_id="pool",
                    delta_add=delta_add,
                    delta_sub=delta_sub,
                )

                _apply_mounted_lp_event(
                    legacy,
                    settlement,
                    now=10,
                    policy=legacy_policy,
                )
                result = apply_lp_position_events_v1(
                    exact,
                    (
                        LPDurationEventV1(
                            ("owner", "pool"),
                            delta_add,
                            delta_sub,
                        ),
                    ),
                    now=10,
                    policy=exact_policy,
                )

                assert type(result) is LPDurationTransitionOkV1, (
                    last_mint,
                    last_remove,
                    churn_tier,
                    last_churn_update,
                    delta_add,
                    delta_sub,
                    exact_policy,
                )
                assert result.state == snapshot_lp_table(legacy)


def test_exact_add_without_progressive_policy_only_sets_last_mint() -> None:
    owner = "owner"
    pool_id = "pool"
    pre = snapshot_lp_table(_legacy_lp(owner=owner, pool_id=pool_id))

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1((owner, pool_id), 1, 0),),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state.get(owner, pool_id) == 11
    assert result.state.get_last_mint_timestamp(owner, pool_id) == 42
    assert result.state.get_churn_tier(owner, pool_id) == 0
    assert result.state.get_last_churn_update_timestamp(owner, pool_id) is None


def test_exact_first_mint_from_zero_matches_mounted_transition() -> None:
    legacy = _legacy_lp(balance=0, last_mint=None)
    exact = snapshot_lp_table(_legacy_lp(balance=0, last_mint=None))
    settlement = _settlement(
        owner="owner",
        pool_id="pool",
        delta_add=5,
        delta_sub=0,
    )

    _apply_mounted_lp_event(
        legacy,
        settlement,
        now=42,
        policy=_legacy_policy(),
    )
    result = apply_lp_position_events_v1(
        exact,
        (LPDurationEventV1(("owner", "pool"), 5, 0),),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state == snapshot_lp_table(legacy)


def test_exact_full_remove_clears_mint_and_preserves_remove_metadata() -> None:
    legacy = _legacy_lp(balance=5, last_mint=1)
    exact = snapshot_lp_table(_legacy_lp(balance=5, last_mint=1))
    settlement = _settlement(
        owner="owner",
        pool_id="pool",
        delta_add=0,
        delta_sub=5,
    )

    _apply_mounted_lp_event(
        legacy,
        settlement,
        now=42,
        policy=_legacy_policy(),
    )
    result = apply_lp_position_events_v1(
        exact,
        (LPDurationEventV1(("owner", "pool"), 0, 5),),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state == snapshot_lp_table(legacy)
    assert result.state.get("owner", "pool") == 0
    assert result.state.get_last_mint_timestamp("owner", "pool") is None
    assert result.state.get_last_remove_timestamp("owner", "pool") == 42


def test_empty_event_batch_is_an_exact_noop() -> None:
    pre = snapshot_lp_table(_legacy_lp())

    result = apply_lp_position_events_v1(
        pre,
        (),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state == pre
    assert result.patch is None


@pytest.mark.parametrize(
    ("events", "code", "path"),
    (
        (
            cast(Any, []),
            LPDurationTransitionCodeV1.WRONG_EXACT_TYPE,
            ("events",),
        ),
        (
            (
                LPDurationEventV1(("owner", "pool"), 1, 0),
                LPDurationEventV1(("owner", "pool"), 1, 0),
            ),
            LPDurationTransitionCodeV1.DUPLICATE_EVENT,
            ("events", 1, "key"),
        ),
        (
            (
                LPDurationEventV1(("owner-b", "pool"), 1, 0),
                LPDurationEventV1(("owner-a", "pool"), 1, 0),
            ),
            LPDurationTransitionCodeV1.NONCANONICAL_EVENTS,
            ("events", 1, "key"),
        ),
    ),
)
def test_malformed_event_families_reject_without_candidate(
    events: object,
    code: LPDurationTransitionCodeV1,
    path: tuple[str | int, ...],
) -> None:
    pre = snapshot_lp_table(_legacy_lp())

    result = apply_lp_position_events_v1(
        pre,
        cast(Any, events),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is code
    assert result.path == path
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")
    assert pre == snapshot_lp_table(_legacy_lp())


def test_same_batch_add_remove_rejects_when_progressive_policy_is_active() -> None:
    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (LPDurationEventV1(("owner", "pool"), 1, 1),),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.SAME_BATCH_ADD_REMOVE
    assert result.path == ("events", 0)


def test_same_batch_add_remove_without_policy_matches_mounted_metadata_semantics() -> None:
    owner = "owner"
    pool_id = "pool"
    legacy = _legacy_lp(owner=owner, pool_id=pool_id)
    exact = snapshot_lp_table(_legacy_lp(owner=owner, pool_id=pool_id))
    settlement = _settlement(
        owner=owner,
        pool_id=pool_id,
        delta_add=1,
        delta_sub=1,
    )

    _apply_mounted_lp_event(
        legacy,
        settlement,
        now=500,
        policy=None,
    )
    result = apply_lp_position_events_v1(
        exact,
        (LPDurationEventV1((owner, pool_id), 1, 1),),
        now=500,
        policy=None,
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state == snapshot_lp_table(legacy)


def test_same_batch_zero_balance_matches_mounted_rejection() -> None:
    legacy = _legacy_lp(balance=0, last_mint=None)
    settlement = _settlement(
        owner="owner",
        pool_id="pool",
        delta_add=1,
        delta_sub=1,
    )
    pre = snapshot_lp_table(_legacy_lp(balance=0, last_mint=None))

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 1, 1),),
        now=500,
        policy=None,
    )

    assert (
        apply_lp_mint_timestamps_after_settlement(
            lp_balances=legacy,
            settlement=settlement,
            block_timestamp=500,
            duration_risk_policy=None,
        )
        == "lp_duration_risk_update_failed: cannot set LP mint timestamp for an empty balance"
    )
    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.DOMAIN_INVARIANT
    assert result.path == ("events", 0, "balance")
    assert pre == snapshot_lp_table(_legacy_lp(balance=0, last_mint=None))


def test_constructor_bypass_empty_event_is_revalidated_and_rejected() -> None:
    event = object.__new__(LPDurationEventV1)
    object.__setattr__(event, "key", ("owner", "pool"))
    object.__setattr__(event, "delta_add", 0)
    object.__setattr__(event, "delta_sub", 0)

    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (event,),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.NONCANONICAL_EVENTS
    assert result.path == ("events", 0)


def test_constructor_bypass_oversized_delta_is_revalidated_and_rejected() -> None:
    event = object.__new__(LPDurationEventV1)
    object.__setattr__(event, "key", ("owner", "pool"))
    object.__setattr__(event, "delta_add", DEX_LP_AMOUNT_MAX + 1)
    object.__setattr__(event, "delta_sub", 0)

    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (event,),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.OUT_OF_RANGE
    assert result.path == ("events", 0)


@pytest.mark.parametrize(
    ("key", "code"),
    (
        (("", "pool"), LPDurationTransitionCodeV1.NONCANONICAL_KEY),
        (("a" * 4_097, "pool"), LPDurationTransitionCodeV1.ITEM_LIMIT),
    ),
)
def test_constructor_bypass_invalid_keys_preserve_stable_rejection_family(
    key: tuple[str, str],
    code: LPDurationTransitionCodeV1,
) -> None:
    event = object.__new__(LPDurationEventV1)
    object.__setattr__(event, "key", key)
    object.__setattr__(event, "delta_add", 1)
    object.__setattr__(event, "delta_sub", 0)

    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (event,),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is code
    assert result.path == ("events", 0, "key")


def test_aggregate_event_bytes_are_bounded_before_position_updates() -> None:
    events = tuple(
        LPDurationEventV1(
            (f"{index:04d}" + ("a" * 4_092), "p"),
            1,
            0,
        )
        for index in range(1_000)
    )

    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        events,
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.BYTE_LIMIT
    assert result.path == ("events",)


def test_corrupt_exact_policy_is_revalidated_before_use() -> None:
    policy = _policy()
    object.__setattr__(policy, "multiplier", True)

    result = apply_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (LPDurationEventV1(("owner", "pool"), 1, 0),),
        now=42,
        policy=policy,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.WRONG_EXACT_TYPE
    assert result.path == ("policy",)


def test_policy_constructor_rejects_boolean_integer_alias() -> None:
    with pytest.raises(TypeError, match="base_age_seconds must be an exact integer"):
        LPDurationRiskPolicyV1(base_age_seconds=True)


def test_future_churn_update_rejects_without_candidate() -> None:
    legacy = _legacy_lp(balance=10, last_mint=1)
    legacy.set_churn_tier("owner", "pool", 1)
    legacy.set_last_churn_update_timestamp("owner", "pool", 100)
    pre = snapshot_lp_table(legacy)

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 1, 0),),
        now=42,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.DOMAIN_INVARIANT
    assert result.path == ("events", 0, "last_churn_update_timestamp")
    assert pre == snapshot_lp_table(legacy)


def test_lp_position_underflow_rejects_without_candidate() -> None:
    pre = snapshot_lp_table(_legacy_lp(balance=0, last_mint=None))

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.OUT_OF_RANGE
    assert result.path == ("events", 0, "balance")


def test_lp_position_overflow_rejects_without_candidate() -> None:
    pre = snapshot_lp_table(
        _legacy_lp(
            balance=DEX_LP_AMOUNT_MAX,
            last_mint=None,
        )
    )

    result = apply_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 1, 0),),
        now=42,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.OUT_OF_RANGE
    assert result.path == ("events", 0, "balance")
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")


def test_exact_age_guard_accepts_boundary_and_returns_lifecycle_candidate() -> None:
    pre = snapshot_lp_table(_legacy_lp(balance=10, last_mint=8))
    events = (LPDurationEventV1(("owner", "pool"), 0, 1),)

    guarded = apply_guarded_lp_position_events_v1(
        pre,
        events,
        now=10,
        min_age_seconds=2,
        policy=None,
    )
    lifecycle = apply_lp_position_events_v1(
        pre,
        events,
        now=10,
        policy=None,
    )

    assert type(guarded) is LPDurationTransitionOkV1
    assert guarded == lifecycle
    assert pre.get("owner", "pool") == 10


def test_exact_age_guard_rejects_stale_by_one_without_candidate() -> None:
    pre = snapshot_lp_table(_legacy_lp(balance=10, last_mint=9))

    result = apply_guarded_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=2,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.POSITION_LOCKED
    assert result.path == ("events", 0, "last_mint_timestamp")
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")
    assert pre == snapshot_lp_table(_legacy_lp(balance=10, last_mint=9))


def test_exact_age_guard_rejects_missing_and_future_mint_metadata() -> None:
    missing = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp(balance=10, last_mint=None)),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=1,
        policy=None,
    )
    future = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp(balance=10, last_mint=11)),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=1,
        policy=None,
    )

    assert type(missing) is LPDurationTransitionRejectV1
    assert missing.code is LPDurationTransitionCodeV1.AGE_METADATA_MISSING
    assert missing.path == ("events", 0, "last_mint_timestamp")
    assert type(future) is LPDurationTransitionRejectV1
    assert future.code is LPDurationTransitionCodeV1.MINT_TIMESTAMP_IN_FUTURE
    assert future.path == ("events", 0, "last_mint_timestamp")


def test_exact_age_guard_same_batch_precedes_candidate_failure_when_enabled() -> None:
    pre = snapshot_lp_table(_legacy_lp(balance=0, last_mint=None))

    result = apply_guarded_lp_position_events_v1(
        pre,
        (LPDurationEventV1(("owner", "pool"), 1, 1),),
        now=10,
        min_age_seconds=1,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.SAME_BATCH_ADD_REMOVE
    assert result.path == ("events", 0)
    assert not hasattr(result, "state")


def test_exact_age_guard_same_batch_precedes_all_remove_age_errors() -> None:
    legacy = LPTable()
    legacy.set("owner-a", "pool", 10)
    legacy.set("owner-b", "pool", 10)

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (
            LPDurationEventV1(("owner-a", "pool"), 0, 1),
            LPDurationEventV1(("owner-b", "pool"), 1, 1),
        ),
        now=10,
        min_age_seconds=1,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.SAME_BATCH_ADD_REMOVE
    assert result.path == ("events", 1)


def test_exact_age_guard_selects_first_canonical_remove_error() -> None:
    legacy = LPTable()
    legacy.set("owner-a", "pool", 10)
    legacy.set("owner-b", "pool", 10)
    legacy.set_last_mint_timestamp("owner-b", "pool", 11)

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (
            LPDurationEventV1(("owner-a", "pool"), 0, 1),
            LPDurationEventV1(("owner-b", "pool"), 0, 1),
        ),
        now=10,
        min_age_seconds=1,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.AGE_METADATA_MISSING
    assert result.path == ("events", 0, "last_mint_timestamp")


def test_exact_progressive_age_guard_matches_mounted_policy_grid() -> None:
    legacy_policy = _legacy_policy()
    exact_policy = _policy()
    events = (LPDurationEventV1(("owner", "pool"), 0, 1),)

    for tier, last_update, now in product((0, 1, 2, 5), (None, 0, 100), (100, 180, 340)):
        if last_update is not None and last_update > now:
            continue
        legacy = _legacy_lp(balance=10, last_mint=100)
        legacy.set_churn_tier("owner", "pool", tier)
        if last_update is not None:
            legacy.set_last_churn_update_timestamp("owner", "pool", last_update)
        exact = snapshot_lp_table(legacy)
        settlement = _settlement(
            owner="owner",
            pool_id="pool",
            delta_add=0,
            delta_sub=1,
        )

        mounted_error = validate_lp_settlement_age_gate(
            settlement=settlement,
            intents=[],
            lp_balances=legacy,
            block_timestamp=now,
            min_lp_position_age_seconds=0,
            duration_risk_policy=legacy_policy,
        )
        exact_result = apply_guarded_lp_position_events_v1(
            exact,
            events,
            now=now,
            min_age_seconds=0,
            policy=exact_policy,
        )

        assert (type(exact_result) is LPDurationTransitionOkV1) is (mounted_error is None)
        if mounted_error is not None:
            assert type(exact_result) is LPDurationTransitionRejectV1
            assert exact_result.code is LPDurationTransitionCodeV1.POSITION_LOCKED


def test_exact_age_guard_rejects_future_churn_update_without_candidate() -> None:
    legacy = _legacy_lp(balance=10, last_mint=1)
    legacy.set_churn_tier("owner", "pool", 1)
    legacy.set_last_churn_update_timestamp("owner", "pool", 11)

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=0,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.CHURN_TIMESTAMP_IN_FUTURE
    assert result.path == ("events", 0, "last_churn_update_timestamp")
    assert not hasattr(result, "state")


def test_exact_age_guard_future_churn_metadata_precedes_fixed_age_lock() -> None:
    legacy = _legacy_lp(balance=10, last_mint=9)
    legacy.set_churn_tier("owner", "pool", 1)
    legacy.set_last_churn_update_timestamp("owner", "pool", 11)

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=100,
        policy=_policy(),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.CHURN_TIMESTAMP_IN_FUTURE
    assert result.path == ("events", 0, "last_churn_update_timestamp")


def test_exact_age_guard_handles_huge_uncapped_tier_without_materializing_power() -> None:
    legacy = _legacy_lp(balance=10, last_mint=0)
    legacy.set_churn_tier("owner", "pool", 1 << 10_000)
    policy = LPDurationRiskPolicyV1(
        base_age_seconds=1,
        max_age_seconds=0,
        multiplier=2,
        max_churn_tier=0,
    )

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=0,
        policy=policy,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.POSITION_LOCKED


def test_exact_age_guard_huge_tier_multiplier_one_matches_legacy_math() -> None:
    legacy = _legacy_lp(balance=10, last_mint=0)
    huge_tier = 1 << 10_000
    legacy.set_churn_tier("owner", "pool", huge_tier)
    policy = LPDurationRiskPolicyV1(
        base_age_seconds=7,
        max_age_seconds=0,
        multiplier=1,
        max_churn_tier=0,
    )

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=7,
        min_age_seconds=0,
        policy=policy,
    )

    assert type(result) is LPDurationTransitionOkV1


def test_exact_age_guard_huge_tier_uses_declared_maximum_age_cap() -> None:
    legacy = _legacy_lp(balance=10, last_mint=0)
    legacy.set_churn_tier("owner", "pool", 1 << 10_000)
    policy = LPDurationRiskPolicyV1(
        base_age_seconds=1,
        max_age_seconds=7,
        multiplier=2,
        max_churn_tier=0,
    )

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(legacy),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=7,
        min_age_seconds=0,
        policy=policy,
    )

    assert type(result) is LPDurationTransitionOkV1


@pytest.mark.parametrize(
    ("min_age_seconds", "code"),
    (
        (cast(Any, True), LPDurationTransitionCodeV1.WRONG_EXACT_TYPE),
        (-1, LPDurationTransitionCodeV1.OUT_OF_RANGE),
        (1 << 32_000_000, LPDurationTransitionCodeV1.BYTE_LIMIT),
    ),
    ids=("boolean_alias", "negative", "byte_limit"),
)
def test_exact_age_guard_revalidates_minimum_age(
    min_age_seconds: object,
    code: LPDurationTransitionCodeV1,
) -> None:
    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=10,
        min_age_seconds=cast(Any, min_age_seconds),
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is code
    assert result.path == ("min_age_seconds",)


def test_exact_age_guard_minimum_age_error_precedes_other_invalid_inputs() -> None:
    result = apply_guarded_lp_position_events_v1(
        cast(Any, object()),
        cast(Any, []),
        now=cast(Any, -1),
        min_age_seconds=cast(Any, True),
        policy=cast(Any, object()),
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.WRONG_EXACT_TYPE
    assert result.path == ("min_age_seconds",)


def test_exact_age_guard_bounds_aggregate_context_bytes() -> None:
    two_point_one_megabytes = 1 << (8 * 2_100_000)

    result = apply_guarded_lp_position_events_v1(
        snapshot_lp_table(_legacy_lp()),
        (LPDurationEventV1(("owner", "pool"), 0, 1),),
        now=two_point_one_megabytes,
        min_age_seconds=two_point_one_megabytes,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.BYTE_LIMIT
    assert result.path == ("context",)
