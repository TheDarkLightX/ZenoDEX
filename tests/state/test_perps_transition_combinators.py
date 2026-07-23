from __future__ import annotations

from dataclasses import replace
from typing import cast

from src.state.perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from src.state.perps_transition_combinators import (
    _build_optional_global_patch_from_entries,
    _existing_account_patch_and_entries,
)
from src.state.state_snapshot_values import CommittedPerpAccountStateV1
from tests.state.test_perps_epoch_transitions import (
    _ALICE,
    _BOB,
    _account,
    _exact_market,
)


def test_account_join_rejects_mutable_unsorted_and_unknown_replacements() -> None:
    pre = _exact_market(
        {
            _ALICE: _account(position_base=0, collateral_quote=10),
            _BOB: _account(position_base=0, collateral_quote=20),
        }
    )
    alice = pre.get_account(_ALICE)
    bob = pre.get_account(_BOB)
    assert type(alice) is CommittedPerpAccountStateV1
    assert type(bob) is CommittedPerpAccountStateV1

    mutable = _existing_account_patch_and_entries(pre, [(_ALICE, alice)])
    unsorted = _existing_account_patch_and_entries(
        pre,
        ((_BOB, bob), (_ALICE, alice)),
    )
    unknown_key = "0x" + "33" * 48
    unknown = _existing_account_patch_and_entries(
        pre,
        ((unknown_key, alice),),
    )

    assert mutable == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
        ("state", "accounts"),
    )
    assert unsorted == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
        ("state", "accounts", 1),
    )
    assert unknown == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
        ("state", "accounts", unknown_key),
    )


def test_account_join_preserves_committed_identity_for_logical_no_ops() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0, collateral_quote=10)})
    alice = pre.get_account(_ALICE)
    assert type(alice) is CommittedPerpAccountStateV1
    equal_replacement = replace(alice)

    result = _existing_account_patch_and_entries(
        pre,
        ((_ALICE, equal_replacement),),
    )

    assert type(result) is tuple
    patch, entries = result
    assert patch is None
    assert entries is pre.account_entries
    assert entries[0][1] is alice


def test_account_join_emits_one_sorted_compare_and_replace_patch() -> None:
    pre = _exact_market(
        {
            _ALICE: _account(position_base=0, collateral_quote=10),
            _BOB: _account(position_base=0, collateral_quote=20),
        }
    )
    alice = pre.get_account(_ALICE)
    bob = pre.get_account(_BOB)
    assert type(alice) is CommittedPerpAccountStateV1
    assert type(bob) is CommittedPerpAccountStateV1
    replacement = replace(alice, collateral_quote=11)

    result = _existing_account_patch_and_entries(
        pre,
        ((_ALICE, replacement),),
    )

    assert type(result) is tuple
    patch, entries = result
    assert patch is not None
    assert len(patch.writes) == 1
    assert patch.writes[0].account_pubkey == _ALICE
    assert patch.writes[0].expected is alice
    assert patch.writes[0].replacement is replacement
    assert entries[0] == (_ALICE, replacement)
    assert entries[1][0] == _BOB
    assert entries[1][1] is bob


def test_global_patch_combinator_requires_the_complete_canonical_registry() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0)})
    canonical = pre.global_entries
    reordered = (canonical[1], canonical[0], *canonical[2:])

    mutable = _build_optional_global_patch_from_entries(list(canonical), canonical)
    incomplete = _build_optional_global_patch_from_entries(canonical[:-1], canonical[:-1])
    noncanonical = _build_optional_global_patch_from_entries(reordered, reordered)

    expected = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
        ("patch", "global"),
    )
    assert mutable == expected
    assert incomplete == expected
    assert noncanonical == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
        ("patch", "global", 0),
    )


def test_global_patch_combinator_returns_none_for_exact_logical_no_op() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0)})

    result = _build_optional_global_patch_from_entries(
        pre.global_entries,
        tuple(pre.global_entries),
    )

    assert result is None


def test_global_patch_combinator_emits_canonical_changed_fields_only() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0)})
    changed_fields = {
        "fee_income",
        "fee_pool_quote",
        "insurance_balance",
    }
    after = tuple(
        (field, cast(int, value) + 1 if field in changed_fields else value)
        for field, value in pre.global_entries
    )

    result = _build_optional_global_patch_from_entries(pre.global_entries, after)

    assert type(result) is CanonicalIsolatedGlobalPatchV1
    assert tuple(write.field for write in result.writes) == tuple(sorted(changed_fields))
    assert all(
        cast(int, write.replacement) == cast(int, write.expected) + 1 for write in result.writes
    )
