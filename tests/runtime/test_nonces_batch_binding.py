"""Batch-level semantic binding for the LIVE nonce authority ``src.state.nonces``.

Phase 2 of the production-promotion plan. ``validate_and_apply_intent_nonce_batch``
is the running spot-DEX replay authority (``src/integration/dex_engine.py:132`` and
``src/integration/autotrader_live.py:2628``, both ``require_all_nonces=True``). The
Phase-1 work proved ``src/core/replay_guard.py`` ≡ ``nonces.py`` on the
SINGLE-TRANSITION slice; this suite pins the BATCH-level semantics that have no
single-transition analogue and were the two open gaps:

* cross-sender ATOMICITY (all-or-nothing rollback),
* ORDER-INDEPENDENCE (per-sender nonces are sorted before the range check),
* in-batch DUPLICATE detection,
* per-sender ISOLATION at the batch level,
* reject-is-NO-OP (the input table is never mutated),
* the canonical reject PRECEDENCE actually run by the authority (nonce-before-sender),
* the full reject VOCABULARY,
* the multi-sender WRAPPER LAW: the batch's accept decision + final per-sender state
  equals folding the proven single-transition ``admit`` over each sender's sorted
  nonces independently (extends the Phase-1 single-sender ``TestBatchWrapperLaw``).

These are deterministic, hard-assertion PROPERTY tests over the actual authority —
NOT a formal proof of the batch (a batch-level ESSO/Lean artifact remains open and
is tracked as the proof_artifact gap on the ``nonces`` surface). This suite does
NOT change ``nonces.py`` — it binds its existing behavior.
"""

from __future__ import annotations

import itertools

import pytest

from src.core.replay_guard import (
    REPLAY_GUARD_SURFACE,
    AdmitRejected,
    ReplayGuardState,
    _canonical_sender,
    admit,
)
from src.runtime.authority import AuthorityMode, active_mode
from src.state.intents import Intent, IntentKind
from src.state.nonces import (
    NonceTable,
    _check_nonce_batch_runtime_invariants,
    validate_and_apply_intent_nonce_batch,
)

# --- senders (48-byte / 96-hex pubkeys) + a non-hex one both impls reject ----
SENDER_A = "0x" + "11" * 48
SENDER_B = "0x" + "22" * 48
SENDER_C = "0x" + "33" * 48
BAD_SENDER = "0xzz" + "11" * 47  # right width, non-hex -> invalid_sender
_INTENT_ID = "0x" + "ab" * 32
U32_MAX = 0xFFFFFFFF

# --- reject vocabulary actually emitted by the authority ---------------------
REJ_BAD_NONCE = "Missing/invalid nonce"
REJ_SENDER_PREFIX = "invalid sender_pubkey for nonce accounting:"
REJ_MIXED = "nonce presence must be consistent across batch"
REJ_DUP = "duplicate nonce in batch"
REJ_SEQ = "nonce sequence invalid"

_MISSING = object()  # sentinel: build an intent with NO nonce field


def _intent(sender: object, nonce: object) -> Intent:
    fields = {} if nonce is _MISSING else {"nonce": nonce}
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_INTENT_ID,
        sender_pubkey=sender,
        deadline=10**12,
        fields=fields,
    )


def _batch(table: NonceTable, pairs, *, require_all: bool = True):
    intents = [_intent(s, n) for (s, n) in pairs]
    return validate_and_apply_intent_nonce_batch(
        nonces=table, intents=intents, require_all_nonces=require_all
    )


def _canon(sender: str) -> str:
    c = _canonical_sender(sender)
    assert c is not None
    return c


# --- 1. per-sender strict-sequential accept + order-independence -------------


@pytest.mark.parametrize(
    "order",
    list(itertools.permutations([1, 2, 3])),
)
def test_single_sender_contiguous_range_accepts_in_any_order(order) -> None:
    table = NonceTable()
    ok, reason, updated = _batch(table, [(SENDER_A, n) for n in order])
    assert ok is True and reason is None and updated is not None
    assert updated.get_last(_canon(SENDER_A)) == 3  # last+1..last+k, regardless of order


def test_order_independence_of_accept_and_final_state() -> None:
    # The same multiset of (sender, nonce) intents in ANY order yields the same
    # accept decision and the same final per-sender state.
    pairs = [(SENDER_A, 1), (SENDER_B, 1), (SENDER_A, 2), (SENDER_B, 2), (SENDER_C, 1)]
    baseline = None
    for perm in itertools.permutations(pairs):
        ok, reason, updated = _batch(NonceTable(), list(perm))
        assert ok is True and reason is None
        state = {s: updated.get_last(_canon(s)) for s in (SENDER_A, SENDER_B, SENDER_C)}
        if baseline is None:
            baseline = state
        assert state == baseline == {SENDER_A: 2, SENDER_B: 2, SENDER_C: 1}


def test_non_contiguous_range_rejects() -> None:
    for bad in ([1, 3], [2, 3], [1, 2, 4]):
        ok, reason, updated = _batch(NonceTable(), [(SENDER_A, n) for n in bad])
        assert ok is False and reason == REJ_SEQ and updated is None


def test_range_must_start_at_last_plus_one() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 5)
    ok, reason, updated = _batch(table, [(SENDER_A, 7), (SENDER_A, 6)])  # 6,7 == 5+1,5+2
    assert ok is True and updated.get_last(_canon(SENDER_A)) == 7
    ok2, reason2, updated2 = _batch(table, [(SENDER_A, 7)])  # skips 6
    assert ok2 is False and reason2 == REJ_SEQ and updated2 is None


# --- 2. cross-sender ATOMICITY (all-or-nothing; the batch-only gap) ----------


def test_cross_sender_atomicity_rejects_whole_batch_no_partial_apply() -> None:
    # A's range is valid; B's is a gap. The WHOLE batch rejects with no partial
    # application — A is NOT advanced. (admit-folded individually, A would accept.)
    table = NonceTable()
    ok, reason, updated = _batch(table, [(SENDER_A, 1), (SENDER_A, 2), (SENDER_B, 5)])
    assert ok is False and reason == REJ_SEQ and updated is None
    # A would have accepted on its own — proving the rollback is cross-sender atomic.
    ok_a, _, updated_a = _batch(NonceTable(), [(SENDER_A, 1), (SENDER_A, 2)])
    assert ok_a is True and updated_a.get_last(_canon(SENDER_A)) == 2


# --- 3. in-batch DUPLICATE detection -----------------------------------------


@pytest.mark.parametrize("dups", [[1, 1], [1, 2, 2], [1, 1, 2]])
def test_in_batch_duplicate_rejects(dups) -> None:
    ok, reason, updated = _batch(NonceTable(), [(SENDER_A, n) for n in dups])
    assert ok is False and reason == REJ_DUP and updated is None


# --- 4. reject-is-NO-OP: the input table is never mutated --------------------


def test_reject_is_no_op_input_table_unchanged() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 3)
    table.set_last(SENDER_B, 1)
    before = dict(table.get_all())
    reject_cases = [
        [(SENDER_A, 5)],                    # gap -> seq invalid
        [(SENDER_A, 4), (SENDER_A, 4)],     # duplicate
        [(SENDER_A, 4), (BAD_SENDER, 1)],   # invalid sender
        [(SENDER_A, 0)],                    # invalid nonce
        [(SENDER_A, 4), (SENDER_B, 9)],     # B gap -> whole batch rejects
    ]
    for pairs in reject_cases:
        ok, reason, updated = _batch(table, pairs)
        assert ok is False and updated is None, pairs
        assert dict(table.get_all()) == before, f"input table mutated by {pairs}"


def test_accept_returns_fresh_table_without_mutating_input() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 1)
    before = dict(table.get_all())
    ok, reason, updated = _batch(table, [(SENDER_A, 2)])
    assert ok is True and updated is not None
    assert updated.get_last(_canon(SENDER_A)) == 2
    assert dict(table.get_all()) == before  # input untouched; advance is on the copy


def test_runtime_invariant_helper_accepts_exact_staged_advance() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 1)
    updated = NonceTable()
    updated.set_last(SENDER_A, 3)
    updated.set_last(SENDER_B, 1)

    ok, err = _check_nonce_batch_runtime_invariants(
        before=table,
        after=updated,
        per_sender={_canon(SENDER_A): [3, 2], _canon(SENDER_B): [1]},
    )
    assert ok is True and err is None


def test_runtime_invariant_helper_rejects_partial_staged_advance() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 1)
    updated = NonceTable()
    updated.set_last(SENDER_A, 3)
    # B's accepted nonce is missing from the staged table.

    ok, err = _check_nonce_batch_runtime_invariants(
        before=table,
        after=updated,
        per_sender={_canon(SENDER_A): [2, 3], _canon(SENDER_B): [1]},
    )
    assert ok is False
    assert err == "nonce runtime invariant violation: staged table mismatch"


def test_runtime_invariant_helper_rejects_empty_sender_group() -> None:
    ok, err = _check_nonce_batch_runtime_invariants(
        before=NonceTable(),
        after=NonceTable(),
        per_sender={_canon(SENDER_A): []},
    )
    assert ok is False
    assert err == "nonce runtime invariant violation: empty sender group"


# --- 5. per-sender ISOLATION at the batch level ------------------------------


def test_per_sender_isolation_each_advances_independently() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 10)
    table.set_last(SENDER_B, 20)
    ok, reason, updated = _batch(table, [(SENDER_A, 11), (SENDER_B, 21), (SENDER_B, 22)])
    assert ok is True
    assert updated.get_last(_canon(SENDER_A)) == 11  # +1
    assert updated.get_last(_canon(SENDER_B)) == 22  # +2
    assert updated.get_last(_canon(SENDER_C)) == 0   # untouched sender stays 0


# --- 6. canonical reject PRECEDENCE (nonce-before-sender) --------------------


def test_canonical_precedence_is_nonce_before_sender() -> None:
    # The AUTHORITY checks the nonce before the sender. A double-fault intent
    # (bad sender AND bad nonce) therefore reports the NONCE error. This pins the
    # canonical consensus precedence (and is exactly why the Phase-1 binding to
    # replay_guard.py — which checks sender-first — is scoped to single-fault).
    ok, reason, updated = _batch(NonceTable(), [(BAD_SENDER, 0)])
    assert ok is False and reason == REJ_BAD_NONCE and updated is None
    # A bad sender with a VALID nonce reports the sender error.
    ok2, reason2, _ = _batch(NonceTable(), [(BAD_SENDER, 1)])
    assert ok2 is False and reason2.startswith(REJ_SENDER_PREFIX)


# --- 7. reject VOCABULARY coverage (all five reasons reachable) --------------


def test_full_reject_vocabulary_is_reachable() -> None:
    seen = set()
    # Missing/invalid nonce (bad value) and (missing field, require_all=True)
    seen.add(_batch(NonceTable(), [(SENDER_A, 0)])[1])
    seen.add(_batch(NonceTable(), [(SENDER_A, _MISSING)])[1])
    # invalid sender
    seen.add(_batch(NonceTable(), [(BAD_SENDER, 1)])[1].split(":")[0] + ":")
    # duplicate
    seen.add(_batch(NonceTable(), [(SENDER_A, 1), (SENDER_A, 1)])[1])
    # sequence invalid
    seen.add(_batch(NonceTable(), [(SENDER_A, 2)])[1])
    # mixed presence (require_all=False)
    seen.add(_batch(NonceTable(), [(SENDER_A, 1), (SENDER_B, _MISSING)], require_all=False)[1])
    assert REJ_BAD_NONCE in seen
    assert REJ_SENDER_PREFIX in seen
    assert REJ_DUP in seen
    assert REJ_SEQ in seen
    assert REJ_MIXED in seen


# --- 8. bounds: positive u32 nonces only -------------------------------------


@pytest.mark.parametrize("bad", [0, -1, U32_MAX + 1, "5", 1.5, True, None, _MISSING])
def test_invalid_nonce_values_reject(bad) -> None:
    ok, reason, updated = _batch(NonceTable(), [(SENDER_A, bad)])
    assert ok is False and reason == REJ_BAD_NONCE and updated is None


def test_u32_max_nonce_is_accepted_at_boundary() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, U32_MAX - 1)
    ok, reason, updated = _batch(table, [(SENDER_A, U32_MAX)])
    assert ok is True and updated.get_last(_canon(SENDER_A)) == U32_MAX


# --- 9. require_all_nonces semantics -----------------------------------------


def test_require_all_true_rejects_any_missing_nonce() -> None:
    ok, reason, updated = _batch(NonceTable(), [(SENDER_A, 1), (SENDER_B, _MISSING)], require_all=True)
    assert ok is False and reason == REJ_BAD_NONCE and updated is None


def test_require_all_false_accepts_nonce_free_batch_as_noop() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 4)
    ok, reason, updated = _batch(table, [(SENDER_A, _MISSING)], require_all=False)
    assert ok is True and reason is None
    assert updated.get_last(_canon(SENDER_A)) == 4  # unchanged


def test_require_all_false_rejects_mixed_presence() -> None:
    ok, reason, updated = _batch(
        NonceTable(), [(SENDER_A, 1), (SENDER_B, _MISSING)], require_all=False
    )
    assert ok is False and reason == REJ_MIXED and updated is None


def test_empty_batch_accepts_noop() -> None:
    table = NonceTable()
    table.set_last(SENDER_A, 7)
    ok, reason, updated = validate_and_apply_intent_nonce_batch(
        nonces=table, intents=[], require_all_nonces=True
    )
    assert ok is True and reason is None and updated.get_last(_canon(SENDER_A)) == 7


# --- 10. multi-sender WRAPPER LAW: batch == per-sender admit-fold -------------


def _fold_admit_per_sender(start_state: dict, pairs) -> tuple[bool, dict]:
    """Reference: fold the proven single-transition ``admit`` over each sender's
    SORTED nonces independently. Returns (all_accepted, final per-sender last).
    Mirrors the batch's set-semantics so we can bind the wrapper to the core."""
    by_sender: dict[str, list[int]] = {}
    for s, n in pairs:
        by_sender.setdefault(_canon(s), []).append(n)
    final = dict(start_state)
    for cs, nonces in by_sender.items():
        if len(nonces) != len(set(nonces)):
            return False, dict(start_state)  # duplicate -> batch rejects
        state = ReplayGuardState()
        if final.get(cs):
            state = state.with_last(cs, final[cs])
        for n in sorted(nonces):
            r = admit(state=state, sender=cs, nonce=n)
            if isinstance(r, AdmitRejected):
                return False, dict(start_state)  # reject-is-no-op for the whole fold
            state = r.state
        final[cs] = state.last_for(cs)
    return True, final


@pytest.mark.parametrize(
    "pairs",
    [
        [(SENDER_A, 1), (SENDER_A, 2), (SENDER_B, 1)],          # multi-sender accept
        [(SENDER_B, 2), (SENDER_A, 1), (SENDER_B, 1), (SENDER_A, 2)],  # shuffled accept
        [(SENDER_A, 1), (SENDER_C, 1), (SENDER_B, 1)],          # three fresh senders
        [(SENDER_A, 1), (SENDER_A, 3)],                          # gap -> both reject
        [(SENDER_A, 1), (SENDER_A, 1)],                          # dup -> both reject
        [(SENDER_A, 2)],                                         # not from 1 -> both reject
    ],
)
def test_multi_sender_wrapper_law_matches_admit_fold(pairs) -> None:
    # For well-formed / single-fault inputs the batch ACCEPT decision and the
    # final per-sender state equal the per-sender sorted-admit fold over the
    # proven single-transition core. (Reject REASONS can differ for double-fault
    # inputs by precedence — pinned in test_canonical_precedence... — so this law
    # binds the accept/state, not the reason.)
    #
    # Hygiene: ``admit`` is authority-routed; this binding is only meaningful
    # against the Python single-transition core, so pin the ambient mode (a future
    # surface promotion must not silently turn this into a Rust-binary dependency).
    assert active_mode(REPLAY_GUARD_SURFACE) is AuthorityMode.PYTHON_AUTHORITY
    ok, _reason, updated = _batch(NonceTable(), pairs)
    fold_ok, fold_state = _fold_admit_per_sender({}, pairs)
    assert ok is fold_ok, f"batch accept={ok} but admit-fold accept={fold_ok} for {pairs}"
    if ok:
        for cs, last in fold_state.items():
            assert updated.get_last(cs) == last, (cs, last)


# --- 11. non-vacuity guard ---------------------------------------------------


def test_suite_exercises_accept_and_every_reject_class() -> None:
    # Defends the suite against silently testing only one path.
    outcomes = {
        "accept": _batch(NonceTable(), [(SENDER_A, 1)]),
        "seq": _batch(NonceTable(), [(SENDER_A, 2)]),
        "dup": _batch(NonceTable(), [(SENDER_A, 1), (SENDER_A, 1)]),
        "bad_nonce": _batch(NonceTable(), [(SENDER_A, 0)]),
        "bad_sender": _batch(NonceTable(), [(BAD_SENDER, 1)]),
    }
    assert outcomes["accept"][0] is True
    assert all(outcomes[k][0] is False for k in ("seq", "dup", "bad_nonce", "bad_sender"))
