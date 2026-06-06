"""
Stage 1 acceptance gate for the deterministic orderbook replay engine + verifier
(``src/core/orderbook_replay.py``).

Each test has REAL TEETH: it builds a VALID replay receipt with the COMMITTED
matcher, then tampers a claim and asserts the verifier RE-EXECUTES from scratch
and rejects with a stable code (or, for the round-trip / determinism cases, that
honest replays accept and are sequence-canonical).

The tamper strategy relies on ``ReplayReceipt`` / ``PerEventResult`` /
``FillRecord`` being DUMB typed containers (shape-only ``__post_init__``), so an
inconsistent claim can be CONSTRUCTED and handed to ``verify_replay`` — all
consistency lives in the verifier, never the container. We mutate via
``dataclasses.replace``.

Acceptance criteria (spec Stage 1):
  (1) valid replay round-trips (replay then verify => ok);
  (2) REORDERED events fail (swap two events' SEQUENCE VALUES, keep original
      per_event/roots => recompute differs => reject);
  (3) SKIPPED-better-price fails (claim a fill against a worse-priced maker while
      a better-priced resting order was available => recompute matches the BETTER
      maker => fills mismatch => reject);
  (4) FEE/QUOTE DRIFT fails (tampered quote/price => recompute correct value =>
      mismatch; changed fee_rule_hash in the claim => stale replay_root => reject);
  (5) DUPLICATE event fails (dup resting order_id => matcher rejects the dup, so a
      claim asserting it was ACCEPTED => recompute disagrees => reject);
  (6) determinism (same event multiset, any caller build order => identical
      replay_root; canonical order is the sequence field).
"""

import dataclasses

import pytest

from src.state.clob_book import (
    PRICE_SCALE,
    ClobBook,
    ClobOrder,
    ClobSide,
)
from src.core.orderbook_replay import (
    CancelEvent,
    FillRecord,
    PerEventResult,
    PlaceEvent,
    ReplayReceipt,
    replay_events,
    verify_replay,
    REJ_ACCEPT_STATUS_MISMATCH,
    REJ_DUP_SEQUENCE,
    REJ_EMPTY_EVENTS,
    REJ_FILL_MISMATCH,
    REJ_POST_ROOT_MISMATCH,
    REJ_PRE_ROOT_MISMATCH,
    REJ_REEXEC_ERROR,
    REJ_REPLAY_ROOT_MISMATCH,
)

BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32
MATCH_HASH = "0x" + "ab" * 32
FEE_HASH = "0x" + "cd" * 32
OTHER_FEE_HASH = "0x" + "ef" * 32


def _owner(tag: str) -> str:
    return "0x" + (tag * 48)[:96]


def _oid(n: int) -> str:
    return "0x" + f"{n:064x}"


def mk(side, price, qty, seq, oid_n, owner_tag="aa"):
    return ClobOrder(
        side=side,
        price_q_per_base=price,
        base_qty=qty,
        sequence=seq,
        order_id=_oid(oid_n),
        owner=_owner(owner_tag),
    )


def place(side, price, qty, seq, oid_n, owner_tag="aa"):
    return PlaceEvent(sequence=seq, order=mk(side, price, qty, seq, oid_n, owner_tag))


def _replay(events):
    return replay_events(
        events,
        base_asset=BASE,
        quote_asset=QUOTE,
        matching_rule_hash=MATCH_HASH,
        fee_rule_hash=FEE_HASH,
    )


# ---------------------------------------------------------------------------
# (1) Valid replay round-trips.
# ---------------------------------------------------------------------------
def test_valid_replay_round_trips():
    # SELL maker @100 (seq 1), BUY taker @101 (seq 2) crossing it: one fill @100.
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb"),
    )
    receipt = _replay(events)

    # Non-vacuity: the second event actually produced a fill at the maker price.
    assert receipt.per_event[1].accepted is True
    assert len(receipt.per_event[1].fills) == 1
    assert receipt.per_event[1].fills[0].maker_price == 100 * PRICE_SCALE
    assert receipt.per_event[1].fills[0].base == 50

    ok, code = verify_replay(receipt)
    assert ok is True
    assert code is None


def test_valid_replay_with_cancel_round_trips():
    # Place a non-crossing SELL, then cancel it by owner: book empties.
    events = (
        place(ClobSide.SELL, 105 * PRICE_SCALE, 50, 1, 1, "aa"),
        CancelEvent(sequence=2, order_id=_oid(1), requester=_owner("aa")),
    )
    receipt = _replay(events)
    assert receipt.per_event[1].accepted is True
    assert receipt.per_event[1].reject_code is None
    # After cancel the book is empty (final root == empty-book root).
    empty_root = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=()).state_root()
    assert receipt.final_book_root == empty_root

    ok, code = verify_replay(receipt)
    assert ok is True and code is None


def test_empty_events_rejected():
    with pytest.raises(ValueError) as exc:
        _replay(())
    assert str(exc.value) == REJ_EMPTY_EVENTS


# ---------------------------------------------------------------------------
# (2) Reordered events fail — swap SEQUENCE VALUES (not list positions).
# ---------------------------------------------------------------------------
def test_reordered_events_fail():
    # Original: A = SELL maker seq 1, B = BUY taker seq 2.
    #   canonical order [A, B]: A rests, B crosses A => fill at A's (SELL) price,
    #   A is the maker.
    a = place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa")
    b = place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb")
    original = _replay((a, b))

    # Reorder by SWAPPING SEQUENCE VALUES so canonical order becomes [B, A]:
    #   B (now seq 1) rests, A (now seq 2) crosses it => fill at B's (BUY) price,
    #   roles FLIP. The claim keeps the ORIGINAL per_event/roots/replay_root but
    #   swaps the events' sequences. Re-execution produces a DIFFERENT outcome.
    a_swapped = PlaceEvent(
        sequence=2,
        order=dataclasses.replace(a.order, sequence=2),
    )
    b_swapped = PlaceEvent(
        sequence=1,
        order=dataclasses.replace(b.order, sequence=1),
    )
    # Build a tampered claim: NEW (swapped) events, but OLD per_event + roots.
    tampered = dataclasses.replace(
        original,
        events=(b_swapped, a_swapped),  # canonical order is now [B(seq1), A(seq2)]
    )

    # Sanity: an honest replay of the swapped events differs from the original.
    honest_swapped = _replay((a_swapped, b_swapped))
    assert honest_swapped.replay_root != original.replay_root
    # Specifically the fill price flips to the BUY taker's resting price (101).
    assert honest_swapped.per_event[1].fills[0].maker_price == 101 * PRICE_SCALE

    ok, code = verify_replay(tampered)
    assert ok is False
    # First per-event divergence: the maker price / fill differs (or roots).
    assert code in {REJ_FILL_MISMATCH, REJ_POST_ROOT_MISMATCH, REJ_PRE_ROOT_MISMATCH}


# ---------------------------------------------------------------------------
# (3) Skipped better price fails.
# ---------------------------------------------------------------------------
def test_skipped_better_price_fails():
    # Two resting SELL makers: @100 (seq 1) and @101 (seq 2). A BUY taker @101
    # (seq 3) of qty 30 MUST match the BETTER (cheaper, @100) maker first.
    m_good = place(ClobSide.SELL, 100 * PRICE_SCALE, 30, 1, 1, "aa")
    m_bad = place(ClobSide.SELL, 101 * PRICE_SCALE, 30, 2, 2, "cc")
    taker = place(ClobSide.BUY, 101 * PRICE_SCALE, 30, 3, 3, "bb")
    receipt = _replay((m_good, m_bad, taker))

    taker_pe = receipt.per_event[2]
    assert taker_pe.accepted is True
    assert len(taker_pe.fills) == 1
    # The honest replay matched the BETTER maker (@100), order id 1.
    assert taker_pe.fills[0].maker_price == 100 * PRICE_SCALE
    assert taker_pe.fills[0].maker_order_id == _oid(1)

    # Tamper: claim the taker matched the WORSE maker (@101, oid 2) instead — i.e.
    # claim a fill that skipped the better-priced resting @100 order.
    bad_fill = receipt.per_event[2].fills[0]
    skipped_claim_fill = dataclasses.replace(
        bad_fill,
        maker_price=101 * PRICE_SCALE,
        maker_order_id=_oid(2),
    )
    tampered_pe = dataclasses.replace(
        receipt.per_event[2], fills=(skipped_claim_fill,)
    )
    tampered = dataclasses.replace(
        receipt,
        per_event=(receipt.per_event[0], receipt.per_event[1], tampered_pe),
    )

    ok, code = verify_replay(tampered)
    assert ok is False
    assert code == REJ_FILL_MISMATCH


# ---------------------------------------------------------------------------
# (4) Fee / quote drift fails.
# ---------------------------------------------------------------------------
def test_quote_drift_fails():
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb"),
    )
    receipt = _replay(events)
    real_fill = receipt.per_event[1].fills[0]
    assert real_fill.quote == 50 * 100  # floor(50 * 100*SCALE / SCALE)

    # Tamper the claimed quote upward (a price/quote drift in the fill).
    drifted_fill = dataclasses.replace(real_fill, quote=real_fill.quote + 1)
    tampered_pe = dataclasses.replace(receipt.per_event[1], fills=(drifted_fill,))
    tampered = dataclasses.replace(
        receipt, per_event=(receipt.per_event[0], tampered_pe)
    )

    ok, code = verify_replay(tampered)
    assert ok is False
    assert code == REJ_FILL_MISMATCH


def test_fee_rule_hash_drift_fails():
    # Changing the pinned fee_rule_hash in the claim (without recomputing the
    # bound replay_root) must reject: replay_root binds the fee rule hash.
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb"),
    )
    receipt = _replay(events)
    # Swap the fee_rule_hash but keep the original (now stale) replay_root.
    tampered = dataclasses.replace(receipt, fee_rule_hash=OTHER_FEE_HASH)

    ok, code = verify_replay(tampered)
    assert ok is False
    # The recomputed replay_root binds the NEW fee hash and differs from the claim.
    assert code == REJ_REPLAY_ROOT_MISMATCH

    # And the honest receipt over the other fee hash has a different replay_root.
    honest_other = replay_events(
        events,
        base_asset=BASE,
        quote_asset=QUOTE,
        matching_rule_hash=MATCH_HASH,
        fee_rule_hash=OTHER_FEE_HASH,
    )
    assert honest_other.replay_root != receipt.replay_root


def test_consistent_fee_rehash_accepts_documenting_stage1_boundary():
    # HONEST SCOPE: deterministic Stage-1 replay alone CANNOT catch a claim that
    # consistently re-hashes a DIFFERENT fee_rule_hash (its replay_root is then
    # self-consistent). Only a client's PINNED rulebook (Stage 2/3) rejects an
    # unexpected fee/matching rule pin. This test documents that boundary as
    # evidence, not assertion: a fully honest replay over OTHER_FEE_HASH verifies.
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb"),
    )
    honest_other = replay_events(
        events,
        base_asset=BASE,
        quote_asset=QUOTE,
        matching_rule_hash=MATCH_HASH,
        fee_rule_hash=OTHER_FEE_HASH,
    )
    ok, code = verify_replay(honest_other)
    assert ok is True and code is None
    # But its replay_root differs from the canonical-fee receipt: the pin IS bound,
    # so a client comparing against an expected pin would still distinguish them.
    canonical = _replay(events)
    assert honest_other.replay_root != canonical.replay_root


def test_matching_rule_hash_drift_fails():
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 50, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb"),
    )
    receipt = _replay(events)
    tampered = dataclasses.replace(receipt, matching_rule_hash=OTHER_FEE_HASH)
    ok, code = verify_replay(tampered)
    assert ok is False
    assert code == REJ_REPLAY_ROOT_MISMATCH


# ---------------------------------------------------------------------------
# (5) Duplicate event fails.
# ---------------------------------------------------------------------------
def test_duplicate_order_id_event_fails():
    # First a NON-crossing SELL @105 (seq 1) RESTS, then a second place reusing
    # the SAME order_id (seq 2) — the matcher rejects it as dup_order_id while the
    # first order is still resting. A claim asserting the dup was ACCEPTED must be
    # rejected by re-execution.
    e1 = place(ClobSide.SELL, 105 * PRICE_SCALE, 50, 1, 1, "aa")
    # Same order_id (1) but different sequence; non-crossing again so it would
    # otherwise rest — but it's a resting-id collision => matcher reject.
    dup_order = ClobOrder(
        side=ClobSide.SELL,
        price_q_per_base=106 * PRICE_SCALE,
        base_qty=50,
        sequence=2,
        order_id=_oid(1),  # DUPLICATE of e1's order id
        owner=_owner("aa"),
    )
    e2 = PlaceEvent(sequence=2, order=dup_order)
    receipt = _replay((e1, e2))

    # Honest replay: e2 rejected with dup_order_id, book unchanged on that step.
    dup_pe = receipt.per_event[1]
    assert dup_pe.accepted is False
    assert dup_pe.reject_code == "dup_order_id"
    assert dup_pe.pre_book_root == dup_pe.post_book_root  # reject-is-no-op
    assert dup_pe.fills == ()

    # Tamper: claim the duplicate event was ACCEPTED (and cleared its reject code).
    lying_pe = dataclasses.replace(dup_pe, accepted=True, reject_code=None)
    tampered = dataclasses.replace(
        receipt, per_event=(receipt.per_event[0], lying_pe)
    )

    ok, code = verify_replay(tampered)
    assert ok is False
    assert code == REJ_ACCEPT_STATUS_MISMATCH


def test_duplicate_sequence_is_fail_closed():
    # Two events sharing a sequence value cannot form a strict total order; replay
    # must fail closed rather than depend on caller arrival order.
    e1 = place(ClobSide.SELL, 105 * PRICE_SCALE, 50, 1, 1, "aa")
    e2 = place(ClobSide.SELL, 106 * PRICE_SCALE, 50, 1, 2, "bb")  # same seq 1
    with pytest.raises(ValueError) as exc:
        _replay((e1, e2))
    assert str(exc.value) == REJ_DUP_SEQUENCE


# ---------------------------------------------------------------------------
# (6) Determinism — same multiset, any build order => identical replay_root.
# ---------------------------------------------------------------------------
def test_determinism_independent_of_caller_build_order():
    a = place(ClobSide.SELL, 100 * PRICE_SCALE, 30, 1, 1, "aa")
    b = place(ClobSide.SELL, 101 * PRICE_SCALE, 40, 2, 2, "cc")
    c = place(ClobSide.BUY, 101 * PRICE_SCALE, 60, 3, 3, "bb")

    r_forward = _replay((a, b, c))
    r_shuffled = _replay((c, a, b))
    r_reverse = _replay((c, b, a))

    # Identical replay_root, final_book_root, and per-event records: canonical
    # order is the SEQUENCE field, not the caller's list order.
    assert r_forward.replay_root == r_shuffled.replay_root == r_reverse.replay_root
    assert (
        r_forward.final_book_root
        == r_shuffled.final_book_root
        == r_reverse.final_book_root
    )
    assert r_forward.per_event == r_shuffled.per_event == r_reverse.per_event

    # All three independently round-trip through the verifier.
    for r in (r_forward, r_shuffled, r_reverse):
        ok, code = verify_replay(r)
        assert ok is True and code is None


def test_determinism_byte_stable_across_runs():
    # The replay_root is a pure function of the (canonicalized) inputs: running
    # the same multiset twice yields byte-identical roots.
    events = (
        place(ClobSide.SELL, 100 * PRICE_SCALE, 30, 1, 1, "aa"),
        place(ClobSide.BUY, 101 * PRICE_SCALE, 30, 2, 2, "bb"),
    )
    r1 = _replay(events)
    r2 = _replay(events)
    assert r1.replay_root == r2.replay_root
    assert r1.final_book_root == r2.final_book_root


# ---------------------------------------------------------------------------
# Verifier robustness: never raises; structural breakage => fail-closed.
# ---------------------------------------------------------------------------
def test_verifier_never_raises_on_malformed_claim():
    # A claim carrying a duplicate sequence cannot be re-executed cleanly; the
    # verifier must return (False, REJ_REEXEC_ERROR), not raise.
    e1 = place(ClobSide.SELL, 105 * PRICE_SCALE, 50, 1, 1, "aa")
    e2 = place(ClobSide.BUY, 101 * PRICE_SCALE, 50, 2, 2, "bb")
    receipt = _replay((e1, e2))
    # Force a duplicate sequence into the claim's events (dumb container allows it).
    dup_seq_event = PlaceEvent(
        sequence=2, order=dataclasses.replace(e1.order, sequence=2)
    )
    broken = dataclasses.replace(receipt, events=(dup_seq_event, e2))
    ok, code = verify_replay(broken)
    assert ok is False
    assert code == REJ_REEXEC_ERROR


def test_final_book_root_tamper_rejects():
    events = (
        place(ClobSide.SELL, 105 * PRICE_SCALE, 50, 1, 1, "aa"),
    )
    receipt = _replay(events)
    tampered = dataclasses.replace(
        receipt, final_book_root="0x" + "00" * 32
    )
    ok, code = verify_replay(tampered)
    assert ok is False
    assert code == REJ_REPLAY_ROOT_MISMATCH or code == "final_root_mismatch"
