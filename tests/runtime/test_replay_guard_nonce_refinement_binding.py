"""Proven-refinement BINDING: ``src.core.replay_guard`` ≡ ``src.state.nonces``.

The CBC replay-guard proof chain has three links:

1. **Kani-Rust**: ``rust-runtime/.../src/replay_guard.rs`` carries four
   ``#[kani::proof]`` harnesses (no-panic, no-overflow, reject-is-no-op,
   ``classify_sequence`` reject-code parity); CI ``runtime-kani.yml``.
2. **Python ``src.core.replay_guard`` ≡ Rust**: the differential conformance test
   ``tests/runtime/test_replay_guard_conformance.py`` drives both sides through
   ``tools/runtime/replay_guard_lib.replay_txs`` → ``apply_tx`` → ``admit``, which
   imports the transition *directly* from ``src.core.replay_guard`` (lib lines
   23-29, 59). CI ``runtime-shadow.yml``.
3. **THIS test — the open link**: ``src.core.replay_guard.admit`` (the CBC-core
   single-transition the proof/differential chain reaches) vs.
   ``src.state.nonces.validate_and_apply_intent_nonce_batch`` — the validator the
   **live authority path** actually runs at settlement
   (``src/integration/dex_engine.py:132``, ``require_all_nonces=True``).

Without link 3 the proof chain stops at ``replay_guard.py`` and never reaches the
running code. This test closes link 3 **on the single-transition slice only** (it
does NOT prove the multi-sender batch — see the residual gap below) by asserting
observational equivalence: thread
both states through one identical (sender, nonce) event sequence at a time —
driving the batch validator with a **single-intent batch per step** so the
single-transition and batch shapes are directly comparable — and assert, at every
step, that accept/reject decision, the (mapped) reject reason, and the resulting
per-sender accepted-nonce state are IDENTICAL.

Reject vocabularies are NOT a bijection. A size-1 batch collapses the three
sequencing rejects of ``admit`` into one batch reason:

    admit ``duplicate_nonce`` | ``stale_nonce`` | ``nonce_gap``
        → batch ``"nonce sequence invalid"``  (size-1: sorted([n]) != [last+1])
    admit ``invalid_nonce``   → batch ``"Missing/invalid nonce"``
    admit ``invalid_sender``  → batch ``"invalid sender_pubkey for nonce accounting: …"``

The mapping is therefore many-to-one on the sequencing codes; this test pins it
explicitly and asserts equivalence on the *equivalence classes*, not the raw
strings. One genuine, safety-neutral divergence is documented and asserted
rather than hidden: ``admit`` checks the sender before the nonce, while the batch
validator checks the nonce before the sender, so a double-fault input reports
different (but both still rejecting, both still no-op) reasons —
``test_double_fault_precedence_divergence`` pins the actual behavior.

Residual gap (NOT closed here): the multi-element batch *wrapper* semantics
(order-independence via sort, cross-sender all-or-nothing atomicity, in-batch
duplicate detection) are not single-transition properties. The optional
``TestBatchWrapperLaw`` section pins the set-semantics law that relates a size-k
batch to the in-order ``admit``-fold **by example** (parametrized cases, NOT a
proof over all batches), and explicitly pins cross-sender atomicity as a
batch-only property with no single-transition analogue. Cross-sender batch
atomicity therefore remains UNPROVEN.
"""

from __future__ import annotations

import pytest

from src.core.replay_guard import (
    REJ_DUPLICATE_NONCE,
    REJ_INVALID_NONCE,
    REJ_INVALID_SENDER,
    REJ_NONCE_GAP,
    REJ_STALE_NONCE,
    REPLAY_GUARD_SURFACE,
    AdmitAccepted,
    AdmitRejected,
    ReplayGuardState,
    admit,
)
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch

# --- Bounded sender corpus -------------------------------------------------
# Three valid 48-byte (96 hex char) senders, plus a non-hex sender that both
# implementations reject via the shared ``canonical_hex_fixed_allow_0x``.
SENDER_A = "0x" + "11" * 48
SENDER_B = "0x" + "22" * 48
SENDER_C = "0x" + "33" * 48
BAD_SENDER = "0xzz" + "11" * 47  # right width, non-hex -> invalid_sender (both)
VALID_SENDERS = (SENDER_A, SENDER_B, SENDER_C)

U32_MAX = 0xFFFFFFFF

# --- Reject-vocabulary mapping (admit code -> batch reason class) ----------
# Size-1 batch collapses the three sequencing rejects into one class.
SEQUENCING_REJECTS = frozenset({REJ_DUPLICATE_NONCE, REJ_STALE_NONCE, REJ_NONCE_GAP})
BATCH_SEQ_INVALID = "nonce sequence invalid"
BATCH_BAD_NONCE = "Missing/invalid nonce"
BATCH_BAD_SENDER_PREFIX = "invalid sender_pubkey for nonce accounting:"


def _admit_class(reason: str) -> str:
    """Collapse an ``admit`` reject code to its size-1-batch equivalence class."""
    if reason in SEQUENCING_REJECTS:
        return BATCH_SEQ_INVALID
    if reason == REJ_INVALID_NONCE:
        return BATCH_BAD_NONCE
    if reason == REJ_INVALID_SENDER:
        return BATCH_BAD_SENDER_PREFIX
    raise AssertionError(f"unmapped admit reject code: {reason!r}")


def _batch_class(reason: str) -> str:
    """Collapse a batch reject reason to its equivalence class (prefix-tolerant)."""
    if reason == BATCH_SEQ_INVALID:
        return BATCH_SEQ_INVALID
    if reason == BATCH_BAD_NONCE:
        return BATCH_BAD_NONCE
    if reason.startswith(BATCH_BAD_SENDER_PREFIX):
        return BATCH_BAD_SENDER_PREFIX
    raise AssertionError(f"unmapped batch reject reason: {reason!r}")


# --- Intent construction (drives the LIVE validator) -----------------------
_INTENT_ID = "0x" + "ab" * 32


def _nonce_intent(sender: object, nonce: object) -> Intent:
    """A minimal nonce-bearing intent for the batch validator.

    ``Intent`` validates only ``module`` and ``intent_id`` in ``__post_init__``;
    ``sender_pubkey`` and ``fields['nonce']`` flow through unvalidated so the
    batch validator performs the same canonicalization/range checks as ``admit``.
    """
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_INTENT_ID,
        sender_pubkey=sender,
        deadline=10**12,
        fields={"nonce": nonce},
    )


def _single_batch(nonces: NonceTable, sender: object, nonce: object):
    """Drive the live validator with a one-intent batch (mirrors one ``admit``)."""
    return validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[_nonce_intent(sender, nonce)],
        require_all_nonces=True,
    )


# --- The enumerated event corpus -------------------------------------------
# A single deterministic sequence exercising, across multiple senders:
#   accept, duplicate (== last), stale (< last), gap (> last+1),
#   invalid_nonce (0 / above-u32), per-sender isolation (interleave), and
#   replay (re-submit an already-accepted nonce). Each entry is a single
#   (sender, nonce) event; both implementations consume them one at a time.
EVENT_SEQUENCE: tuple[tuple[object, object], ...] = (
    (SENDER_A, 1),            # accept
    (SENDER_B, 1),            # accept (B independent of A)
    (SENDER_A, 2),            # accept
    (SENDER_A, 2),            # duplicate_nonce (== last A)
    (SENDER_A, 1),            # stale_nonce  (replay of an older A tx)
    (SENDER_B, 3),            # nonce_gap    (last B = 1, skips 2)
    (SENDER_C, 1),            # accept (C fresh; isolation from A,B)
    (SENDER_A, 4),            # nonce_gap    (last A = 2)
    (SENDER_A, 3),            # accept (A resumes contiguous)
    (SENDER_B, 2),            # accept (B resumes after its rejected gap)
    (BAD_SENDER, 1),          # invalid_sender (both reject; states untouched)
    (SENDER_A, 0),            # invalid_nonce (zero / below range)
    (SENDER_A, -1),           # invalid_nonce (negative)
    (SENDER_A, U32_MAX + 1),  # invalid_nonce (above u32)
    (SENDER_C, 2),            # accept (C last = 1)
    (SENDER_C, 2),            # duplicate_nonce — replay of just-accepted C nonce
    (SENDER_A, 4),            # accept (A last = 3)
)


def _expected_admit_reason(state: ReplayGuardState, sender: object, nonce: object) -> str | None:
    """Oracle for the single-transition reject code (mirrors ``_admit_python``)."""
    # Sender first, then nonce range, then policy — matching admit precedence.
    from src.core.replay_guard import _canonical_sender, _is_plain_int

    canon = _canonical_sender(sender)
    if canon is None:
        return REJ_INVALID_SENDER
    if not _is_plain_int(nonce) or not (1 <= nonce <= U32_MAX):
        return REJ_INVALID_NONCE
    last = state.last_for(canon)
    if nonce == last:
        return REJ_DUPLICATE_NONCE
    if nonce < last:
        return REJ_STALE_NONCE
    if nonce > last + 1:
        return REJ_NONCE_GAP
    return None


def test_event_corpus_is_non_vacuous():
    """Guard against a corpus that never exercises the intended classes."""
    state = ReplayGuardState()
    seen_accept = seen_dup = seen_stale = seen_gap = seen_bad_nonce = seen_bad_sender = False
    for sender, nonce in EVENT_SEQUENCE:
        reason = _expected_admit_reason(state, sender, nonce)
        if reason is None:
            seen_accept = True
            state = state.with_last(_canon(sender), nonce)
        elif reason == REJ_DUPLICATE_NONCE:
            seen_dup = True
        elif reason == REJ_STALE_NONCE:
            seen_stale = True
        elif reason == REJ_NONCE_GAP:
            seen_gap = True
        elif reason == REJ_INVALID_NONCE:
            seen_bad_nonce = True
        elif reason == REJ_INVALID_SENDER:
            seen_bad_sender = True
    assert seen_accept and seen_dup and seen_stale and seen_gap
    assert seen_bad_nonce and seen_bad_sender


def _canon(sender: object) -> str:
    from src.core.replay_guard import _canonical_sender

    canon = _canonical_sender(sender)
    assert canon is not None
    return canon


def test_observational_equivalence_over_event_corpus():
    """Core binding: iterate ``admit`` and the size-1 batch validator over one
    identical event sequence; every step must agree on decision, reject class,
    and the resulting per-sender accepted-nonce state.

    Inputs here carry at most one fault dimension (sender XOR nonce), so the
    reject *class* equality is exact; the double-fault precedence reversal is
    pinned separately in ``test_double_fault_precedence_divergence``.
    """
    # Hermeticity: ``admit`` routes through the authority selector; this binding
    # is meaningful only against the Python single-transition core. Pin the
    # ambient mode so a future surface promotion can't silently change what we
    # are comparing (and turn this into a Rust-binary dependency).
    from src.runtime.authority import AuthorityMode, active_mode

    assert active_mode(REPLAY_GUARD_SURFACE) is AuthorityMode.PYTHON_AUTHORITY

    guard_state = ReplayGuardState()
    nonce_table = NonceTable()

    accepts = 0
    for step, (sender, nonce) in enumerate(EVENT_SEQUENCE):
        # --- single transition (CBC-core, proof/differential-reached) ---
        guard_result = admit(state=guard_state, sender=sender, nonce=nonce)

        # --- live authority (size-1 batch) ---
        ok, reason, updated = _single_batch(nonce_table, sender, nonce)

        if isinstance(guard_result, AdmitAccepted):
            accepts += 1
            assert ok is True, f"step {step}: admit accepted but batch rejected ({reason!r})"
            assert reason is None
            assert updated is not None
            # Resulting accepted-nonce state must agree for the touched sender.
            canon = _canon(sender)
            assert guard_result.state.last_for(canon) == updated.get_last(canon) == nonce
            guard_state = guard_result.state
            nonce_table = updated
        else:
            assert isinstance(guard_result, AdmitRejected)
            assert ok is False, (
                f"step {step}: admit rejected ({guard_result.reason}) but batch accepted"
            )
            assert reason is not None
            assert updated is None  # batch reject => caller keeps prior table
            # Reject-class equivalence (mapped vocabulary).
            assert _admit_class(guard_result.reason) == _batch_class(reason), (
                f"step {step}: reject class mismatch "
                f"admit={guard_result.reason!r} -> {_admit_class(guard_result.reason)!r}; "
                f"batch={reason!r} -> {_batch_class(reason)!r}"
            )
            # Reject-is-no-op: both states unchanged. Thread the PRIOR state
            # forward (do NOT overwrite the table with the validator's None).

    # Global per-sender state equality: the FULL accepted-nonce table must agree
    # across every sender the corpus touched (not just the per-step spot check),
    # so cross-sender leakage inside the corpus would be caught here too.
    from src.core.replay_guard import _canonical_sender

    touched = {
        _canonical_sender(s) for s, _ in EVENT_SEQUENCE if _canonical_sender(s) is not None
    }
    for cs in touched:
        assert guard_state.last_for(cs) == nonce_table.get_last(cs), (
            f"final state mismatch for {cs}: "
            f"guard={guard_state.last_for(cs)} nonces={nonce_table.get_last(cs)}"
        )

    # Non-vacuity: the corpus must accept some and reject some, so a future
    # "reject everything" (or "accept everything") regression cannot pass.
    assert 0 < accepts < len(EVENT_SEQUENCE)


def test_per_sender_isolation_binding():
    """One sender's rejected events must not advance another sender's accepted
    nonce in EITHER implementation. Interleave a stream of A-rejects between two
    B-accepts and assert B's last advances by exactly the B accepts."""
    guard_state = ReplayGuardState()
    nonce_table = NonceTable()

    # B accepts 1, then A suffers gap/dup/stale/invalid, then B accepts 2.
    interleaved: tuple[tuple[object, object], ...] = (
        (SENDER_B, 1),            # B accept -> last_B = 1
        (SENDER_A, 5),            # A gap (last_A = 0)
        (SENDER_A, 0),            # A invalid_nonce
        (BAD_SENDER, 1),          # invalid_sender
        (SENDER_B, 1),            # B duplicate (no advance)
        (SENDER_B, 2),            # B accept -> last_B = 2
    )
    for sender, nonce in interleaved:
        g = admit(state=guard_state, sender=sender, nonce=nonce)
        ok, reason, updated = _single_batch(nonce_table, sender, nonce)
        if isinstance(g, AdmitAccepted):
            assert ok and updated is not None
            guard_state, nonce_table = g.state, updated
        else:
            assert not ok and updated is None

    cb = _canon(SENDER_B)
    ca = _canon(SENDER_A)
    # B advanced to exactly 2 in both; A never advanced past 0 in either.
    assert guard_state.last_for(cb) == nonce_table.get_last(cb) == 2
    assert guard_state.last_for(ca) == nonce_table.get_last(ca) == 0


def test_double_fault_precedence_divergence():
    """GENUINE, safety-neutral divergence (documented, not papered over).

    ``admit`` validates the sender before the nonce (returns ``invalid_sender``);
    the batch validator validates the nonce before the sender (returns
    ``Missing/invalid nonce``). For a double-fault input both still REJECT and
    both still NO-OP — the only difference is which reason is reported. This pins
    the actual divergent codes so the binding is honest about its one seam.
    """
    bad_both_sender = BAD_SENDER
    bad_both_nonce = 0  # below range

    g = admit(state=ReplayGuardState(), sender=bad_both_sender, nonce=bad_both_nonce)
    ok, reason, updated = _single_batch(NonceTable(), bad_both_sender, bad_both_nonce)

    # Both reject, both no-op.
    assert isinstance(g, AdmitRejected)
    assert ok is False and updated is None

    # ...but the reported reason DIVERGES by precedence:
    assert g.reason == REJ_INVALID_SENDER  # admit: sender checked first
    assert reason == BATCH_BAD_NONCE       # batch: nonce checked first
    # Hence the reject CLASSES differ for double-fault inputs — which is exactly
    # why the equivalence harness restricts strict class-equality to single-fault
    # inputs. Safety (reject + no-op) is preserved on both sides.
    assert _admit_class(g.reason) != _batch_class(reason)


class TestBatchWrapperLaw:
    """Pins the multi-element batch wrapper law BY EXAMPLE (not a proof).

    The size-1 binding pins the single-transition. The batch validator is a
    *set*-semantics wrapper: for one sender, a size-k batch accepts iff the
    in-order ``admit``-fold over ``sorted(nonces)`` accepts every element and the
    final accepted nonce matches. These parametrized cases CONSTRAIN that law by
    example for a single sender; they do NOT prove it over all batches, and the
    cross-sender all-or-nothing atomicity (test_cross_sender_atomicity_is_batch_only)
    is documented as a batch-only property that remains UNPROVEN.
    """

    @staticmethod
    def _fold_admit_sorted(start: ReplayGuardState, sender: str, nonces: list[int]):
        """Fold ``admit`` over the SORTED nonces; return (all_accepted, final_state)."""
        state = start
        for n in sorted(nonces):
            r = admit(state=state, sender=sender, nonce=n)
            if isinstance(r, AdmitRejected):
                return False, start  # reject-is-no-op for the whole fold
            state = r.state
        return True, state

    def _batch(self, table: NonceTable, sender: str, nonces: list[int]):
        intents = [_nonce_intent(sender, n) for n in nonces]
        return validate_and_apply_intent_nonce_batch(
            nonces=table, intents=intents, require_all_nonces=True
        )

    @pytest.mark.parametrize(
        "nonces",
        [
            [1, 2, 3],       # contiguous in order -> accept
            [3, 2, 1],       # contiguous out of order -> batch sorts -> accept
            [1, 3],          # gap -> reject
            [2, 3],          # does not start at last+1 -> reject
            [1, 1, 2],       # in-batch duplicate -> reject
            [1, 2, 2, 3],    # in-batch duplicate -> reject
        ],
    )
    def test_size_k_batch_matches_sorted_admit_fold(self, nonces):
        sender = SENDER_A
        ok, _reason, updated = self._batch(NonceTable(), sender, nonces)
        # In-batch duplicates are a batch-only concept; the sorted-admit fold
        # must also reject them (admit would see ``duplicate_nonce``/no advance).
        all_ok, folded = self._fold_admit_sorted(ReplayGuardState(), sender, nonces)
        has_dups = len(nonces) != len(set(nonces))
        if has_dups:
            assert ok is False and updated is None
            return
        assert ok is all_ok, f"batch accept={ok} but sorted-admit-fold accept={all_ok}"
        if ok:
            assert updated is not None
            canon = _canon(sender)
            assert updated.get_last(canon) == folded.last_for(canon) == max(nonces)

    def test_cross_sender_atomicity_is_batch_only(self):
        """A multi-sender batch is all-or-nothing: one sender's bad nonce rejects
        the WHOLE batch (including the otherwise-valid sender). This is a wrapper
        property with no single-transition analogue — documented as residual."""
        intents = [
            _nonce_intent(SENDER_A, 1),  # would accept alone
            _nonce_intent(SENDER_B, 5),  # gap -> rejects the whole batch
        ]
        ok, reason, updated = validate_and_apply_intent_nonce_batch(
            nonces=NonceTable(), intents=intents, require_all_nonces=True
        )
        assert ok is False and updated is None and reason == BATCH_SEQ_INVALID
        # Iterating admit, by contrast, would accept A and only reject B; the
        # batch's atomic rollback of A is the wrapper-level difference.
        ga = admit(state=ReplayGuardState(), sender=SENDER_A, nonce=1)
        assert isinstance(ga, AdmitAccepted)
