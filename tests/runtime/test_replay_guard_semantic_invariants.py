"""Independent **semantic invariants** for the replay/idempotency guard.

Like the fee-router invariants, these run against the Python authority alone —
not as a Python/Rust differential — so they catch a bug present identically in
both runtimes. The headline property is **per-sender isolation**: one sender's
nonce stream can neither advance nor block another's, the replay-guard analogue
of the fee-router's per-`(source, asset)` isolation.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random
from collections import defaultdict

from src.core.replay_guard import (
    AdmitAccepted,
    AdmitRejected,
    ReplayGuardState,
    admit,
)

SENDERS = ["0x" + f"{tag:02x}" * 48 for tag in (0xA0, 0xB0, 0xC0, 0xD0)]


def _run(calls):
    """Apply (sender, nonce) calls; return (state, decisions_by_sender)."""
    state = ReplayGuardState()
    decisions: dict[str, list[tuple[int, bool]]] = defaultdict(list)
    for sender, nonce in calls:
        result = admit(state=state, sender=sender, nonce=nonce)
        accepted = isinstance(result, AdmitAccepted)
        if accepted:
            state = result.state
        decisions[sender].append((nonce, accepted))
    return state, decisions


def _mixed_calls(seed: int, n: int = 250):
    rng = random.Random(seed)
    return [(rng.choice(SENDERS), rng.randint(1, 6)) for _ in range(n)]


# --- I1: per-sender isolation (no cross-sender interference) ------------------


def test_no_cross_sender_interference():
    calls = _mixed_calls(seed=4242)
    _, mixed = _run(calls)

    per_sender: dict[str, list] = defaultdict(list)
    for sender, nonce in calls:
        per_sender[sender].append((sender, nonce))

    for sender, sub in per_sender.items():
        _, alone = _run(sub)
        assert alone[sender] == mixed[sender], (
            f"sender {sender[:8]} decisions changed when other senders were interleaved"
        )


def test_one_senders_history_does_not_admit_anothers_first_nonce_out_of_order():
    # Advance A far; B's first admissible nonce must still be exactly 1.
    state = ReplayGuardState()
    for n in range(1, 6):
        state = admit(state=state, sender=SENDERS[0], nonce=n).state
    assert isinstance(admit(state=state, sender=SENDERS[1], nonce=5), AdmitRejected)
    assert admit(state=state, sender=SENDERS[1], nonce=5).reason == "nonce_gap"
    assert isinstance(admit(state=state, sender=SENDERS[1], nonce=1), AdmitAccepted)


# --- I2: monotonic acceptance (accepted nonces are exactly 1,2,3,...) ---------


def test_accepted_nonces_form_a_gapless_prefix_per_sender():
    _, decisions = _run(_mixed_calls(seed=7))
    for sender, seq in decisions.items():
        accepted = [n for (n, ok) in seq if ok]
        assert accepted == list(range(1, len(accepted) + 1)), (sender[:8], accepted)


# --- I3: anti-replay / idempotency -------------------------------------------


def test_any_nonce_at_or_below_last_is_rejected():
    rng = random.Random(3)
    state = ReplayGuardState()
    last = 0
    for _ in range(60):
        if last == 0 or rng.random() < 0.6:
            # advance
            result = admit(state=state, sender=SENDERS[0], nonce=last + 1)
            assert isinstance(result, AdmitAccepted)
            state = result.state
            last += 1
        else:
            replay = rng.randint(1, last)
            result = admit(state=state, sender=SENDERS[0], nonce=replay)
            assert isinstance(result, AdmitRejected)
            assert result.reason in ("duplicate_nonce", "stale_nonce")


# --- I4: rejection is a no-op on state ---------------------------------------


def test_rejected_admissions_never_change_state():
    state = ReplayGuardState()
    state = admit(state=state, sender=SENDERS[0], nonce=1).state
    root = state.state_root()
    for sender, nonce in [
        (SENDERS[0], 1),  # duplicate
        (SENDERS[0], 5),  # gap
        ("0xzz" + "11" * 47, 1),  # invalid sender
        (SENDERS[0], 0),  # invalid nonce
        (SENDERS[1], 7),  # other sender, gap
    ]:
        result = admit(state=state, sender=sender, nonce=nonce)
        assert isinstance(result, AdmitRejected)
        # The caller keeps the prior state; its root is unchanged.
        assert state.state_root() == root


# --- I5: order independence of the final state across distinct senders --------


def test_final_state_independent_of_inter_sender_ordering():
    # Each sender's own nonces stay in order, but the senders are shuffled.
    base = []
    for sender in SENDERS:
        for n in range(1, 5):
            base.append((sender, n))

    state_a, _ = _run(base)

    rng = random.Random(123)
    # A different interleaving that keeps each sender's own nonces in order.
    buckets = defaultdict(list)
    for sender, n in base:
        buckets[sender].append((sender, n))
    order = []
    pointers = {s: 0 for s in buckets}
    remaining = sum(len(v) for v in buckets.values())
    while remaining:
        s = rng.choice([s for s in buckets if pointers[s] < len(buckets[s])])
        order.append(buckets[s][pointers[s]])
        pointers[s] += 1
        remaining -= 1

    state_b, _ = _run(order)
    assert state_a.state_root() == state_b.state_root()
