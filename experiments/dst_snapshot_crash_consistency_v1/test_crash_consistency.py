"""Exhaustive crash-consistency tests for the DexState snapshot commit.

Run: PYTHONPATH=. pytest experiments/dst_snapshot_crash_consistency_v1/test_crash_consistency.py
"""

from __future__ import annotations

import json
import random

from crash_consistency import (
    corrupt_byte,
    persisted_demo,
    recover_and_verify,
    torn_at,
)


def test_intact_snapshot_is_accepted_and_round_trips():
    committed, payload, v = persisted_demo()
    r = recover_and_verify(committed, payload, v)
    assert r.accepted and r.reason == "ok"


def test_every_torn_write_is_rejected():
    # A crash at ANY offset before the end leaves truncated bytes -> rejected.
    # Only the complete payload (offset == len) is ever accepted.
    committed, payload, v = persisted_demo()
    for offset in range(0, len(payload)):
        assert not recover_and_verify(committed, torn_at(payload, offset), v).accepted, offset
    assert recover_and_verify(committed, payload, v).accepted


def test_every_single_byte_corruption_is_rejected():
    # EXHAUSTIVE over EVERY single-byte fault: every position x every other byte
    # value (len * 255 candidates) -- none is ever silently accepted.
    committed, payload, v = persisted_demo()
    for pos in range(len(payload)):
        orig = payload[pos]
        for new in range(256):
            if new == orig:
                continue
            assert not recover_and_verify(committed, corrupt_byte(payload, pos, new), v).accepted, (pos, new)


def test_corruption_that_stays_valid_json_is_still_rejected():
    # The load-bearing crash-consistency property: even a corruption that remains
    # valid JSON (a different *plausible* state — bit-rot inside a quoted address)
    # is rejected by the commitment, never silently loaded as authoritative.
    committed, payload, v = persisted_demo()
    s = payload.decode("utf-8")
    flipped = None
    for i, c in enumerate(s):
        if c in "abcdef":  # hex letter inside a quoted string -> any letter is valid JSON
            cand = (s[:i] + ("e" if c != "e" else "a") + s[i + 1:]).encode("utf-8")
            try:
                json.loads(cand.decode("utf-8"))
            except Exception:
                continue
            if cand != payload:
                flipped = cand
                break
    assert flipped is not None, "expected to find a valid-JSON corruption"
    r = recover_and_verify(committed, flipped, v)
    assert (not r.accepted) and r.reason == "commitment_mismatch"


def test_recovery_is_deterministic_replay():
    # DST determinism: the same on-disk bytes yield the same recovery verdict every time.
    committed, payload, v = persisted_demo()
    corrupt = corrupt_byte(payload, 5, payload[5] ^ 0xFF)
    r1 = recover_and_verify(committed, corrupt, v)
    r2 = recover_and_verify(committed, corrupt, v)
    assert r1 == r2 and not r1.accepted


def test_seeded_multibyte_corruption_never_accepted():
    # Seed-reproducible multi-byte fault sweep: no random 1..8-byte corruption is accepted.
    committed, payload, v = persisted_demo()
    rng = random.Random(12345)
    for _ in range(500):
        b = bytearray(payload)
        for _ in range(rng.randint(1, 8)):
            b[rng.randint(0, len(b) - 1)] = rng.randint(0, 255)
        cand = bytes(b)
        if cand == payload:  # astronomically unlikely; keep it honest
            continue
        assert not recover_and_verify(committed, cand, v).accepted
