"""Deterministic tests for the grinding-resistant tie-break prototype.

Run: ``pytest experiments/neutral_tiebreak_v1/test_neutral_tiebreak.py``

Every test is deterministic: the statistical anti-grinding test draws its random
seeds from a fixed-seed RNG so the pass/fail is reproducible.
"""

from __future__ import annotations

import os
import random

import pytest

from neutral_tiebreak import (
    ab_key_lex,
    ab_key_seeded,
    best_seeded_grinding_winrate,
    committed_seed_tiebreak_key,
    lex_grinding_winrate,
    order_identifiers,
    winner,
)

HONEST = [f"intent-{i:04d}" for i in range(7)]  # field size 8 with one grinder
FAIR_RATE = 1.0 / (len(HONEST) + 1)             # = 0.125


def _seeds(n: int, *, rng_seed: int = 1234) -> list[bytes]:
    rng = random.Random(rng_seed)
    return [rng.randbytes(32) for _ in range(n)]


# --- Determinism / replay (consensus safety) ------------------------------

def test_order_is_pure_and_replayable():
    seed = b"\x11" * 32
    ids = list(HONEST)
    first = order_identifiers(ids, seed=seed)
    for _ in range(5):
        assert order_identifiers(ids, seed=seed) == first
    # Input order must not matter (set-determinism).
    assert order_identifiers(list(reversed(ids)), seed=seed) == first


def test_seeded_key_is_deterministic():
    a = committed_seed_tiebreak_key(b"seed", "intent-0001")
    b = committed_seed_tiebreak_key(b"seed", "intent-0001")
    assert a == b and len(a) == 32


def test_framing_is_collision_free():
    # The exact pair that collided under the old `|| 0x00 ||` framing.
    a = committed_seed_tiebreak_key(b"a\x00b", "c")
    b = committed_seed_tiebreak_key(b"a", "b\x00c")
    assert a != b


def test_python_matches_golden_vectors():
    # The shared parity_vectors.tsv is the cross-language contract: the Rust
    # shadow (rust/tests/parity.rs) recomputes the same vectors. Both sides
    # assert against this single file, so any Python/Rust drift is caught.
    path = os.path.join(os.path.dirname(__file__), "parity_vectors.tsv")
    n = 0
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")  # NOT strip(): empty seed/id fields are leading tabs
            if not line:
                continue
            seed_hex, id_hex, key_hex = line.split("\t")
            seed = bytes.fromhex(seed_hex)
            ident = bytes.fromhex(id_hex).decode("utf-8")
            assert committed_seed_tiebreak_key(seed, ident).hex() == key_hex
            n += 1
    assert n >= 7


# --- The current rule is fully grindable ----------------------------------

def test_lex_rule_is_fully_grindable():
    # A grinder who picks their own intent_id always wins ties under lex order.
    assert lex_grinding_winrate(HONEST) == 1.0


# --- The seeded rule resists grinding (statistical, deterministic) ---------

def test_seeded_rule_resists_grinding():
    seeds = _seeds(3000)
    candidates = [f"grind-{i:04d}" for i in range(50)]
    best = best_seeded_grinding_winrate(HONEST, candidates, seeds)
    # Grinding the identifier cannot beat fair odds by more than sampling noise.
    assert best < FAIR_RATE + 0.05, f"grinding win-rate {best:.3f} too high"
    # And it is nowhere near the lex rule's guaranteed win.
    assert best < 0.30


def test_seeded_rule_is_fair_to_honest_ids():
    # Each id is the winner ~1/k of the time over random seeds.
    seeds = _seeds(4000)
    field = list(HONEST) + ["grind-0000"]
    counts = {i: 0 for i in field}
    for s in seeds:
        counts[winner(field, seed=s)] += 1
    for i, c in counts.items():
        rate = c / len(seeds)
        assert abs(rate - FAIR_RATE) < 0.03, f"{i} win-rate {rate:.3f} off-fair"


def test_seed_binding_reshuffles_order():
    # Different seeds generally produce different orders, so a participant who
    # cannot predict the seed cannot predict the order.
    ids = list(HONEST)
    distinct = {tuple(order_identifiers(ids, seed=bytes([k]) * 32)) for k in range(20)}
    assert len(distinct) > 1


# --- The (A, B) objective is preserved; only genuine ties are reseeded -----

def test_ab_objective_preserved_when_not_tied():
    # When (A, B) differ, the seeded key orders identically to the lex key:
    # the tie-break component is never consulted.
    seed = b"\x22" * 32
    rows = [
        (100, 5, "z-last"),    # a=100 b=5
        (100, 9, "a-first"),   # a=100 b=9  (higher surplus)
        (200, 5, "m-mid"),     # a=200 b=5  (higher volume)
    ]
    lex_order = sorted(rows, key=lambda r: ab_key_lex(*r))
    seeded_order = sorted(rows, key=lambda r: ab_key_seeded(r[0], r[1], r[2], seed))
    assert [r[2] for r in lex_order] == [r[2] for r in seeded_order]


def test_only_genuine_ties_can_reorder():
    # Two rows tied on (A, B) may order differently under the seeded rule than
    # under lex -- that is the whole point. Find a seed that flips them.
    a, b = 100, 5
    x, y = "intent-aaaa", "intent-bbbb"
    lex = sorted([x, y], key=lambda i: ab_key_lex(a, b, i))
    assert lex == [x, y]  # lex: x before y (grindable)
    flipped = any(
        sorted([x, y], key=lambda i: ab_key_seeded(a, b, i, bytes([k]) * 32)) == [y, x]
        for k in range(64)
    )
    assert flipped, "seeded rule never reorders a genuine tie -- unexpected"


# --- Input validation (fail-closed) ---------------------------------------

def test_rejects_bad_inputs():
    with pytest.raises(TypeError):
        committed_seed_tiebreak_key("not-bytes", "id")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        committed_seed_tiebreak_key(b"seed", 123)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        committed_seed_tiebreak_key(b"seed", "id", domain_sep="")
    with pytest.raises(ValueError):
        winner([], seed=None)
