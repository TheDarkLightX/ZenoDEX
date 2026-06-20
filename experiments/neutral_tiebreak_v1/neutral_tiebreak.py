"""Grinding-resistant deterministic tie-break primitive (prototype, isolated).

Roadmap item 1a (``internal/ZENODEX_RESEARCH_BUILDOUT_ROADMAP_2026-06-18.md``),
grounded in research findings H12 (Algorand VRF sortition), H14 (RANDAO
last-revealer grinding), H15 (Aequitas order-fairness). This module is an
ISOLATED prototype: it is not wired into any consensus path. A byte-identical
Rust shadow lives in ``rust/`` with cross-language parity vectors
(``parity_vectors.tsv``).

PROBLEM
-------
ZenoDex breaks ties on participant-chosen identifiers:

* spot batch clearing -- the greedy key's final component is ``str(intent_id)``
  (``src/core/batch_clearing_ordering.py:211``: ``candidate_key = (b, -a, str(intent_id))``);
* proof mining / improvement-bounty routing -- ties resolve on a ``miner_id``
  (``tools/gpu_jobs/improvement_bounty_round_route_v1.py``);
* sealed-bid auctions -- equal-remainder leftovers are ranked by a key that
  includes ``bidder_id`` and ``commitment`` (``src/core/sealed_bid_auction.py``).

In each case a participant who can choose their identifier can GRIND it to win
ties deterministically (pick a small identifier). This is the "selectable
tie-break" / "biased hash tie-break" concern.

FIX (this module)
-----------------
Replace only the identifier component of the tie-break with a key derived from a
per-batch SEED, using collision-free length-prefixed framing::

    framed(x)          = u64_be(len(x)) || x
    tiebreak_key(s, id) = sha256( framed(domain_sep) || framed(s) || framed(id) )

Only the final identifier component changes; the primary objective components are
preserved byte-for-byte. The key is a pure deterministic function of (seed, id),
so it is consensus-safe: the same inputs replay to the same order with no live
randomness.

COMPOSITION REQUIREMENT (NOT solved here)
-----------------------------------------
Grinding-resistance holds ONLY if ``seed`` is, at production time, BOTH:

* **unpredictable / unavailable** until all identifiers are locked -- otherwise a
  participant computes ``tiebreak_key`` offline and grinds their id; and
* **unbiasable** -- otherwise the actor who fixes the seed (e.g. the last revealer,
  RANDAO H14) chooses a favorable one.

A public or pre-committed-but-readable seed fixed *before* identifiers are chosen
is still grindable. An unbiasable, late-bound seed must come from a VRF, a
commit-reveal-with-punishment, or a threshold randomness beacon (H12/H13) -- a
separate, composed obligation. This module proves only the tie-break MECHANISM
given such a seed; it does not produce the seed.
"""

from __future__ import annotations

import hashlib
from typing import Sequence

DOMAIN_SEP = "zenodex.neutral_tiebreak/v1"


def _framed(field: bytes) -> bytes:
    """Length-prefixed framing: ``u64_be(len) || field`` (collision-free)."""
    return len(field).to_bytes(8, "big") + field


# --- Tie-break keys -------------------------------------------------------

def lex_tiebreak_key(identifier: str) -> str:
    """Model the CURRENT (grindable) tie-break: the raw participant identifier.

    Smaller identifiers win ties, so a participant who picks their own
    ``identifier`` can always win by choosing a small one.
    """
    if not isinstance(identifier, str):
        raise TypeError("identifier must be a str")
    return identifier


def committed_seed_tiebreak_key(
    seed: bytes, identifier: str, *, domain_sep: str = DOMAIN_SEP
) -> bytes:
    """Grinding-resistant tie-break key over length-prefixed framed fields.

    ``sha256( framed(domain_sep) || framed(seed) || framed(identifier) )``.
    Pure and deterministic. ``seed`` must be unpredictable until identifiers are
    locked AND unbiasable at production (see the module COMPOSITION REQUIREMENT).
    """
    if not isinstance(seed, (bytes, bytearray)):
        raise TypeError("seed must be bytes")
    if not isinstance(identifier, str):
        raise TypeError("identifier must be a str")
    if not isinstance(domain_sep, str) or not domain_sep:
        raise ValueError("domain_sep must be a non-empty str")
    h = hashlib.sha256()
    h.update(_framed(domain_sep.encode("utf-8")))
    h.update(_framed(bytes(seed)))
    h.update(_framed(identifier.encode("utf-8")))
    return h.digest()


# --- Composite (objective + tie-break) keys (the real drop-in shape) ------

def _checked_int(value: int, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return value


def ab_key_lex(volume_a: int, surplus_b: int, identifier: str) -> tuple[int, int, str]:
    """Model the current greedy composite key SHAPE ``(b, -a, str(intent_id))``.

    Mirrors ``batch_clearing_ordering.py:211``, which selects the *minimum* of
    this tuple. The first two components encode that path's exact objective
    direction (minimize ``b``, then maximize ``a``); this prototype does not
    re-judge that direction. The point of interest is the THIRD component -- the
    grindable identifier -- which is the only thing replaced. (Note: a separate
    global-AB ordering path uses a different key; this models the greedy key.)
    """
    return (_checked_int(surplus_b, "surplus_b"), -_checked_int(volume_a, "volume_a"),
            lex_tiebreak_key(identifier))


def ab_key_seeded(
    volume_a: int, surplus_b: int, identifier: str, seed: bytes,
    *, domain_sep: str = DOMAIN_SEP,
) -> tuple[int, int, bytes]:
    """Same composite key, with the final tie-break replaced by the seeded key.

    The first two components are preserved byte-for-byte vs ``ab_key_lex``; only
    the third changes from a grindable identifier to a grinding-resistant key.
    """
    return (
        _checked_int(surplus_b, "surplus_b"),
        -_checked_int(volume_a, "volume_a"),
        committed_seed_tiebreak_key(seed, identifier, domain_sep=domain_sep),
    )


# --- Deterministic ordering ----------------------------------------------

def order_identifiers(identifiers: Sequence[str], *, seed: bytes | None) -> list[str]:
    """Deterministically order identifiers by the tie-break.

    ``seed is None`` reproduces the current grindable lexicographic order;
    a non-``None`` seed uses the grinding-resistant seeded key. Pure function:
    equal inputs always yield the identical list (consensus-safe replay).
    """
    if seed is None:
        return sorted(identifiers, key=lex_tiebreak_key)
    return sorted(identifiers, key=lambda i: committed_seed_tiebreak_key(seed, i))


def winner(identifiers: Sequence[str], *, seed: bytes | None) -> str:
    """The single winner (smallest tie-break key)."""
    ordered = order_identifiers(identifiers, seed=seed)
    if not ordered:
        raise ValueError("identifiers must be non-empty")
    return ordered[0]


# --- Analysis helpers (used by tests / the design doc) --------------------

def lex_grinding_winrate(honest_ids: Sequence[str]) -> float:
    """Win-rate a grinder achieves against ``honest_ids`` under the lex rule.

    Returns ``1.0``: the grinder picks the empty identifier ``""`` (which sorts
    before any non-empty id) and wins every tie. Requires non-empty honest ids
    (an empty honest id is degenerate -- nothing sorts before it).
    """
    if not honest_ids:
        raise ValueError("honest_ids must be non-empty")
    if any((not isinstance(i, str)) or i == "" for i in honest_ids):
        raise ValueError("honest_ids must all be non-empty strings")
    grind_id = ""  # strictly smaller than every non-empty honest id
    return 1.0 if winner(list(honest_ids) + [grind_id], seed=None) == grind_id else 0.0


def best_seeded_grinding_winrate(
    honest_ids: Sequence[str], candidate_ids: Sequence[str], seeds: Sequence[bytes]
) -> float:
    """Best win-rate a grinder can reach under the SEEDED rule.

    The grinder may pick any ``candidate_id`` offline, but does not know which
    ``seed`` will be used. For each candidate, measure its win-rate against
    ``honest_ids`` over ``seeds``; return the maximum. With an unbiasable,
    late-bound seed this stays near ``1/(len(honest_ids)+1)`` -- grinding gives
    no advantage.
    """
    if not seeds:
        raise ValueError("seeds must be non-empty")
    best = 0.0
    for cand in candidate_ids:
        field = list(honest_ids) + [cand]
        wins = sum(1 for s in seeds if winner(field, seed=s) == cand)
        best = max(best, wins / len(seeds))
    return best
