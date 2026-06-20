"""Unbiasable-seed source for the neutral tie-break (prototype, isolated).

Provides the per-batch seed that `neutral_tiebreak.py` requires: a value that is
(a) unpredictable until identifiers are locked and (b) hard to bias. Mechanism:
**commit-reveal with punishment** — binding commitments, reveals verified against
them, non-revealers slashed + excluded; the seed is the hash of the canonical
verified reveals. A byte-identical Rust shadow lives in `rust/` (parity vectors
in `seed_parity_vectors.tsv`).

HONEST SCOPE (the load-bearing caveat, per findings H13/H14)
-----------------------------------------------------------
Commit-reveal-with-punishment gives **binding** (a participant cannot change its
value after committing), makes **withholding costly** (a non-revealer forfeits its
bond and is excluded), and yields a **deterministic, replayable** seed. It does
**not** by itself cryptographically eliminate the RANDAO *last-revealer* residual:
an actor holding the final reveal slot(s) still has a reveal-or-withhold choice.
Here that residual is **bonded** — each withholding costs a slash, bounding its
expected value — but cryptographic elimination requires composing this with a
**VDF** over the commitments (so the outcome is not computable in time to decide)
or a **threshold randomness beacon** (drand). This module proves the
commit-reveal-binding + slashing mechanism; the VDF/beacon layer is the next
increment. Do not claim full unbiasability from this module alone.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Iterable, Mapping

COMMIT_DOMAIN = "zenodex.seed_commit/v1"
SEED_DOMAIN = "zenodex.seed/v1"


def _framed(field: bytes) -> bytes:
    """Length-prefixed framing: ``u64_be(len) || field`` (collision-free)."""
    return len(field).to_bytes(8, "big") + field


def commit(value: bytes, nonce: bytes, *, domain: str = COMMIT_DOMAIN) -> bytes:
    """Binding commitment ``sha256(framed(domain) || framed(value) || framed(nonce))``."""
    if not isinstance(value, (bytes, bytearray)):
        raise TypeError("value must be bytes")
    if not isinstance(nonce, (bytes, bytearray)):
        raise TypeError("nonce must be bytes")
    if not isinstance(domain, str) or not domain:
        raise ValueError("domain must be a non-empty str")
    h = hashlib.sha256()
    h.update(_framed(domain.encode("utf-8")))
    h.update(_framed(bytes(value)))
    h.update(_framed(bytes(nonce)))
    return h.digest()


def verify_reveal(commitment: bytes, value: bytes, nonce: bytes, *, domain: str = COMMIT_DOMAIN) -> bool:
    """True iff ``(value, nonce)`` opens ``commitment`` (re-derive and compare)."""
    if not isinstance(commitment, (bytes, bytearray)):
        raise TypeError("commitment must be bytes")
    return bytes(commitment) == commit(value, nonce, domain=domain)


def seed_from_pairs(pairs: Iterable[tuple[str, bytes]], *, seed_domain: str = SEED_DOMAIN) -> bytes:
    """Seed hash over (participant_id, value) pairs, sorted by id UTF-8 bytes.

    ``sha256(framed(seed_domain) || for (id,value) in sorted: framed(id) || framed(value))``.
    The canonical, language-agnostic ordering (sort on UTF-8 bytes) is what lets the
    Rust shadow reproduce this byte-for-byte. This is the cross-language parity surface.
    """
    items = sorted(((pid.encode("utf-8"), bytes(val)) for pid, val in pairs), key=lambda t: t[0])
    h = hashlib.sha256()
    h.update(_framed(seed_domain.encode("utf-8")))
    for id_bytes, value in items:
        h.update(_framed(id_bytes))
        h.update(_framed(value))
    return h.digest()


@dataclass(frozen=True)
class Reveal:
    participant_id: str
    value: bytes
    nonce: bytes


@dataclass(frozen=True)
class SeedResult:
    seed: bytes
    included: tuple[str, ...]  # participants whose reveal verified (sorted)
    slashed: tuple[str, ...]   # committed but did not validly reveal (sorted)


def derive_seed(
    *,
    commitments: Mapping[str, bytes],
    reveals: Iterable[Reveal],
    seed_domain: str = SEED_DOMAIN,
    commit_domain: str = COMMIT_DOMAIN,
) -> SeedResult:
    """Derive the per-batch seed from verified reveals; slash non/invalid-revealers.

    For every committed participant, a reveal is *included* iff it opens that
    participant's commitment; otherwise the participant is *slashed* and excluded.
    The seed is ``sha256(framed(seed_domain) || for id in sorted(included):
    framed(id) || framed(value))``, sorted by the participant id's UTF-8 bytes
    (language-agnostic order). Deterministic / replayable. Raises if no reveal is
    valid (a batch with no usable entropy must fail closed, not seed from nothing).
    """
    if not commitments:
        raise ValueError("commitments must be non-empty")
    reveals_by_id: dict[str, list[Reveal]] = {}
    for r in reveals:
        if not isinstance(r, Reveal):
            raise TypeError("reveals must be Reveal instances")
        reveals_by_id.setdefault(r.participant_id, []).append(r)

    included_pairs: list[tuple[str, bytes]] = []
    slashed: list[str] = []
    for pid, c in commitments.items():
        # Order-independent + griefing-resistant: a participant is included iff
        # ANY of its reveals validly opens its commitment. A commitment binds a
        # unique (value, nonce), so at most one *distinct* reveal can open it and
        # the included value is deterministic regardless of duplicate/adversarial
        # reveals or their iteration order. Otherwise the participant is slashed.
        opener = next(
            (r for r in reveals_by_id.get(pid, [])
             if verify_reveal(c, r.value, r.nonce, domain=commit_domain)),
            None,
        )
        if opener is not None:
            included_pairs.append((pid, bytes(opener.value)))
        else:
            slashed.append(pid)

    if not included_pairs:
        raise ValueError("no valid reveal — fail closed (no seed from zero entropy)")

    seed = seed_from_pairs(included_pairs, seed_domain=seed_domain)
    return SeedResult(
        seed=seed,
        included=tuple(sorted(pid for pid, _v in included_pairs)),
        slashed=tuple(sorted(slashed)),
    )
