"""Grinding-resistant deterministic tie-break key for settlement ordering.

Promoted (consensus-critical) from ``experiments/neutral_tiebreak_v1/``. The
spot batch-clearing canonical order breaks (A, B) ties on the tuple of
participant-chosen ``intent_id`` strings (``batch_clearing_ordering._ab_ordering_key``),
so a participant can grind a small ``intent_id`` to win ties. This module
provides the grinding-resistant replacement: a tie-break token derived from a
per-batch ``seed`` and the identifier.

    token(seed, id) = sha256( domain_sep("zenodex.neutral_tiebreak")
                              || encode_bytes(seed) || encode_bytes(id_utf8) )

using the repo's canonical framing (``domain_sep_bytes`` + length-prefixed
``encode_bytes``), so it composes with the existing canonical encoders. Pure and
deterministic: equal inputs replay to the same token (consensus-safe).

Given a ``seed`` that is unpredictable until identifiers are locked, the win
probability over identifier choices is ~uniform, so grinding the identifier gives
no advantage. **The seed-production obligation is separate and load-bearing**: the
seed must be unpredictable-until-locked AND unbiasable at production (a public
pre-fixed seed is still grindable; a last-revealer-biasable seed degrades it). An
unbiasable, late-bound seed comes from a commit-reveal-with-punishment + VDF /
threshold beacon. This module is the tie-break mechanism only.
"""

from __future__ import annotations

from ..state.canonical import domain_sep_bytes, encode_bytes, sha256_hex

DOMAIN = "zenodex.neutral_tiebreak"


def neutral_tiebreak_key(seed: bytes, identifier: str, *, domain: str = DOMAIN) -> str:
    """Grinding-resistant tie-break token (hex digest) for ``identifier``.

    A pure, deterministic function of ``(seed, identifier)`` using canonical
    framing. Returned as a hex string so it slots directly into the existing
    ``tuple[str, ...]`` tie-break comparison without changing its type.
    """
    if not isinstance(seed, (bytes, bytearray)):
        raise TypeError("seed must be bytes")
    if not isinstance(identifier, str):
        raise TypeError("identifier must be a str")
    if not isinstance(domain, str) or not domain:
        raise ValueError("domain must be a non-empty str")
    preimage = (
        domain_sep_bytes(domain)
        + encode_bytes(bytes(seed))
        + encode_bytes(identifier.encode("utf-8"))
    )
    return sha256_hex(preimage)


def tiebreak_token(identifier: str, seed: bytes | None) -> str:
    """The tie-break token for ``identifier``: the raw id when ``seed is None``
    (today's grindable behavior — unchanged), else the seeded key.

    This is the single seam used by ``batch_clearing_ordering._ab_ordering_key``:
    with ``seed=None`` the canonical order is byte-identical to the pre-seam code.
    """
    if not isinstance(identifier, str):
        raise TypeError("identifier must be a str")
    return identifier if seed is None else neutral_tiebreak_key(seed, identifier)
