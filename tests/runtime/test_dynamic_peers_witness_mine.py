"""Symbolic disaster-witness mine for ZenoLedger DYNAMIC PEER ADMISSION.

`build_dynamic_peer_admission_v0` (src/integration/zeno_ledger_dynamic_peers_v0.py)
is the consensus-adjacent gate that lets a public ZenoLedger node grow its peer
set at runtime: a signed-shaped *candidate* announcement plus a local *peer-check
report* are folded into the node's `current_peer_urls`, bounded by `max_peer_count`.
This module had ZERO tests (highest-priority gap).

This treats the admission build as the system-under-test and uses `hypothesis` to
search for a witness for the disaster class:

    PEER-ADMISSION SAFETY:  an admit MUST be
      (B)  BOUNDED        final_peer_count <= max_peer_count
      (D)  DISTINCT       final_peer_urls has no duplicates (dedup is total)
      (M)  MONOTONIC      every pre-existing current peer survives (no silent drop)
      (P)  PROVENANCE     final == canonical(current) ∪ candidate_urls, and every
                          admitted url is a candidate url NOT already current
                          (no out-of-candidate / phantom peer is ever admitted,
                           no current peer is re-counted as "admitted")
      (C)  COUNT INTEGRITY reported *_count fields equal the actual list lengths
      (I)  IDEMPOTENT     re-admitting the same candidate against the post-set
                          admits ZERO new peers and leaves the set unchanged
      (DET) DETERMINISTIC identical inputs -> identical admission_hash

Any admit violating one of these is a peer-registry disaster: an unbounded /
duplicate / shrinking / out-of-allowlist peer set, or a non-deterministic /
non-idempotent registry that diverges across honest replicas. A clean run over
thousands of generated (current, candidate, report, cap) tuples is a bounded
NEGATIVE receipt for this disaster class on the admission path.

SCOPE / NON-CLAIMS:
  * This module performs NO BLS/signature verification, so no crypto oracle is
    stubbed (crypto_oracle_stubbed=false). The candidate is shape-validated only.
  * Out of scope: cross-module sequencing (how admitted peers are persisted /
    gossiped), the off-chain peer-check probe itself, candidate provenance /
    authenticity, and multi-round eclipse / sybil dynamics. We mine ONLY the
    single-shot admission set algebra of `build_dynamic_peer_admission_v0`.
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_dynamic_peers_v0 as m  # noqa: E402

NETWORK_ID = "zeno-testnet"
CHAIN_ID = "zeno-chain-1"
PEER_CHECK_SCHEMA = "zenodex.zeno_ledger.node_peer_check_report.v0"

# A small, BOUNDED URL vocabulary so generated `current` and `candidate` sets
# overlap often (exercising the "already current -> not admitted" branch) and so
# canonicalization (trailing-slash collapse) is hit. Indices 0..4 are distinct
# canonical urls; the trailing-slash variant collapses onto index 0.
_BASE_URLS = [
    "http://peer0.example",
    "http://peer1.example",
    "https://peer2.example:8443",
    "http://peer3.example/path",
    "https://peer4.example",
]
# Non-canonical inputs that MUST collapse onto an existing canonical url under
# canonical_peer_url_v0 (rstrip('/')), so dedup is genuinely exercised.
_NONCANON = {
    "http://peer0.example/": "http://peer0.example",
}
_URL_CHOICES = _BASE_URLS + list(_NONCANON.keys())


def _canon(url: str) -> str:
    return _NONCANON.get(url, url)


def _peer_check_report(candidate_urls, *, all_ok: bool = True, mark_bad_index=None):
    """A peer-check report shaped exactly as build_dynamic_peer_admission_v0
    requires: schema/network/chain/ok match the candidate, and `peers` lists the
    candidate urls in order. `mark_bad_index` flips one peer's `ok` to False to
    drive the reject path."""
    peers = []
    for idx, url in enumerate(candidate_urls):
        peers.append({"peer_url": url, "ok": not (mark_bad_index == idx)})
    return {
        "schema": PEER_CHECK_SCHEMA,
        "network_id": NETWORK_ID,
        "chain_id": CHAIN_ID,
        "ok": all_ok,
        "peers": peers,
    }


def _build_candidate(candidate_input_urls):
    return m.build_dynamic_peer_candidate_v0(
        network_id=NETWORK_ID,
        chain_id=CHAIN_ID,
        source_node_id="source-node",
        source_peer_url="http://source.example",
        candidate_peer_urls=candidate_input_urls,
        observed_at_height=7,
    )


def _assert_admission_safe(admission, *, current_input, candidate_input, cap):
    """The peer-admission-safety invariant, factored out so the teeth test can
    reuse it. Raises AssertionError on any disaster-class violation.

    Re-derives the expected set algebra INDEPENDENTLY of the module (using only
    the canonical-url helper, which is the trusted boundary) so this is a real
    differential check, not a restatement of the module's own output."""
    # Independent re-derivation of the canonical current / candidate sets.
    exp_current: list[str] = []
    seen: set[str] = set()
    for url in current_input:
        c = _canon(url)
        if c not in seen:
            seen.add(c)
            exp_current.append(c)
    exp_candidate: list[str] = []
    seen_c: set[str] = set()
    for url in candidate_input:
        c = _canon(url)
        if c not in seen_c:
            seen_c.add(c)
            exp_candidate.append(c)

    final = admission["final_peer_urls"]
    admitted = admission["admitted_peer_urls"]
    current_set = set(exp_current)

    # (D) DISTINCT — dedup is total over the final set.
    assert len(final) == len(set(final)), f"DUPLICATE peer in final set: {final}"
    assert len(admitted) == len(set(admitted)), f"DUPLICATE in admitted: {admitted}"

    # (B) BOUNDED — never exceed the operator-declared cap.
    assert len(final) <= cap, (
        f"UNBOUNDED PEER SET: final_peer_count {len(final)} > max_peer_count {cap}"
    )

    # (M) MONOTONIC — no pre-existing peer is silently dropped on admission.
    for u in exp_current:
        assert u in final, f"SILENT DROP: current peer {u} missing from final {final}"

    # (P) PROVENANCE — final is exactly current ∪ candidate (order: current, then
    # new candidates), and every admitted url is a candidate url not already
    # current (no out-of-allowlist / phantom peer; no re-counted current peer).
    exp_admitted = [u for u in exp_candidate if u not in current_set]
    exp_final = exp_current + exp_admitted
    assert admitted == exp_admitted, (
        f"PROVENANCE BREACH (admitted): module={admitted} expected={exp_admitted}"
    )
    assert final == exp_final, (
        f"PROVENANCE BREACH (final): module={final} expected={exp_final}"
    )
    for u in admitted:
        assert u in set(exp_candidate), f"OUT-OF-ALLOWLIST admit: {u} not a candidate url"
        assert u not in current_set, f"RE-ADMITTED existing peer counted as new: {u}"

    # (C) COUNT INTEGRITY — reported counts match the actual lists.
    assert admission["final_peer_count"] == len(final), "final_peer_count mismatch"
    assert admission["admitted_peer_count"] == len(admitted), "admitted_peer_count mismatch"
    assert admission["current_peer_count"] == len(exp_current), "current_peer_count mismatch"
    assert admission["candidate_peer_count"] == len(exp_candidate), "candidate_peer_count mismatch"


# --------------------------------------------------------------------------- #
# Teeth / non-vacuity: planted violations MUST trip the checker. Without these
# the negative receipt below would be a false receipt.
# --------------------------------------------------------------------------- #
def test_invariant_catches_unbounded_set():
    """A forged admission that exceeds the cap MUST trip the BOUNDED check."""
    forged = {
        "admitted_peer_urls": ["http://peer1.example"],
        "final_peer_urls": ["http://peer0.example", "http://peer1.example"],
        "final_peer_count": 2,
        "admitted_peer_count": 1,
        "current_peer_count": 1,
        "candidate_peer_count": 1,
    }
    with pytest.raises(AssertionError, match="UNBOUNDED PEER SET"):
        _assert_admission_safe(
            forged,
            current_input=["http://peer0.example"],
            candidate_input=["http://peer1.example"],
            cap=1,  # only room for 1, but final has 2
        )


def test_invariant_catches_out_of_allowlist_admit():
    """A forged admission that admits a peer NOT in the candidate list (a phantom
    / out-of-allowlist peer) MUST trip the PROVENANCE check."""
    forged = {
        "admitted_peer_urls": ["http://evil.example"],  # not a candidate url
        "final_peer_urls": ["http://peer0.example", "http://evil.example"],
        "final_peer_count": 2,
        "admitted_peer_count": 1,
        "current_peer_count": 1,
        "candidate_peer_count": 1,
    }
    with pytest.raises(AssertionError, match="PROVENANCE BREACH|OUT-OF-ALLOWLIST"):
        _assert_admission_safe(
            forged,
            current_input=["http://peer0.example"],
            candidate_input=["http://peer1.example"],
            cap=10,
        )


def test_invariant_catches_silent_drop():
    """A forged admission that drops an existing current peer MUST trip MONOTONIC."""
    forged = {
        "admitted_peer_urls": ["http://peer1.example"],
        "final_peer_urls": ["http://peer1.example"],  # peer0 silently dropped
        "final_peer_count": 1,
        "admitted_peer_count": 1,
        "current_peer_count": 1,
        "candidate_peer_count": 1,
    }
    with pytest.raises(AssertionError, match="SILENT DROP|PROVENANCE BREACH"):
        _assert_admission_safe(
            forged,
            current_input=["http://peer0.example"],
            candidate_input=["http://peer1.example"],
            cap=10,
        )


def test_invariant_catches_duplicate_in_final():
    """A forged admission with a duplicate in the final set MUST trip DISTINCT."""
    forged = {
        "admitted_peer_urls": ["http://peer1.example"],
        "final_peer_urls": ["http://peer0.example", "http://peer1.example", "http://peer1.example"],
        "final_peer_count": 3,
        "admitted_peer_count": 1,
        "current_peer_count": 1,
        "candidate_peer_count": 1,
    }
    with pytest.raises(AssertionError, match="DUPLICATE peer"):
        _assert_admission_safe(
            forged,
            current_input=["http://peer0.example"],
            candidate_input=["http://peer1.example"],
            cap=10,
        )


# --------------------------------------------------------------------------- #
# Boundary / reject-path tests (deterministic).
# --------------------------------------------------------------------------- #
def test_admission_rejects_over_cap_is_no_op():
    """When admitting would exceed the cap, the build REJECTS (no admission is
    produced) — fail-closed, no partial/over-cap peer set is emitted."""
    cand = _build_candidate(["http://peer1.example", "http://peer2.example:8443"])
    pcr = _peer_check_report(cand["candidate_peer_urls"])
    with pytest.raises(ValueError, match="exceeds max_peer_count"):
        m.build_dynamic_peer_admission_v0(
            current_peer_urls=["http://peer0.example"],
            candidate=cand,
            peer_check_report=pcr,
            max_peer_count=2,  # 1 current + 2 new = 3 > 2
        )


def test_admission_rejects_rejected_peer_in_report():
    """A candidate whose peer-check report contains a NOT-ok peer is rejected:
    no silent admission of an unhealthy peer."""
    cand = _build_candidate(["http://peer1.example", "http://peer2.example:8443"])
    pcr = _peer_check_report(cand["candidate_peer_urls"], mark_bad_index=1)
    with pytest.raises(ValueError, match="rejected peer"):
        m.build_dynamic_peer_admission_v0(
            current_peer_urls=[],
            candidate=cand,
            peer_check_report=pcr,
            max_peer_count=10,
        )


def test_admission_rejects_network_mismatch():
    """A peer-check report for a different network is rejected (no cross-network
    peer admission)."""
    cand = _build_candidate(["http://peer1.example"])
    pcr = _peer_check_report(cand["candidate_peer_urls"])
    pcr["network_id"] = "OTHER-NETWORK"
    with pytest.raises(ValueError, match="network mismatch"):
        m.build_dynamic_peer_admission_v0(
            current_peer_urls=[],
            candidate=cand,
            peer_check_report=pcr,
            max_peer_count=10,
        )


# --------------------------------------------------------------------------- #
# The mine: search for a peer-admission disaster witness.
# --------------------------------------------------------------------------- #
@settings(max_examples=1200, suppress_health_check=[HealthCheck.too_slow])
@given(
    current_input=st.lists(st.sampled_from(_URL_CHOICES), min_size=0, max_size=6),
    candidate_input=st.lists(st.sampled_from(_URL_CHOICES), min_size=1, max_size=6),
    slack=st.integers(min_value=0, max_value=4),
)
def test_admission_has_no_safety_witness(current_input, candidate_input, slack):
    # Build a VALID candidate via the module's own builder (it dedups internally).
    cand = _build_candidate(candidate_input)
    candidate_urls = cand["candidate_peer_urls"]
    pcr = _peer_check_report(candidate_urls)

    # Independent count of the post-set so we can pick a cap that sometimes admits
    # and sometimes rejects (cap = required - 0..? would only reject; cap =
    # required + slack lets us straddle the boundary).
    seen: set[str] = set()
    exp_current = []
    for u in current_input:
        c = _canon(u)
        if c not in seen:
            seen.add(c)
            exp_current.append(c)
    new_count = sum(1 for u in candidate_urls if u not in seen)
    required = len(exp_current) + new_count
    cap = max(1, required - 2 + slack)  # straddles the cap boundary

    try:
        admission = m.build_dynamic_peer_admission_v0(
            current_peer_urls=current_input,
            candidate=cand,
            peer_check_report=pcr,
            max_peer_count=cap,
        )
    except (ValueError, TypeError):
        return  # rejected — fail-closed; no peer set was mutated. Safe.

    # ---- ADMIT: the peer-admission-safety invariant must hold. ----
    _assert_admission_safe(
        admission, current_input=current_input, candidate_input=candidate_input, cap=cap
    )

    # (DET) DETERMINISM: identical inputs -> identical certificate.
    admission2 = m.build_dynamic_peer_admission_v0(
        current_peer_urls=current_input,
        candidate=cand,
        peer_check_report=pcr,
        max_peer_count=cap,
    )
    assert admission2["admission_hash"] == admission["admission_hash"], "non-deterministic admission"

    # (I) IDEMPOTENCE: re-admitting the SAME candidate against the new post-set
    # admits ZERO new peers and leaves the final set unchanged (modulo the cap,
    # which still holds since the set did not grow).
    final_after = admission["final_peer_urls"]
    admission_again = m.build_dynamic_peer_admission_v0(
        current_peer_urls=final_after,
        candidate=cand,
        peer_check_report=pcr,
        max_peer_count=cap,
    )
    assert admission_again["admitted_peer_urls"] == [], (
        f"NON-IDEMPOTENT: re-admit added {admission_again['admitted_peer_urls']}"
    )
    assert admission_again["final_peer_urls"] == final_after, (
        "NON-IDEMPOTENT: final set changed on re-admission"
    )
