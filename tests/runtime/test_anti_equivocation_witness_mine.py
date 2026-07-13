"""Disaster-witness mine for ZenoLedger anti-equivocation evidence soundness.

TARGET: src/integration/zeno_ledger_anti_equivocation_v0.py

This surface decides whether a (sequencer / watcher-profile) operator has
*equivocated* — produced two conflicting commitments for the SAME consensus
position — and, if so, mints a hash-bound `slashable` evidence packet. Slashing
is irreversible value destruction, so the evidence relation must be sound in
BOTH directions:

DISASTER CLASSES MINED
======================
1. FALSE EQUIVOCATION (build soundness). A `build_*_equivocation_slashing_evidence_v0`
   call returns a `slashable` packet for a pair that does NOT genuinely conflict:
     - same payload (identical commitment / header_hash), or
     - a different consensus position (checkpoint: different (chain_id,height);
       watcher: non-overlapping range AND tip).
   If evidence can be minted here, an honest operator is slashable -> safety hole.

2. MISSED EQUIVOCATION (detector completeness). A genuinely conflicting pair —
   checkpoint: same (chain_id, height), different header_hash; watcher: same
   (profile_id, chain_id) and same range OR same tip-height, different
   last_header_hash — is NOT rejected by the corresponding
   `validate_*_non_equivocation_v0`. A missed conflict lets a double-commit
   finalize undetected -> safety hole.

3. DETECTOR SOUNDNESS (no false positive). A set with no genuine conflict
   (every shared consensus position carries an identical commitment) MUST be
   accepted. A spurious rejection would slash / halt an honest set.

The invariants are encoded as `_assert_no_false_equivocation_*` /
`_assert_detector_*` helpers reused by the deterministic teeth tests, so a
passing property run is a non-vacuous bounded NEGATIVE receipt.

SCOPE / NON-CLAIMS
==================
- `hash_v0` is SHA-256 over canonical JSON; this module performs NO BLS /
  signature verification, so NO crypto oracle is stubbed (crypto_oracle_stubbed
  = false). Signature/aggregate forgery is out of scope.
- `validate_slashing_evidence_v0` is a SHAPE + HASH-BINDING validator by
  contract; it deliberately does NOT cross-check that the embedded `artifacts`
  semantically realize the claimed conflict (same position, distinct payload).
  We therefore do NOT assert that semantic cross-check on `validate_*` — we
  assert it on the BUILD path, which is the only path that inspects the raw
  commitments. That narrow contract is a documented limitation, not a finding.
- Multi-module sequencing, registry/quorum composition, and adversarial
  canonical-JSON collisions are out of scope.
- Domains are kept small/bounded (<=6 items, heights/ranges <=8) so the build
  preconditions (matching chain_id, distinct header hashes, canonical 32-byte
  hex, sorted hashes) are satisfiable and the mine exercises the ADMIT path
  rather than only the reject path.
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_anti_equivocation_v0 as m  # noqa: E402
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    build_checkpoint_v0,
    build_header_v0,
    hash_v0,
)
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0  # noqa: E402

ZERO_ROOT = "0x" + "00" * 32
SLASHABLE_SCHEMA = m.SLASHING_EVIDENCE_SCHEMA_V0


def _root(label: str) -> str:
    """A canonical lowercase 0x-prefixed 32-byte root, distinct per label."""
    return hash_v0("anti_equivocation_mine_root", {"label": label})


# --------------------------------------------------------------------------- #
# Valid-object builders (use the module's own build_* so we hit the ADMIT path)
# --------------------------------------------------------------------------- #
def _header(*, chain_id: str, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=_root(f"ingress-{body_label}"),
        tx_root=_root(f"tx-{body_label}"),
        pre_state_root=_root(f"pre-{body_label}"),
        post_state_root=_root(f"post-{body_label}"),
        app_hash=_root(f"app-{body_label}"),
        evidence_root=_root(f"evidence-{body_label}"),
        body_root=_root(f"body-{body_label}"),
        data_availability_root=_root(f"da-{body_label}"),
        proof_journal_hash=_root(f"proof-{body_label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _checkpoint(*, chain_id: str, height: int, body_label: str) -> dict[str, object]:
    return build_checkpoint_v0(_header(chain_id=chain_id, height=height, body_label=body_label))


def _verify_report(*, from_height: int, to_height: int, tip_label: str) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "range_verified",
        "mode": "replay_bound",
        "authority_scope": "replay_bound_range_v0",
        "range_verified": True,
        "header_linkage_checked": True,
        "state_continuity_checked": True,
        "state_replay_checked": True,
        "receipt_replay_checked": True,
        "config_binding_checked": True,
        "replay_config_digest": _root("replay-config"),
        "checked_heights": list(range(from_height, to_height + 1)),
        "proof_metadata_checked_heights": [],
        "proof_verification_checked_heights": [],
        "last_header_hash": _root(f"tip-{tip_label}"),
        "last_post_state_root": _root(f"post-{tip_label}"),
        "last_app_hash": _root(f"app-{tip_label}"),
        "errors": [],
    }


def _attestation(*, from_height: int, to_height: int, tip_label: str, watcher: str) -> dict[str, object]:
    return build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=from_height, to_height=to_height, tip_label=tip_label),
        watcher_id=watcher,
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )


# --------------------------------------------------------------------------- #
# Invariant helpers (factored out so the teeth tests reuse the SAME predicate)
# --------------------------------------------------------------------------- #
def _genuine_checkpoint_conflict(a: dict, b: dict) -> bool:
    """Ground truth: a,b are an equivocation iff same (chain_id,height) but
    DIFFERENT header_hash. Anything else is a non-conflict."""
    return (
        a["chain_id"] == b["chain_id"]
        and int(a["height"]) == int(b["height"])
        and a["header_hash"] != b["header_hash"]
    )


def _assert_no_false_equivocation_checkpoint(evidence: object, a: dict, b: dict) -> None:
    """FALSE-EQUIVOCATION invariant for the checkpoint build path.

    Raises AssertionError if a `slashable` packet was minted for a non-conflict,
    or if the minted packet is internally inconsistent (status, distinctness,
    sortedness, hash binding)."""
    assert _genuine_checkpoint_conflict(a, b), (
        "FALSE EQUIVOCATION: slashable checkpoint evidence minted for a NON-conflicting "
        f"pair chain_id_a={a['chain_id']!r} h_a={a['height']} chain_id_b={b['chain_id']!r} "
        f"h_b={b['height']} same_header={a['header_hash'] == b['header_hash']}"
    )
    assert evidence["status"] == "slashable"
    assert evidence["schema"] == SLASHABLE_SCHEMA
    hh = evidence["conflicting_header_hashes"]
    assert hh[0] != hh[1], "evidence claims a conflict but the two header hashes are equal"
    assert list(hh) == sorted(hh), "conflicting header hashes not canonical-sorted"
    ah = evidence["artifact_hashes"]
    assert ah[0] != ah[1] and list(ah) == sorted(ah), "artifact hashes not distinct+sorted"
    # hash-binding self-consistency: validator must accept what the builder mints
    m.validate_slashing_evidence_v0(evidence)


def _genuine_watcher_conflict(a: tuple, b: tuple) -> bool:
    """Ground truth for watcher attestations parsed as
    (profile_id, chain_id, from_height, to_height, header_hash). Equivocation
    iff same (profile_id, chain_id) and (same full range OR same tip) but a
    DIFFERENT last_header_hash."""
    pa, ca, fa, ta, hba = a
    pb, cb, fb, tb, hbb = b
    if pa != pb or ca != cb or hba == hbb:
        return False
    same_range = fa == fb and ta == tb
    same_tip = ta == tb
    return same_range or same_tip


def _parse_att(att: dict) -> tuple:
    return (
        att["profile_id"],
        att["chain_id"],
        int(att["from_height"]),
        int(att["to_height"]),
        att["last_header_hash"],
    )


def _assert_no_false_equivocation_watcher(evidence: object, a: dict, b: dict) -> None:
    """FALSE-EQUIVOCATION invariant for the watcher build path."""
    ta, tb = _parse_att(a), _parse_att(b)
    assert _genuine_watcher_conflict(ta, tb), (
        "FALSE EQUIVOCATION: slashable watcher evidence minted for a NON-conflicting "
        f"pair a={ta} b={tb}"
    )
    assert evidence["status"] == "slashable"
    assert evidence["schema"] == SLASHABLE_SCHEMA
    hh = evidence["conflicting_header_hashes"]
    assert hh[0] != hh[1] and list(hh) == sorted(hh)
    m.validate_slashing_evidence_v0(evidence)


def _assert_detector_matches_truth_checkpoint(checkpoints: list[dict]) -> None:
    """MISSED/SOUNDNESS invariant for the checkpoint detector: it rejects iff
    SOME pair genuinely conflicts (same (chain_id,height), different header)."""
    truth_conflict = False
    seen: dict[tuple, str] = {}
    for c in checkpoints:
        key = (str(c["chain_id"]), int(c["height"]))
        h = str(c["header_hash"])
        if key in seen and seen[key] != h:
            truth_conflict = True
        seen.setdefault(key, h)

    rejected = False
    try:
        m.validate_checkpoint_non_equivocation_v0(checkpoints)
    except ValueError:
        rejected = True

    if truth_conflict:
        assert rejected, (
            "MISSED EQUIVOCATION: a same-(chain_id,height) pair with different header "
            "was ACCEPTED by validate_checkpoint_non_equivocation_v0"
        )
    else:
        assert not rejected, (
            "FALSE POSITIVE: validate_checkpoint_non_equivocation_v0 rejected a set with "
            "no genuine (chain_id,height) header conflict"
        )


# --------------------------------------------------------------------------- #
# Strategies (small, bounded; satisfiable build-time constraints)
# --------------------------------------------------------------------------- #
_chain = st.sampled_from(["chain-x", "chain-y"])
_height = st.integers(min_value=0, max_value=4)
# body_label drives header_hash; reusing a label yields an IDENTICAL header_hash.
_label = st.sampled_from(["p", "q", "r"])

# A checkpoint spec; a small list of them lets duplicates + conflicts both arise.
_ckpt_spec = st.tuples(_chain, _height, _label)

# watcher: (from, span>=0 so to>=from, tip_label). Small ranges => overlapping
# tips/ranges are frequently sampled, so the genuine-conflict branch fires.
_att_spec = st.tuples(
    st.integers(min_value=0, max_value=4),  # from_height
    st.integers(min_value=0, max_value=3),  # span (to = from + span)
    st.sampled_from(["t0", "t1", "t2"]),    # tip_label -> last_header_hash
)


# =============================== TEETH TESTS =============================== #
def test_teeth_false_equivocation_checkpoint_planted_nonconflict() -> None:
    """Teeth/non-vacuity: a FORGED 'slashable' checkpoint packet built from a
    duplicate (same header) pair MUST trip the false-equivocation checker.
    Without this, a green property run would be a false receipt."""
    ck = _checkpoint(chain_id="chain-x", height=1, body_label="p")
    # Forge a packet that *claims* slashable but the underlying pair is identical.
    forged = {
        "schema": SLASHABLE_SCHEMA,
        "status": "slashable",
        "conflicting_header_hashes": sorted([_root("hx"), _root("hy")]),
        "artifact_hashes": sorted([_root("ax"), _root("ay")]),
    }
    with pytest.raises(AssertionError, match="FALSE EQUIVOCATION"):
        _assert_no_false_equivocation_checkpoint(forged, ck, dict(ck))


def test_teeth_false_equivocation_watcher_planted_nonconflict() -> None:
    """Teeth: a forged watcher packet for a same-payload pair (identical tip)
    MUST trip the checker."""
    a = _attestation(from_height=1, to_height=5, tip_label="t0", watcher="w-a")
    b = _attestation(from_height=1, to_height=5, tip_label="t0", watcher="w-b")  # SAME tip header
    forged = {
        "schema": SLASHABLE_SCHEMA,
        "status": "slashable",
        "conflicting_header_hashes": sorted([_root("h1"), _root("h2")]),
        "artifact_hashes": sorted([_root("a1"), _root("a2")]),
    }
    with pytest.raises(AssertionError, match="FALSE EQUIVOCATION"):
        _assert_no_false_equivocation_watcher(forged, a, b)


def test_teeth_missed_equivocation_checkpoint_buggy_detector() -> None:
    """Teeth: a buggy detector that only checks ADJACENT pairs would MISS a
    conflict separated by a duplicate. The truth-oracle helper MUST flag that
    miss. We plant the miss by re-implementing the broken detector inline and
    asserting the helper's MISSED-EQUIVOCATION branch catches it via a forged
    'no rejection' simulation."""
    ck_a = _checkpoint(chain_id="chain-x", height=1, body_label="p")
    ck_b = _checkpoint(chain_id="chain-x", height=1, body_label="q")  # genuine conflict
    # Truth says conflict exists; simulate a detector that FAILED to reject by
    # monkey-asserting the helper against a list where the real module DOES reject,
    # but we verify the helper's logic by directly checking the truth branch.
    # Construct a planted "accepted-despite-conflict" via a local broken checker:
    def _broken_validate(_cks):
        return None  # never rejects -> a missed-equivocation detector

    saved = m.validate_checkpoint_non_equivocation_v0
    try:
        m.validate_checkpoint_non_equivocation_v0 = _broken_validate  # type: ignore[assignment]
        with pytest.raises(AssertionError, match="MISSED EQUIVOCATION"):
            _assert_detector_matches_truth_checkpoint([ck_a, ck_b])
    finally:
        m.validate_checkpoint_non_equivocation_v0 = saved  # type: ignore[assignment]


def test_teeth_false_positive_checkpoint_buggy_detector() -> None:
    """Teeth: a detector that ALWAYS rejects would slash an honest set. The
    soundness branch of the truth-oracle helper MUST catch that on a duplicate
    (no-conflict) list."""
    ck = _checkpoint(chain_id="chain-x", height=2, body_label="r")

    def _always_reject(_cks):
        raise ValueError("spurious equivocation")

    saved = m.validate_checkpoint_non_equivocation_v0
    try:
        m.validate_checkpoint_non_equivocation_v0 = _always_reject  # type: ignore[assignment]
        with pytest.raises(AssertionError, match="FALSE POSITIVE"):
            _assert_detector_matches_truth_checkpoint([ck, dict(ck)])
    finally:
        m.validate_checkpoint_non_equivocation_v0 = saved  # type: ignore[assignment]


# ============================ PROPERTY MINES ============================ #
@settings(max_examples=900)
@given(spec_a=_ckpt_spec, spec_b=_ckpt_spec)
def test_checkpoint_build_has_no_false_equivocation_witness(spec_a, spec_b) -> None:
    """FALSE-EQUIVOCATION mine: for every pair the builder ADMITS, the pair must
    genuinely conflict and the minted packet must be self-consistent."""
    ca = _checkpoint(chain_id=spec_a[0], height=spec_a[1], body_label=spec_a[2])
    cb = _checkpoint(chain_id=spec_b[0], height=spec_b[1], body_label=spec_b[2])
    try:
        evidence = m.build_checkpoint_equivocation_slashing_evidence_v0(ca, cb)
    except ValueError:
        return  # rejected -> safe, no evidence minted
    _assert_no_false_equivocation_checkpoint(evidence, ca, cb)
    # determinism / order-independence of the minted certificate
    reversed_evidence = m.build_checkpoint_equivocation_slashing_evidence_v0(cb, ca)
    assert reversed_evidence == evidence, "evidence is not order-independent"


@settings(max_examples=900)
@given(specs=st.lists(_ckpt_spec, min_size=1, max_size=6))
def test_checkpoint_detector_matches_truth_no_witness(specs) -> None:
    """MISSED / FALSE-POSITIVE mine for the checkpoint detector against an
    independent ground-truth oracle."""
    checkpoints = [_checkpoint(chain_id=c, height=h, body_label=lab) for (c, h, lab) in specs]
    _assert_detector_matches_truth_checkpoint(checkpoints)


@settings(max_examples=900)
@given(spec_a=_att_spec, spec_b=_att_spec)
def test_watcher_build_has_no_false_equivocation_witness(spec_a, spec_b) -> None:
    """FALSE-EQUIVOCATION mine for the watcher build path."""
    fa, sa, la = spec_a
    fb, sb, lb = spec_b
    a = _attestation(from_height=fa, to_height=fa + sa, tip_label=la, watcher="w-a")
    b = _attestation(from_height=fb, to_height=fb + sb, tip_label=lb, watcher="w-b")
    try:
        evidence = m.build_watcher_attestation_equivocation_slashing_evidence_v0(a, b)
    except ValueError:
        return  # rejected -> safe
    _assert_no_false_equivocation_watcher(evidence, a, b)
    reversed_evidence = m.build_watcher_attestation_equivocation_slashing_evidence_v0(b, a)
    assert reversed_evidence == evidence, "watcher evidence is not order-independent"


@settings(max_examples=900)
@given(specs=st.lists(_att_spec, min_size=1, max_size=6))
def test_watcher_detector_matches_truth_no_witness(specs) -> None:
    """MISSED / FALSE-POSITIVE mine for the watcher detector against an
    independent ground-truth oracle over both the range-key and tip-key
    conflict relations."""
    attestations = [
        _attestation(from_height=f, to_height=f + s, tip_label=lab, watcher=f"w-{i}")
        for i, (f, s, lab) in enumerate(specs)
    ]
    # Independent truth: scan all pairs for a genuine (range OR tip) conflict.
    parsed = [_parse_att(att) for att in attestations]
    truth_conflict = any(
        _genuine_watcher_conflict(parsed[i], parsed[j])
        for i in range(len(parsed))
        for j in range(i + 1, len(parsed))
    )
    rejected = False
    try:
        m.validate_watcher_attestation_non_equivocation_v0(attestations)
    except ValueError:
        rejected = True

    if truth_conflict:
        assert rejected, (
            "MISSED EQUIVOCATION: watcher attestations with a genuine range/tip "
            f"conflict were ACCEPTED; parsed={parsed}"
        )
    else:
        assert not rejected, (
            "FALSE POSITIVE: validate_watcher_attestation_non_equivocation_v0 rejected "
            f"a set with no genuine range/tip conflict; parsed={parsed}"
        )
