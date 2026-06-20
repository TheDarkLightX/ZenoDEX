"""Tests for the commit-reveal-with-punishment seed source.

Run: ``pytest experiments/neutral_tiebreak_v1/test_seed_source.py``
"""

from __future__ import annotations

import os

import pytest

from seed_source import (
    Reveal,
    commit,
    derive_seed,
    seed_from_pairs,
    verify_reveal,
)


def _three_party():
    parties = {"p-a": (b"va", b"na"), "p-b": (b"vb", b"nb"), "p-c": (b"vc", b"nc")}
    commitments = {pid: commit(v, n) for pid, (v, n) in parties.items()}
    reveals = [Reveal(pid, v, n) for pid, (v, n) in parties.items()]
    return commitments, reveals


# --- Commitment: binding + collision-free framing ------------------------

def test_commit_binding_and_verify():
    c = commit(b"value-A", b"nonce-1")
    assert verify_reveal(c, b"value-A", b"nonce-1")
    assert not verify_reveal(c, b"value-B", b"nonce-1")  # different value
    assert not verify_reveal(c, b"value-A", b"nonce-2")  # different nonce
    assert len(c) == 32


def test_commit_framing_is_collision_free():
    assert commit(b"ab", b"c") != commit(b"a", b"bc")


# --- Seed: deterministic, order-independent ------------------------------

def test_seed_deterministic_replay():
    commitments, reveals = _three_party()
    r1 = derive_seed(commitments=commitments, reveals=reveals)
    r2 = derive_seed(commitments=commitments, reveals=reveals)
    assert r1.seed == r2.seed and len(r1.seed) == 32 and r1.slashed == ()


def test_seed_is_reveal_order_independent():
    commitments, reveals = _three_party()
    a = derive_seed(commitments=commitments, reveals=reveals).seed
    b = derive_seed(commitments=commitments, reveals=list(reversed(reveals))).seed
    assert a == b


# --- Punishment: withholding / invalid reveal is slashed + excluded ------

def test_withholding_is_slashed_and_excluded():
    commitments, reveals = _three_party()
    partial = [r for r in reveals if r.participant_id != "p-c"]  # p-c withholds
    res = derive_seed(commitments=commitments, reveals=partial)
    assert res.slashed == ("p-c",)
    assert "p-c" not in res.included
    # seed is exactly the seed over the remaining verified pairs
    assert res.seed == seed_from_pairs([("p-a", b"va"), ("p-b", b"vb")])


def test_invalid_reveal_is_slashed():
    commitments, reveals = _three_party()
    bad = [Reveal("p-c", b"WRONG", b"nc") if r.participant_id == "p-c" else r for r in reveals]
    res = derive_seed(commitments=commitments, reveals=bad)
    assert "p-c" in res.slashed and "p-c" not in res.included


def test_duplicate_reveals_are_order_independent():
    # A valid reveal plus an adversarial invalid duplicate for the same
    # participant must include the participant (with the bound value) regardless
    # of order — no order-dependent include/slash flip.
    commitments, reveals = _three_party()
    base = derive_seed(commitments=commitments, reveals=reveals)
    others = [r for r in reveals if r.participant_id != "p-c"]
    valid_c = Reveal("p-c", b"vc", b"nc")
    invalid_c = Reveal("p-c", b"WRONG", b"nc")
    res1 = derive_seed(commitments=commitments, reveals=others + [valid_c, invalid_c])
    res2 = derive_seed(commitments=commitments, reveals=others + [invalid_c, valid_c])
    assert res1.seed == res2.seed == base.seed
    assert "p-c" in res1.included and res1.slashed == ()


def test_only_invalid_duplicates_are_slashed():
    commitments, reveals = _three_party()
    others = [r for r in reveals if r.participant_id != "p-c"]
    res = derive_seed(
        commitments=commitments,
        reveals=others + [Reveal("p-c", b"X", b"nc"), Reveal("p-c", b"Y", b"nc")],
    )
    assert "p-c" in res.slashed and "p-c" not in res.included


# --- Entropy: every included contributor influences the seed -------------

def test_every_included_contributor_influences_seed():
    # Flipping any one included reveal changes the seed → a participant who
    # committed before seeing others' reveals cannot predict it (in scope).
    commitments, reveals = _three_party()
    base = derive_seed(commitments=commitments, reveals=reveals).seed
    for i in range(len(reveals)):
        pid, val, nonce = reveals[i].participant_id, reveals[i].value, reveals[i].nonce
        val2 = val + b"X"
        c2 = dict(commitments)
        c2[pid] = commit(val2, nonce)
        rv2 = list(reveals)
        rv2[i] = Reveal(pid, val2, nonce)
        assert derive_seed(commitments=c2, reveals=rv2).seed != base


# --- Fail-closed --------------------------------------------------------

def test_fail_closed_when_no_valid_reveal():
    commitments, _ = _three_party()
    with pytest.raises(ValueError):
        derive_seed(commitments=commitments, reveals=[])  # everyone withholds


def test_rejects_bad_inputs():
    with pytest.raises(TypeError):
        commit("not-bytes", b"n")  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        derive_seed(commitments={}, reveals=[])


# --- Cross-language parity (shared golden vectors) ----------------------

def _read(name: str) -> str:
    with open(os.path.join(os.path.dirname(__file__), name), encoding="utf-8") as fh:
        return fh.read()


def test_commit_matches_golden_vectors():
    n = 0
    for line in _read("commit_parity_vectors.tsv").splitlines():
        line = line.rstrip("\n")
        if not line:
            continue
        vh, nh, ch = line.split("\t")
        assert commit(bytes.fromhex(vh), bytes.fromhex(nh)).hex() == ch
        n += 1
    assert n >= 4


def test_seed_matches_golden_vectors():
    n = 0
    for line in _read("seed_parity_vectors.tsv").splitlines():
        line = line.rstrip("\n")
        if not line:
            continue
        pairs_field, sh = line.split("\t")
        pairs = []
        for tok in pairs_field.split(";"):
            idh, vh = tok.split(":")
            pairs.append((bytes.fromhex(idh).decode("utf-8"), bytes.fromhex(vh)))
        assert seed_from_pairs(pairs).hex() == sh
        n += 1
    assert n >= 3
