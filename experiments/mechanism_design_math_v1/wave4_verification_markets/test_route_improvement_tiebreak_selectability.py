# [TESTER] v1
"""
Wave-4 verification-markets tie-break selectability (charter
docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md section 10, O-VM-03 / H-MD-VM-003).
Integer/string witnesses through the REAL improvement-bounty round selection
(tools/gpu_jobs/improvement_bounty_round_route_v1.py: _route_tiebreak_key and
_select_winner).

O-VM-03: improvement ties are resolved by `_route_tiebreak_key`
= (hop_count, pool_ids, intermediate_asset, miner_id), whose final component is
the SUBMITTER-CHOSEN miner_id (a free-form string, not a witness hash or a
bonded value). _select_winner takes the max improvement, breaking ties by the
smallest tiebreak_key. So among equally-good proposals on the SAME route, the
winner is whoever picked the lexicographically smallest miner_id — a tie win is
costlessly SELECTABLE by choosing a small miner_id. The selection is over
already-VERIFIED submissions (ok=True); the witness-verifier gate is orthogonal
and assumed passed, which is exactly the realistic two-valid-proposals tie.

Verdict polarity (charter): hypotheses are phrased "deviation exists", so a
PASSING test == SUPPORTED — the costless tie selectability is demonstrated.
Research evidence only; no selection-rule change, no remedy claim (binding the
tie-break to a bonded/committed value instead of a free miner_id is an UNTESTED
design question, not asserted here).
"""

from __future__ import annotations

from tools.gpu_jobs.improvement_bounty_round_route_v1 import (
    Submission,
    _route_tiebreak_key,
    _select_winner,
)

# A fixed 2-hop route shared by all competing proposals (same hops, pools,
# intermediate asset) so the tie-break key differs ONLY in miner_id.
_ROUTE = [
    {"pool_id": "0x" + "aa" * 32, "asset_out": "0x" + "02" * 32},
    {"pool_id": "0x" + "bb" * 32, "asset_out": "0x" + "03" * 32},
]


def _sub(miner_id: str, improvement: int) -> Submission:
    """A verified submission on the shared route with the REAL tie-break key."""
    return Submission(
        miner_id=miner_id,
        witness_path="",
        witness_sha256="",
        ok=True,
        error="",
        job_digest="job",
        improvement_u64=improvement,
        tiebreak_key=_route_tiebreak_key(_ROUTE, miner_id=miner_id),
    )


def test_h_md_vm_003_improvement_tie_resolved_by_submitter_chosen_miner_id() -> None:
    """On an improvement tie over the SAME route, the REAL _select_winner picks the
    submission whose only differing tie-break component — the submitter-chosen
    miner_id — is smallest. The winner is independent of submission order, so it is
    purely a function of the chosen miner_id."""
    a, b = _sub("aa", 1000), _sub("bb", 1000)
    # The keys differ only in the final (miner_id) slot.
    assert a.tiebreak_key[:3] == b.tiebreak_key[:3]
    assert a.tiebreak_key[3] == "aa" and b.tiebreak_key[3] == "bb"

    # Smaller miner_id wins, regardless of order.
    assert _select_winner([a, b]) == 0          # 'aa' wins
    assert _select_winner([b, a]) == 1          # still 'aa' (index of a)
    assert {_select_winner([a, b])} == {0}


def test_h_md_vm_003_attacker_steals_tie_by_choosing_minimal_miner_id() -> None:
    """Costless selectability: an attacker who ties the honest miner's improvement
    on the same route can GUARANTEE the win by choosing a miner_id smaller than any
    rival's. The win flips on the miner_id choice alone — no extra work, bond, or
    better proposal required."""
    honest = _sub("honest_miner", 1000)
    # Attacker copies route + improvement, picks a smaller miner_id.
    attacker = _sub("0", 1000)                   # "0" < "honest_miner" lexicographically
    assert attacker.improvement_u64 == honest.improvement_u64
    assert attacker.tiebreak_key[:3] == honest.tiebreak_key[:3]

    subs = [honest, attacker]
    win = _select_winner(subs)
    assert subs[win].miner_id == "0"             # attacker wins the tie costlessly

    # Had the attacker not minimized, the honest miner would have won.
    honest2, loser = _sub("aaa", 1000), _sub("zzz", 1000)
    assert _select_winner([honest2, loser]) == 0  # 'aaa' < 'zzz' -> honest wins


def test_h_md_vm_003_strict_improvement_beats_any_miner_id() -> None:
    """Boundary / non-vacuity: the miner_id lever applies ONLY to genuine
    improvement ties. A strictly larger improvement_u64 wins regardless of how
    small the rival's miner_id is — so the selectability cannot override a better
    proposal, it only decides ties."""
    # Rival picks the smallest possible miner_id but a worse improvement.
    small_id_worse = _sub("", 1000)              # empty string: minimal miner_id
    better = _sub("zzzzzzzz", 1001)              # larger miner_id, strictly better
    win = _select_winner([small_id_worse, better])
    assert _select_winner([small_id_worse, better]) == 1
    assert better.improvement_u64 > small_id_worse.improvement_u64
    assert _select_winner([better, small_id_worse]) == 0   # order-independent
