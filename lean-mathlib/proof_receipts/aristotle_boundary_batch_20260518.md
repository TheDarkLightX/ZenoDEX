---
title: Aristotle Boundary Batch Receipt 2026-05-18
type: proof_receipt
permalink: autonomous-tau-dex-review/proof-receipts/aristotle-boundary-batch-20260518
---

# Aristotle Boundary Batch Receipt 2026-05-18

Purpose: record three Aristotle proof-search packets that close local proof
obligations for UPBA v2 score ordering, ZenoEnergy advisory ranking, and
ZenoCover reserve arithmetic.

## Projects

| Track | Aristotle project | Promoted Lean file |
| --- | --- | --- |
| UPBA v2 score order | `3b1272f9-9fdc-4597-8f33-9fbed7bbf8fa` | `lean-mathlib/Proofs/UPBAV2ScoreOrder.lean` |
| ZenoEnergy advisory boundary | `5d8fef0b-06e9-4a3d-a230-f074a0d38f7d` | `lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean` |
| ZenoCover reserve arithmetic | `1842c293-4d87-477e-9557-7c6425b2541a` | `lean-mathlib/Proofs/ZenoCoverReserveArithmetic.lean` |

Submitted packets are recorded under:

```text
internal/aristotle/upba_v2_score_order_20260518
internal/aristotle/zenoenergy_advisory_boundary_20260518
internal/aristotle/zenocover_reserve_arithmetic_20260518
```

Returned result archives are recorded under:

```text
internal/aristotle/results/upba_v2_score_order_3b1272f9/result.tar.gz
internal/aristotle/results/zenoenergy_advisory_boundary_5d8fef0b/result.tar.gz
internal/aristotle/results/zenocover_reserve_1842c293/result.tar.gz
```

## Local Replay

Returned packets were unpacked in `/tmp/aristotle-results/unpacked` and checked
with:

```bash
cd /tmp/aristotle-results/unpacked/upba-v2-score/aristotle-upba-v2-score_aristotle
lake build AristotleTask

cd /tmp/aristotle-results/unpacked/zenoenergy-boundary/aristotle-zenoenergy-boundary_aristotle
lake build AristotleTask

cd /tmp/aristotle-results/unpacked/zenocover-reserve/aristotle-zenocover-reserve_aristotle
lake build AristotleTask
```

Result: all three returned packets built successfully.

Trust scan on returned Lean:

```bash
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' \
  /tmp/aristotle-results/unpacked/*/*/AristotleTask.lean
```

Result: no matches.

## Promoted Checks

The accepted proof bodies were adapted into the repository namespace and checked
with:

```bash
cd lean-mathlib
lake env lean Proofs/UPBAV2ScoreOrder.lean
lake env lean Proofs/ZenoEnergyAdvisoryBoundary.lean
lake env lean Proofs/ZenoCoverReserveArithmetic.lean
lake build Proofs.UPBAV2ScoreOrder Proofs.ZenoEnergyAdvisoryBoundary Proofs.ZenoCoverReserveArithmetic
lake env lean Proofs.lean
```

The three promoted modules are also covered by:

```bash
pytest -q tests/formal/test_lean_aristotle_boundary_packets.py
```

Result: all focused Lean checks, the module-target Lake build, the aggregate
`Proofs.lean` import check, and the pytest wrapper passed.

Proof-quality scan:

```bash
python3 /home/trevormoc/.codex/skills/proof-quality-curation/scripts/lean_proof_quality_scan.py \
  lean-mathlib/Proofs/UPBAV2ScoreOrder.lean \
  lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean \
  lean-mathlib/Proofs/ZenoCoverReserveArithmetic.lean
```

Result: ZenoEnergy advisory boundary and ZenoCover reserve arithmetic scored
`S`; UPBA v2 score order scored `A` because the finite Nat order proof uses
solver tactics and one broad structural equality simplification.

## Proof Meaning

UPBA v2 score order:

```text
StrictBetter(candidate, incumbent) ∧ WeakNoWorse(incumbent, other)
  -> WeakNoWorse(candidate, other)
```

This is the streaming update invariant for canonical fill-vector scoring. It is
only a score-order theorem.

ZenoEnergy advisory boundary:

```text
WithinEps(winner_energy, winner_true_cost, eps)
∧ WithinEps(other_energy, other_true_cost, eps)
∧ winner_energy + 2*eps <= other_energy
  -> winner_true_cost <= other_true_cost
```

The checked-stop theorem then lifts a checked prefix plus energy-separated
suffix to a full finite candidate list, and to a global feasible set only with
an explicit coverage premise.

ZenoCover reserve arithmetic:

```text
minReserve <= reserveAvailable
  -> totalPaid(reserveAvailable, minReserve, claims)
     <= reserveAvailable - minReserve
```

Sequential verified claims cannot spend below the declared reserve floor in the
natural-number arithmetic model.

## Boundaries

- UPBA v2 score ordering does not prove candidate generation, price-grid
  sufficiency, omitted-candidate rejection, or global optimality.
- ZenoEnergy remains advisory. Energy ranking may reorder or shortlist
  candidates only when a verifier-facing certificate or exact fallback covers
  the unchecked candidates.
- ZenoCover reserve arithmetic does not model insurance law, claim truth,
  oracle honesty, custody, reserve operation, or any promise to pay.
- The Aristotle warning about preferred Lean `v4.28.0` was observed at
  submission time. Repository replay used the repo-pinned Lean `v4.27.0`.

Integration decision: accept the returned proof bodies after local replay,
statement-surface review, and trust scan. The promoted modules are deliberately
small so future production claims can import only the proof boundary they need.
