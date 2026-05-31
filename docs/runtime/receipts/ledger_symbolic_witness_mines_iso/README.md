# ZenoLedger symbolic disaster-witness mines — bounded negative receipts (2026-05-31)

Property-based (`hypothesis`) disaster-witness search over three **unowned**
(Codex's ledger footprint is only `zeno_ledger_signature.py`) consensus-finality
modules that previously had only **example-based** tests. Each mine encodes a
disaster class as a falsifiable safety invariant, searches thousands of generated
inputs, and is paired with a **teeth / non-vacuity** test proving the invariant
actually catches a planted violation (a passing property test with no teeth is a
false receipt — CLAUDE.md non-vacuity discipline).

> Discipline: this is a **bounded** search, not a proof. A clean run is a negative
> receipt over the generated domain (small validator sets / registries / tx lists),
> not a universal guarantee. No code was changed — these surfaces held.

## Mines

| # | Module (unowned) | Disaster class mined | Invariant | Examples | Result |
|---|---|---|---|---|---|
| A | `zeno_ledger_signer_registry.verify_signature_quorum_v0` | **Quorum forgery** — a finality certificate admitted with under-threshold / mis-counted stake | admit ⟹ counted signers are *distinct, active* registry signers ∧ `accepted_weight == Σ registry weights` ∧ `accepted_weight ≥ threshold` ∧ determinism | 2000 | **No witness** |
| B | `zeno_ledger_validator_schedule_v0.build_proposer_duty_v0` | **Bad proposer schedule** — out-of-set/revoked proposer, non-determinism, or proportional unfairness (censorship/over-weight) | over one full cycle: proposer always active-in-set ∧ deterministic duty_hash ∧ each active validator selected *exactly* `voting_power` times | 1500 | **No witness** |
| C | `zeno_ledger_conflict_graph_v0` (`transactions_conflict_v0` / `build_conflict_graph_v0`) | **Under-conflict** — two txs sharing state scheduled into different components → unsafe parallel execution (double-spend / nondeterminism) | global-cell tx conflicts with ALL ∧ relation symmetric ∧ graph edge ⇔ pairwise relation ∧ different-component txs do not conflict | 1500 | **No witness** |

The BLS signature check (`validate_bls_signed_artifact_envelope_v0`, the crypto
layer, owned elsewhere) is treated as a **valid-signature oracle** (stubbed to
accept) in mine A, so the search exercises only the **counting / dedup / threshold
/ active-filter** logic. Signature/aggregate forgery is explicitly out of scope and
asserted nowhere.

## Teeth (non-vacuity)

- A: `test_invariant_catches_forged_certificate` — a forged report (weight below
  threshold; a phantom unregistered signer) trips the checker.
- C: `test_conflict_graph_mine_is_non_vacuous` — proves the global-wildcard branch
  and the cross-component-separation branch both actually fire on hand-built input.
- B: boundary test `test_proposer_schedule_rejects_height_before_start`.

## Refuted at read time (no mine needed)

`_shared_conflict_cells_v0`'s docstring claims "any tx mapped to the global cell
conflicts with every other tx." The plain-intersection line alone would *not*
honor that for a one-sided global cell — but lines 68-69
(`if GLOBAL_DEX_CELL_V0 in left_cells or … in right_cells: return [GLOBAL…]`)
implement the wildcard correctly. Hypothesized under-conflict **refuted**; mine C
now guards it.

## Reproduce

```bash
# from the claude/runtime-disaster-hardening-iso worktree
PYTHONPATH="$PWD" python3 -m pytest \
  tests/runtime/test_signer_quorum_counting_witness_mine.py \
  tests/runtime/test_ledger_schedule_conflict_witness_mine.py -q
# 6 passed (3 mines @ ~5000 total generated cases + 3 teeth/boundary tests)
```

## Scope / non-claims

Bounded, single-module property search. Does **not** assert the composed node
acceptance path, the BLS crypto, or any multi-module sequencing. It fills the
symbolic-witness gap these example-tested modules left, and the mines are now
standing regression guards against the named disaster classes.
