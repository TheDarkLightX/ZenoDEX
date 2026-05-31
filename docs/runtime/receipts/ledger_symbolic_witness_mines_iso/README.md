# ZenoLedger + state symbolic disaster-witness mines — bounded negative receipts (2026-05-31)

Property-based (`hypothesis`) disaster-witness search over **ten unowned**
consensus-critical surfaces (Codex's ledger/state footprint is only
`zeno_ledger_signature.py`) that previously had **example-based tests only** (or,
for `dynamic_peers`, none). Each mine encodes a disaster class as a falsifiable
safety invariant, searches hundreds–thousands of generated *valid* inputs, and is
paired with a **teeth / non-vacuity** test that plants a real violation and proves
the invariant-checker catches it (a passing property test with no teeth is a false
receipt — CLAUDE.md non-vacuity discipline).

> Discipline: **bounded** search, not proof. A clean run is a negative receipt over
> the generated domain (small registries / validator sets / states / tx lists), not
> a universal guarantee. **No source was changed** — every surface held. Each mine
> was independently re-verified by a separate adversarial agent (re-run + assertion
> mutation to confirm teeth + non-vacuity-of-admits check + `git status src/`), and
> the full suite was then re-run centrally: **45 tests pass, ~20,500 generated cases.**

## Mines

### A. Ledger finality / safety family

| Module (unowned) | Disaster class | Examples | Result |
|---|---|---|---|
| `signer_registry.verify_signature_quorum_v0` | **quorum forgery** — finality cert admitted with under-threshold / mis-counted stake | 2000 | no witness |
| `validator_schedule.build_proposer_duty_v0` | out-of-set/revoked proposer, non-determinism, proportional unfairness | 1500 | no witness |
| `conflict_graph_v0` | **under-conflict** — conflicting txs split into different parallel-exec components | 1500 | no witness |
| `bonded_slashing_v0.apply_bonded_slashing_v0` | **over/under/phantom/collateral slash**, split-leak, policy-cap breach, reject-not-no-op | 900 | no witness |
| `anti_equivocation_v0` (checkpoint + watcher) | **false equivocation** (slash a non-conflicting pair) ∧ **missed equivocation** (real conflict undetected), both directions | 3600 | no witness |
| `live_quorum_v0` | **live-admission forgery** — checkpoint admitted without the wrapped signer-quorum actually clearing; payload-binding / no foreign-payload reuse | 900 | no witness |
| `dynamic_peers_v0.build_dynamic_peer_admission_v0` | **peer-admission** — unbounded set, out-of-allowlist admit, silent drop of current peer, duplicate in final, count-field drift (had *zero* prior tests) | 1200 | no witness |

### B. State canonicalization (state-root-split class — a collision here is CRITICAL)

| Module (unowned) | Disaster class | Examples | Result |
|---|---|---|---|
| `src/state/canonical.py` | canonical-encoder **collision / non-determinism / non-idempotence** (JSON, fixed-hex, uvarint, bytes, domain-sep) | 5000 | no witness |
| `src/state/state_root.py` | **state-root collision** — order-dependence ∨ framing-injectivity break (a moved byte / a balance-row vs LP-row preserving the root) | 2100 | no witness |
| `src/state/support_root.py` | support-root collision / order-dependence / case-fold ambiguity / single-scalar injectivity break | 1800 | no witness |

The BLS signature checks (`validate_bls_signed_artifact_envelope_v0`, the crypto
layer owned elsewhere) are treated as **valid-signature oracles** in the quorum and
`live_quorum` mines, so those searches exercise only the counting / threshold /
admission-composition logic. `bonded_slashing` and `anti_equivocation` perform no
signature verification (they bind by canonical re-hash), so no oracle was needed.
Signature / aggregate forgery is explicitly out of scope and asserted nowhere.

## Teeth (non-vacuity) — every mine has a planted-violation test

Examples of the strongest: `state_root` plants a real framing collision (a balance
row vs a byte-identical LP-share row), proves the production framed encoder keeps
them distinct while an unframed reference collides, and confirms the injectivity
checker raises on the collision — showing the section-label + length-prefix is
load-bearing. `bonded_slashing` plants six distinct violations (over-slash,
split-leak, phantom, policy-cap breach, collateral mutation, under-slash) against
the same helper the property test uses. `anti_equivocation` plants both a
non-conflicting pair (false-equivocation) and a buggy detector (missed/false
positive). Verifiers additionally mutated a live assertion in each mine and
confirmed the mine then **fails**, then reverted.

## Refuted at read time

`conflict_graph._shared_conflict_cells_v0`'s docstring claims a global-cell tx
conflicts with everything; plain intersection alone would not honor that one-sided
— but the `if GLOBAL_DEX_CELL_V0 in left or … in right: return [GLOBAL]` branch
does. Hypothesized under-conflict **refuted**; the conflict mine now guards it.

## Reproduce

```bash
# from the claude/runtime-disaster-hardening-iso worktree
PYTHONPATH="$PWD" python3 -m pytest tests/runtime/test_*_witness_mine.py -q
# 45 passed  (10 mines + teeth/boundary tests; ~20,500 generated cases)
```

## Scope / non-claims

Bounded, single-module property search. Does **not** assert the composed node
acceptance path, the BLS crypto, multi-transition / cross-block sequencing, or the
model↔runtime refinement gap. It fills the symbolic-witness gap these example-only
modules left, and the mines now stand as regression guards against the named
disaster classes.
