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

## Generation-creativity tier (rung 2–3 — beyond uniform-random PBT)

The mines above are honest but **rung-1**: uniform random single-draws, which
confirm the easy center of the input space and rarely reach multi-transition
sequences, structural boundaries, or the threshold knife-edge. Three follow-up
mines climb the generation ladder against the **same real code** (no
re-implementation), each independently verified to be *genuinely* more creative
(the verifier cited the actual `itertools.product` / `RuleBasedStateMachine` /
`target()` code, not relabeled randomness):

| Technique | Surface | What it reaches that rung-1 cannot | Coverage | Result |
|---|---|---|---|---|
| **Exhaustive bounded enumeration** (`itertools.product`, *complete* not sampled) + adversarial structural seeds | `state_root` / `canonical` / `support_root` | LEB128 carry edges (127/128, 2³²±1) **deterministically**; a *certificate* over a whole ≤3-entry lattice; field-boundary-shift / split-aliasing / BAL-vs-LPB shapes uniform sampling never builds | **33,045,246 state pairs** checked complete-over-bound | no collision |
| **Stateful multi-transition machines** (`RuleBasedStateMachine`, registry threaded forward) | `bonded_slashing`, `dynamic_peers` | **multi-slash accumulation** (10+ distinct-hash evidence packets on one subject), evidence **replay**, cumulative-slash-over-a-run, multi-round peer accumulation — structurally unreachable single-shot | 2 machines × 250 runs × 20 steps | no double-slash |
| **Target-guided boundary pushing** (`hypothesis.target()` + distribution shaping) | quorum / slash-split / schedule | the exact knife-edge — `target()` reached **fitness 0 = `accepted_weight == threshold` exactly**, and `slash == available` — instead of the uniform center | 3000+ examples concentrated at boundaries | no witness |

Cross-run invariants (e.g. `cumulative_slashed <= bonded` across the whole
sequence, `entry_slashed == externally_tracked_cumulative` for ledger-drift) are
the genuinely new safety statements. The exhaustive mine passed an internal
Codex review (B−→A after honest per-sweep bound docstrings + exact `C(N,2)`
assertions + teeth rewired through the real helper).

**Honest limits:** "exhaustive" = complete only over the *deliberately tiny*
declared bounds (2-pubkey/2-asset sub-alphabets, ≤3 entries, single-nonce), not a
maximal-domain proof; the pool section is seed-covered, not enumerated. Stateful
and target-guided remain bounded sampling, just steered far better. SHA-256
preimage resistance is assumed throughout.

## Refuted at read time

`conflict_graph._shared_conflict_cells_v0`'s docstring claims a global-cell tx
conflicts with everything; plain intersection alone would not honor that one-sided
— but the `if GLOBAL_DEX_CELL_V0 in left or … in right: return [GLOBAL]` branch
does. Hypothesized under-conflict **refuted**; the conflict mine now guards it.

## Reproduce

```bash
# from the claude/runtime-disaster-hardening-iso worktree
# rung-1 (uniform-random) mines:
PYTHONPATH="$PWD" python3 -m pytest tests/runtime/test_*_witness_mine.py -q
# 45 passed  (10 mines + teeth/boundary tests; ~20,500 generated cases)
# rung 2-3 (exhaustive / stateful / target-guided):
PYTHONPATH="$PWD" python3 -m pytest \
  tests/runtime/test_state_collision_exhaustive_mine.py \
  tests/runtime/test_ledger_stateful_sequence_mine.py \
  tests/runtime/test_boundary_target_guided_mine.py -q
# 27 passed  (33M exhaustive pairs + stateful sequences + boundary-steered)
```

## Scope / non-claims

Bounded, single-module property search. Does **not** assert the composed node
acceptance path, the BLS crypto, multi-transition / cross-block sequencing, or the
model↔runtime refinement gap. It fills the symbolic-witness gap these example-only
modules left, and the mines now stand as regression guards against the named
disaster classes.
