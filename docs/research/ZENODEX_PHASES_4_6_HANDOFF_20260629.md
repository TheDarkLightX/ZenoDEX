# ZenoDEX Phases 4-6 Research Handoff

Date: 2026-06-29

This handoff captures the recovered Devin work after the GLM 5.2 credit cutoff.
The goal is to preserve a commit-ready research packet that GPT 5.5 can extend
without relying on Devin session replay.

## Current Branch

Branch: `cpss-bc-research-codex-grade-a`

The previous child-frontier work is already committed on this branch. This
handoff covers the uncommitted Phases 4-6 research packet around CPMM split
concavity, discrete argmax proximity, K-pool generalization, adversarial gain
bounds, and fixed-order min-out-cap evidence.

## Recovered Work

### Phase 3D/4 Foundation

- `WindowBound.lean` proves floor proximity for Lipschitz functions and the
  value-side integer optimum bound.
- `CpmmSplitConcavity.lean` proves continuous CPMM split negative second
  forward difference under valid-domain hypotheses.
- `TernarySearchExactness.lean` proves discrete concavity implies unimodality
  and global maximum.
- `TernarySearchAlgorithm.lean` proves one-step ternary-search narrowing and
  shrinkage under discrete concavity.

### Phase 4

- `KPoolSplitConcavity.lean` proves 3-pool coordinate-wise continuous concavity,
  a K-pool coordinate-slice concavity kernel for fixed non-moving pools, a
  List-sum fixed-pool bridge after active/remainder selection, an explicit
  selected-list bridge for `left ++ active :: between ++ remainder :: right`
  decomposition witnesses, an order-tagged selected-list bridge covering both
  active-before-remainder and remainder-before-active witnesses, an
  active-before-remainder arbitrary-index List decomposition bridge, a
  remainder-before-active arbitrary-index order-tagged List decomposition
  bridge, concrete active/remainder index witnesses inside those supplied
  decompositions, a
  bounded erase-active-then-remainder removal bridge that recovers exactly the
  fixed non-moving pools from those supplied decompositions, active-before and
  remainder-before arbitrary-index removal bridges over undecomposed full
  Lists, a fixed-pool permutation quotient bridge for the fixed non-moving
  pool compression, a proof-carrying unordered selection certificate bridge
  for supplied full-presentation/decomposition/canonical-fixed witnesses,
  full-List ordered-index constructors for that certificate in both
  selected-pair orders, identity-stable full-List presentation bridges for
  duplicate-valued pool selection by distinct ids, an id-ordered full-List
  presentation bridge for supplied stable-id ordered presentations, a stable-id
  sorted-output certificate bridge tying arbitrary identified input Lists to
  supplied id-ordered permutation representatives, an executable stable-id List
  merge-sort bridge for arbitrary identified Lists with unique stable ids, a
  stable-id List permutation quotient bridge proving valid permuted List
  presentations canonicalize to the same sorted output, a Finset Nat quotient
  bridge connecting unordered Finset presentations (keyed by stable ids) to the
  merge-sort concavity path, a Multiset quotient bridge for unordered
  identified-pool collections under a no-duplicate-stable-id contract, a
  Multiset stable-id selection bridge deriving selected-pair index order from
  sorted-output stable-id order, a stable-id lookup witness bridge proving
  selected stable IDs bind to unique sorted-output positions before lowering
  into the Multiset stable-id concavity path, a deterministic runtime stable-id
  lookup certificate checker for canonical bytes and selected-ID/index
  validation, a deterministic runtime-to-Lean assumption bridge that emits and
  re-validates a certificate-relative sorted-ID/lookup/order/hash packet, a
  generated Lean witness module that binds those packet constants to
  proof-facing lookup witness obligations and typechecks against the existing
  lookup index-order theorem, a generated Lean domain witness module that binds
  per-pool digests to Lean-relevant concrete pool fields and typechecks an
  executable stable-id List certificate theorem wrapper, a runtime unordered
  domain canonicalizer that accepts valid pool-order permutations and emits the
  same sorted proof-facing certificate and generated Lean witness source, and
  one concrete 4-pool plus one concrete 5-pool coordinate-wise checkpoint.
- `DiscreteArgmaxProximity.lean` replaces the false discrete-concavity target
  with abstract argmax-proximity theorems, including the certified-anchor
  distance radius `|argmax_g-b*| <= sqrt(2*tau/m)` and the oracle-tight
  perturbation radius `sqrt(2*(f_cont(b*)-f_disc(argmax_g))/m)`, plus CPMM
  conditional instantiations for the clean model. It also proves
  `abstract_one_sided_perturbed_argmax_distance_sharp_quadratic`, a quadratic
  witness showing the generic one-sided `sqrt(2*(alpha+epsilon)/m)` radius is
  attained under the abstract hypotheses.
- `TIGHT_ARGMAX_CEILING_FEE_BOUND_20260630.md` records the derivation ladder:
  oracle-tight radius, best certified-anchor radius, and the production
  gross-spot ceiling-fee envelope.
- `discrete_argmax_proximity_test.py` now includes a research-scope tight
  argmax certificate checker. It validates canonical certificate bytes,
  duplicate-key absence, no-authority flags, domain hash, anchor/argmax
  membership, production dominance, one-sided perturbation, source-typed `m`,
  recomputed tau, and radius hierarchy before accepting the packet. Endpoint
  `m` packets must recompute the endpoint lower bound. Interval-backed `m`
  packets must reference a SHA-256 identified rational interval curvature
  certificate that is resolved, domain-checked, and accepted before the tighter
  argmax radius is accepted. The checker now rejects reserves, fee bps, or
  total input outside its 128-bit research float lane before recomputing `m`,
  `tau`, or radius metrics, returning `BAD_DOMAIN` rather than surfacing Python
  float overflow.
- `CpmmSplitConcavity.lean` now proves the endpoint curvature lower bound is
  positive and proves `splitFunctionCont_strong_concavity_from_m_certificate`:
  a supplied `m > 0` bounded by the endpoint curvature certificate is a valid
  strong-concavity certificate once the second-derivative identity is supplied.
  It also proves `splitFunctionCont_strong_concavity_from_curvature_floor`, a
  consumer theorem for any externally checked local curvature floor, and
  `strong_concavity_interval_lower_bound`, the local interval floor theorem
  `T0(a)+T1(a) >= T0(hi)+T1(lo)` for `lo <= a <= hi`.
  It also proves `strong_concavity_interval_floor_refinement`, the split
  monotonicity theorem showing that child interval floors cannot be lower than
  the parent interval floor.
  `concavity_conservation_law_test.py` validates the matching research-scope
  pool-parameter `m` certificate format with canonical bytes, duplicate-key
  rejection, domain hash binding, no-authority flags, recomputed endpoint
  bound, and bad-`m` rejection. It also validates a separate exact-curvature
  research certificate schema with recomputed minimizer, exact floor, and
  mutation rejection. The exact-curvature float lane now rejects domains above
  its 128-bit research bound before conversion, so oversized pool-valid
  integers return a structured boundary reject instead of overflow. It also
  validates a rational interval certificate schema with exact `{num,den}`
  fields, ordered interval-cover validation, recomputed interval floors, strict
  interval schema keys, and mutation rejection. The best-cover
  interval builder uses the same verifier, chooses among a deterministic
  portfolio that includes uniform placement, and cannot generate a certificate
  worse than uniform placement for the same interval count. The greedy
  refinement builder repeatedly splits the weakest exact interval floor and is
  backed by the Lean split-monotonicity theorem. The bounded optimal midpoint
  audit builder searches all midpoint split schedules under a 16-interval cap,
  emits the same interval certificate schema, and checks the greedy builder
  against that bounded exact-DP optimum.
  `EXACT_CURVATURE_M_CERTIFICATE_20260630.md` records the resulting sharper
  `m` denominators for the tight argmax-radius chain; the discrete argmax
  research checker now consumes those interval `m` certificates through an
  explicit composition path.
- `KPoolDiscreteArgmaxProximity.lean` lifts the scalar proximity result to a
  K-pool scalar conditional theorem, with empirical simplex coverage for small
  K-pool domains.
- Python scripts under `docs/research/` provide deterministic empirical checks
  for K-pool concavity, discrete violations, non-CPMM curve families, and
  discrete argmax proximity.

### Phase 5

- `ConcavityConservationLaw.lean` proves the formal Lipschitz gain bound,
  CPMM algebraic window-depth identity, AND the stateful CPMM attack gain
  bound (`cpmm_stateful_gain_bound`: `out_B_without_A - out_B_with_A <= L*a_A`
  for fee-free CPMM; `cpmm_stateful_gain_bound_with_fee`: same with fee
  parameter gamma). This closes the formal gap between the generic Lipschitz
  increment and the exact stateful attack model.
- `ConcavityConservationLaw.lean` also separates two attack semantics that were
  easy to conflate. The finite optimizer
  `a_B = sqrt(M*(M+a_A))` is Lean-proven for the fee-free donation/no-output
  perturbation gain `K*a_A*a_B/((M+a_B)*(M+a_A+a_B))`, via
  `cpmm_donation_gain_argmax_bound`. The fee-bearing single-pool version is
  also Lean-proven via `cpmm_donation_gain_argmax_bound_with_fee`: for net
  inputs `u = gammaA*a_A` and `v = gammaB*a_B`, the raw attacker optimizer is
  `sqrt(M*(M+gammaA*a_A))/gammaB` when `gammaB > 0`. The filled-A state-change
  gain has a different expression and approaches the asymptotic bound
  `K*a_A/(M+a_A)` as `a_B` grows; the donation optimizer is empirically
  falsified as a bound for that model.
- Empirical tests document that a second-order concavity approximation is
  falsified as a universal stateful attack bound.
- The honest security-side observation is that actual stateful gain decreases
  with pool depth in the tested model; the formal Lipschitz product alone is
  not claimed as a decreasing frontier.

### Phase 6

- `MinOutCapGameTheory.lean` proves the fixed-order filled-user no-gain
  property with formal game definitions (`utility`: if filled then output
  else 0; `batchTransition`: conditional pool state transition). Five
  theorems including `filled_user_no_profitable_deviation` (utility-based
  no-gain) and `batch_state_invariant_after_filled_deviation` (conditional
  transition equality). Codex A grade, zero findings. NOT a full Nash
  equilibrium for the (A,B) optimal ordering game.
- `nash_equilibrium_min_out_cap_test.py` is scoped as a fixed-order
  filled-user no-gain check with [Lean PROVEN + empirical replay] labels
  for the no-gain property and [Empirical] labels for welfare/collusion.
- Filled users cannot improve by lowering min_out under the fixed ordering
  in the deterministic test regime. [Lean PROVEN]
- Unfilled users can benefit from lowering min_out; this is documented as
  welfare-improving behavior, not strategic manipulation by filled users.

## Devin Workflow Context

The recovered Devin context used the `problem-solver-toolkit` workflow as the
main research loop:

1. Clarify the claim and write what would falsify it.
2. Choose a representation that exposes state, especially state variables and
   transitions.
3. Propose invariants or monovariants from constraints.
4. Attack the claim on small, boundary, and adversarial cases before proof.
5. Minimize any counterexample and revise the claim instead of forcing it.
6. Lock the method only after the claim survives attack.
7. Certify with Lean, SMT, deterministic replay, or an explicit evidence bundle.
8. Record the reusable pattern, non-claims, and replay commands.

The relevant local references are:

- `external/Morph/problem_solver_toolkit.md`
- `external/Morph/problem_solver_toolkit_v2.md`
- Codex skill: `problem-solving-toolkit`

The useful moves for this packet were:

- R6, make state explicit: use reserves, balances, path state, and subset masks
  as first-class state rather than treating orderings as opaque permutations.
- C4, normalize/canonicalize: quotient repeated users, split coordinates, and
  equivalent witness shapes where the property is invariant.
- D3, dynamic programming: replace factorial ordering search with explicit
  subset or bounded-window DP where a checker can replay the result.
- S4, counterexample hunting: treat discrete concavity, second-order stateful
  gain bounds, and broad Nash wording as hypotheses until adversarial scripts
  fail to break the narrowed claim.
- P1/P3, invariants and potentials: promote only the invariant that has a
  replayable proof or deterministic test surface.

Budget exhaustion, timeouts, or missing solver evidence mean `UNKNOWN`, not
`SUPPORTED`.

## Research Kernel MCP Instructions

Research Kernel MCP is configured locally as the `research-kernel` MCP server.
The local config uses:

```text
command: uv run --no-project --with mcp python /home/trevormoc/.codex/mcp_servers/Research-Kernel-MCP/internal/research_kernel_mcp/server.py
RESEARCH_HOME=/home/trevormoc/Downloads/Autonomous Tau DEX/internal/research_kernel
RK_MODE=safe
RK_EXECUTION=disabled_by_default
```

The `.mcp.json` and `mcp-servers.json` files are local ignored config files.
Do not commit them as part of this packet.

Before relying on the server, run the deterministic backend self-test:

```bash
uv run --no-project --with mcp python \
  /home/trevormoc/.codex/mcp_servers/Research-Kernel-MCP/internal/research_kernel_mcp/server.py \
  --self-test
```

Use Research Kernel as a durable research graph, not as consensus authority.
It stores public claims, hypotheses, evidence, counterexamples, reports, and
artifact references. Hidden reasoning should stay out of the artifact store.

Recommended MCP sequence for GPT 5.5:

1. Call `rk_start` with a scoped run such as
   `zenodex-phases-4-6-20260629` if no existing run fits.
2. Call `rk_retrieve` with modes
   `["similar_claims", "prior_failures", "contradictory_evidence"]` before
   adding new atoms.
3. Call `rk_morph` on the target theorem or algorithm before choosing a final
   formulation.
4. Call `rk_atom_add` for each public `CLAIM`, `HYPOTHESIS`, `RESULT`, `RISK`,
   or `QUESTION`. Keep unsupported material at `UNKNOWN` or `CANDIDATE`.
5. Call `rk_refute` for important claims. Set
   `counterexample_is_actual=true` only for a concrete witness.
6. Call `rk_evidence_attach` with at least one `source_uri`, `artifact_path`,
   or `artifact_text` when a claim has replay support.
7. Call `rk_frontier` when selecting the next high-value research action.
8. Call `rk_report` to produce the handoff snapshot.
9. Call `rk_promote` only after local replay, refutation, dependencies,
   provenance, contradiction search, and rationale are present. Promotion is
   fail-closed; rejected promotion is useful evidence.

The main tool surface is:

```text
rk_start
rk_atom_add
rk_link
rk_retrieve
rk_morph
rk_refute
rk_evidence_attach
rk_score
rk_frontier
rk_promote
rk_report
```

Useful resources are:

```text
rk://runs/{run_id}/summary
rk://runs/{run_id}/graph
rk://runs/{run_id}/frontier
rk://atoms/{atom_id}
rk://claims/{claim_id}
rk://memory/similar/{query}
rk://memory/contradictions/{claim_id}
rk://reports/latest
```

If the MCP client is unavailable, use the local replay gates and record the
outputs in the handoff:

```bash
python3 tools/check_research_kernel_frontier_hygiene_20260628.py
python3 tools/check_rk_frontier_spec_selector.py
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/tau/test_research_kernel_frontier_hygiene_20260628.py
```

For this Phases 4-6 packet, Research Kernel should record only the verified
scope in this handoff: continuous CPMM and 3-pool concavity lemmas, the K-pool
coordinate-slice and selected-list bridges explicitly named here, abstract
discrete argmax proximity, empirical K-pool and min-out-cap evidence, and the
explicit non-claims. It should not record production, consensus, or full Nash
claims unless later evidence actually supports them.

## Verification Run Before Handoff

Lean:

```bash
cd lean-mathlib
lake env lean Proofs/PrecommitCollusionImpossibility.lean
lake env lean Proofs/TernarySearchExactness.lean
lake env lean Proofs/TernarySearchAlgorithm.lean
lake env lean Proofs/CpmmSplitConcavity.lean
lake env lean Proofs/KPoolSplitConcavity.lean
lake env lean Proofs/ConcavityConservationLaw.lean
lake env lean Proofs/DiscreteArgmaxProximity.lean
lake env lean Proofs/KPoolDiscreteArgmaxProximity.lean
lake env lean Proofs/WindowBound.lean
```

Empirical scripts:

```bash
python3 docs/research/concavity_bounded_adversarial_test.py
python3 docs/research/concavity_conservation_law_test.py
python3 docs/research/discrete_argmax_proximity_test.py
python3 docs/research/k_pool_concavity_test.py
python3 docs/research/k_pool_discrete_argmax_proximity_test.py
python3 docs/research/k_pool_discrete_violation_test.py
python3 docs/research/nash_equilibrium_min_out_cap_test.py
python3 docs/research/non_cpmm_curve_concavity_test.py
```

Pytest wrappers:

```bash
python3 -m pytest -q \
  tests/formal/test_lean_concavity_conservation_law.py \
  tests/formal/test_lean_discrete_argmax_proximity.py \
  tests/formal/test_lean_kpool_discrete_argmax_proximity.py \
  tests/formal/test_lean_kpool_split_concavity.py \
  tests/research/test_concavity_conservation_law.py \
  tests/research/test_discrete_argmax_proximity.py \
  tests/research/test_kpool_discrete_argmax_proximity.py
```

Result: 37 pytest tests passed in 77.84s.

## Continuation Evidence Manifest

The first continuation step is a compact, source-pinned research evidence
manifest:

```bash
python3 tools/check_zenodex_phases_4_6_research_evidence.py
python3 tools/check_zenodex_phases_4_6_research_evidence.py --run-scripts
python3 tools/check_zenodex_phases_4_6_research_evidence.py --run-pytest
python3 tools/check_zenodex_phases_4_6_research_evidence.py --run-lean
```

The manifest is
`tools/zenodex_phases_4_6_research_evidence_manifest.json`. It pins the Lean
files, deterministic empirical scripts, pytest wrappers, and this handoff by
SHA-256. The checker rejects hash drift, missing critical artifacts, placeholder
Lean proof tokens, widened production or consensus claims, full Nash wording, and
the false universal stateful-attack-bound claim. The new K-pool split wrapper is
explicitly marked as `new_in_worktree` in the manifest until it is tracked.
The current continuation also pins the interval-m-backed tight argmax
composition flag and fails closed if the flag or nonclaim coverage is missing.
It also pins the bounded optimal midpoint-refinement audit flag and fails
closed if the bounded-audit nonclaim is missing.

## Non-Claims

- The production ceiling-fee effective-L bounds are low-fee empirical
  regressions, not universal claims. High-fee tests falsify the effective-L
  fee perturbation bound; the universal formal lane uses gross spot (`K/M`)
  with the fee perturbation assumption explicit in `CeilingFeeRounding.lean`.
- The full all-K continuous K-pool proof is not formalized over full unordered
  pool collections. This packet now proves the
  coordinate-slice kernel, a List-sum fixed-pool bridge, an explicit
  selected-list decomposition bridge, an order-tagged selected-list bridge for
  both selected-pair orders, active-before-remainder and
  remainder-before-active arbitrary-index List decomposition bridges, concrete
  active/remainder index witnesses inside
  supplied decompositions, a bounded active/remainder removal bridge for those
  supplied decompositions, active-before-remainder and remainder-before-active
  arbitrary-index active/remainder removal bridges, a fixed-pool permutation
  quotient bridge for the fixed non-moving pool compression, a proof-carrying
  unordered selection certificate bridge for supplied
  full-presentation/decomposition/canonical-fixed witnesses, full-List
  ordered-index constructors for that certificate in both selected-pair orders,
  identity-stable full-List presentation bridges for duplicate-valued pool
  selection by distinct ids, an id-ordered full-List presentation bridge for
  supplied stable-id ordered presentations, a stable-id sorted-output
  certificate bridge from arbitrary identified input Lists to supplied
  id-ordered permutation representatives, an executable stable-id List
  merge-sort bridge for arbitrary identified Lists with unique stable ids, a
  stable-id List permutation quotient bridge for valid identified List
  presentations, a keyed `Finset Nat` presentation/quotient/concavity bridge
  for stable-id unordered presentations with consistent lookups, a `Multiset`
  presentation/quotient/certificate-output/concavity bridge for unordered
  identified-pool collections under a no-duplicate-stable-id contract, a
  Multiset stable-id selection bridge deriving selected-pair index order from
  sorted-output stable-id order, a stable-id lookup witness bridge binding
  selected IDs to unique sorted-output positions, a runtime stable-id lookup
  checker for canonical JSON bytes, duplicate-key rejection, duplicate stable-ID
  rejection, selected-ID membership, sorted-output index consistency, and
  selected-pair order, a runtime-to-Lean stable-id lookup assumption bridge
  that emits a canonical certificate-relative assumption packet for sorted
  stable IDs, selected lookup witnesses, selected-pair order, and certificate
  hash, a generated Lean witness module tying those constants to
  `StableIdSortedLookupWitnessCont` obligations and the lookup index-order
  theorem, a generated Lean domain witness module tying per-pool digests to
  concrete `IdentifiedFixedPoolTermCont` fields and the executable stable-id
  List merge-sort certificate path, a runtime unordered domain canonicalizer
  that normalizes valid pool-order permutations to the same sorted
  proof-facing certificate and Lean witness source, one concrete 4-pool
  coordinate instance, and one concrete 5-pool coordinate instance.
  Production settlement integration and a top-level all-K theorem remain open.
- The min-out-cap game-theory evidence is a fixed-order filled-user no-gain
  check, not a full Nash equilibrium proof.
- The concavity second-order approximation is not a universal stateful attack
  bound. The test suite intentionally includes falsification guards for that
  approximation. The Lean-proven stateful gain bound (`cpmm_stateful_gain_bound`)
  uses the Lipschitz constant L*a_A, not the falsified concavity formula.
- The stateful CPMM attack gain bound `gain <= L*a_A` is Lean-proven
  (`cpmm_stateful_gain_bound` for fee-free, `cpmm_stateful_gain_bound_with_fee`
  for fee-bearing CPMM). The empirical scaling probe in
  `concavity_bounded_adversarial_test.py` uses `|f''(0)|` (maximum curvature)
  which gives a tighter constant but is empirical only.
- The tightest generic argmax-distance certificate under strong concavity and
  one-sided ceiling-fee perturbation is the oracle radius
  `sqrt(2*(f_cont(b*)-f_prod(argmax))/m)`. The best certified-anchor radius is
  `sqrt(2*tau/m)`, where `tau = f_cont(b*) - f_prod(anchor)`. The universal
  gross-spot envelope gives `tau <= alpha + eta_bound`; the low-fee `3L+2`
  window remains empirical.
- The one-sided `sqrt(2*(alpha+epsilon)/m)` radius is formally sharp for the
  abstract hypotheses via a quadratic witness. The witness is not a production
  CPMM instance, and any tighter production radius needs additional certified
  structure.
- The tight argmax certificate checker is research-scope evidence only. It
  validates a supplied packet against recomputed values and rejects stale,
  noncanonical, authority-bearing, or radius-understating packets. It is not
  wired into production routing, settlement, or consensus authority.
- The tight argmax certificate float-domain guard bounds only the research
  checker's float recomputation lane to 128-bit inputs. Larger domains need an
  exact-arithmetic certificate path before they can be replayed in this checker.
- The interval-m-backed tight argmax certificate path consumes a checked
  curvature certificate before accepting a tighter radius. It does not choose
  the production argmax, prove optimal interval placement, or change production
  routing, settlement, or consensus authority.
- The closed-form exact-curvature minimizer checker is bounded to the 128-bit
  research float domain and rejects larger domains before conversion. Use the
  rational interval certificate path for exact-arithmetic floors outside that
  lane.
- The bounded optimal midpoint-refinement audit is exact only within the
  stated 16-interval midpoint-split cap. It is not a proof of unbounded greedy
  optimality or continuous optimal interval placement.
- The donation/no-output exact optimizer is single-pool and scoped to the
  donation/no-output perturbation gain. The fee-bearing theorem requires a
  positive attacker fee multiplier `gammaB`; when `gammaB = 0`, there is no
  finite raw attacker-size optimizer. It is not a bound for the filled-A
  state-change gain in `cpmm_stateful_gain_bound_tight`, and multi-hop donation
  optimizer extensions remain open.
- These files are research evidence and proof artifacts; they do not change
  consensus authority or production runtime behavior.
- `src/core/kpool_stable_id_lookup_certificate.py` is a deterministic boundary
  checker for a research certificate format. It is not wired into consensus
  authority or production settlement behavior.
- The same module emits the Lean-facing assumption packet only after a
  certificate is accepted. Lean still consumes mathematical assumptions; it does
  not parse JSON bytes directly.
- `lean-mathlib/Proofs/KPoolRuntimeLookupWitnessGenerated.lean` is generated
  evidence for the proof-facing obligation shape. It does not prove production
  pool economics from `pool_digest` values and is not wired into consensus
  authority.
- `lean-mathlib/Proofs/KPoolRuntimeDomainWitnessGenerated.lean` is generated
  evidence for a digest-bound concrete List-domain witness. It binds example
  `pool_digest` values to Lean-visible `K`, `M`, `c`, and fixed-input `a`
  constants before constructing the executable stable-id List certificate
  wrapper. It does not prove production settlement integration, consensus
  authority, or the top-level production unordered-container API.
- The runtime unordered domain canonicalizer is a research-only intake bridge:
  it accepts valid pool-order permutations, rejects duplicate IDs and drift, and
  emits the same sorted proof-facing certificate and generated Lean witness
  source. It is not a production settlement adapter and does not change
  consensus authority.

## Recommended GPT 5.5 Continuation

1. Package the stable-id List permutation quotient as unordered-presentation
   certificates, then connect those certificates to the existing proof-carrying
   selection path.
   DONE: `IdentifiedFinsetPresentationCont` in `KPoolSplitConcavity.lean`
   keys on `Finset Nat` (stable ids) with a lookup function, avoiding the
   `DecidableEq` issue on `ℝ`-bearing pool terms. The bridge theorem
   `stableIdSortedPoolsCont_eq_of_finset_eq` proves that any two Finset
   presentations with the same id set and consistent lookups produce the
   same sorted output. The concavity theorems
   `splitFunctionConcave_of_finsetActiveBeforeRemainder` and
   `splitFunctionConcave_of_finsetRemainderBeforeActive` compose the
   Finset-to-List materialization with the existing merge-sort concavity
   path for both selected-pair orders. DONE:
   `IdentifiedMultisetPresentationCont` materializes
   `Multiset IdentifiedFixedPoolTermCont` through `Multiset.toList`,
   `stableIdSortedPoolsCont_eq_of_multiset_eq` proves equal multisets
   canonicalize to the same sorted output, and
   `stableIdMergeSortPresentationCertificate_output_pools_eq_of_multiset_eq`
   proves equal multisets expose the same executable certificate-output pool
   sequence. The concavity theorems
   `splitFunctionConcave_of_multisetActiveBeforeRemainder` and
   `splitFunctionConcave_of_multisetRemainderBeforeActive` compose the
   Multiset-to-List materialization with the merge-sort concavity path for both
   selected-pair orders. DONE:
   `MultisetStableIdActiveBeforeRemainderSelectionCont`,
   `MultisetStableIdRemainderBeforeActiveSelectionCont`,
   `stableIdSortedPoolsCont_index_lt_of_id_lt`, and the two
   `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableId...`
   theorems derive selected-pair index order from stable-id order before
   consuming the Multiset concavity path. DONE:
   `StableIdSortedLookupWitnessCont`,
   `stableIdSortedLookupWitness_index_unique`,
   `MultisetStableIdLookupActiveBeforeRemainderSelectionCont`,
   `MultisetStableIdLookupRemainderBeforeActiveSelectionCont`, and the two
   `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableIdLookup...`
   theorems move the public selection surface to stable-ID lookup witnesses
   while deriving the existing index-witness record internally. DONE:
   `src/core/kpool_stable_id_lookup_certificate.py` adds a deterministic
   boundary checker for canonical bytes, duplicate JSON keys, duplicate stable
   IDs, absent selected IDs, out-of-bounds indices, ID/index mismatch, and
   selected-pair order mismatch, with named reject reasons covered by
   `tests/core/test_kpool_stable_id_lookup_certificate.py`. DONE:
   the same module adds a runtime-to-Lean assumption bridge that emits a
   canonical certificate-relative packet containing sorted stable IDs, active
   and remainder lookup witnesses, selected-pair order, and certificate hash.
   The tests mutate each bridge field and require named rejection for stale
   hash, sorted-ID drift, lookup drift, order drift, duplicate JSON keys, and
   noncanonical bytes. DONE:
   `lean-mathlib/Proofs/KPoolRuntimeLookupWitnessGenerated.lean` is a
   deterministic generated witness module for the accepted example packet. It
   binds the certificate hash, assumption hash, sorted stable IDs, active and
   remainder lookup constants, witness obligations, and selected-pair order to
   the existing Lean lookup index-order theorem. The runtime tests require the
   fixture to match the renderer byte-for-byte and reject source mutations.
   DONE:
   `lean-mathlib/Proofs/KPoolRuntimeDomainWitnessGenerated.lean` is a
   deterministic generated domain witness module for the accepted example
   packet. It binds `pool_digest` values to canonical pool-domain payloads,
   emits concrete `IdentifiedFixedPoolTermCont` values, proves sorted stable ID
   and in-bounds selected-index facts by computation, constructs the executable
   stable-id List certificate, and wraps the existing concavity theorem under
   the existing domain hypotheses. The runtime tests mutate digest, economics,
   lookup, order, and generated source fields with named rejection.
   DONE: the runtime unordered domain canonicalizer now accepts valid
   pool-order permutations and emits the same sorted proof-facing certificate
   and generated Lean witness source, while rejecting duplicate IDs,
   noncanonical bytes, stale lookup hashes, digest/economics drift, selection
   drift, schema drift, and duplicate JSON keys. Production settlement
   integration and a top-level all-K theorem remain open.
   Codex review: A grade, zero findings. Confirmed Multiset permutation bridge
   soundness, stable-id Nodup transfer, selected-id-to-index ordering, lookup
   witness uniqueness, and lookup lowering all compose cleanly with the
   existing merge-sort path.
2. Model ceiling-fee rounding in Lean to keep the production effective-L
   empirical constants scoped and prove the conservative gross-spot lane.
   DONE: `CeilingFeeRounding.lean` formalizes the production CPMM swap
   arithmetic (ceiling fee + floor output) and proves conservative floor
   error and argmax proximity bounds (`K0/M0 + K1/M1 + 2` and
   `L + K0/M0 + K1/M1 + 2`). It also proves the coupled continuous-split
   Lipschitz max-bound
   `|splitCont(x)-splitCont(y)| <= max(c0*K0/M0,c1*K1/M1)*|x-y|`,
   replacing the looser sum-of-components argument for the continuous split
   objective. The proved production bounds are the universal gross-spot lane;
   the effective-L constants are low-fee empirical regressions and are
   high-fee falsified as universal constants.
   Key theorems: `cpmm_output_lipschitz_wrt_net`
   (K/M Lipschitz constant), `cpmm_prod_floor_error_bound_directed`
   (per-pool floor error in [0, K/M+1)), `split_prod_floor_error_bound`
   (2-pool split floor error), `cpmm_prod_discrete_argmax_proximity`
   (production argmax proximity), `cpmm_prod_certified_anchor_argmax_distance`
   (gross-envelope production argmax-distance radius), and
   `split_lipschitz_coupled` (continuous split Lipschitz max-bound).
   `DiscreteArgmaxProximity.lean` also includes the sharpness witness
   `abstract_one_sided_perturbed_argmax_distance_sharp_quadratic`.
   `docs/research/discrete_argmax_proximity_test.py` also validates the
   derived research certificate boundary with 300 accepted certificates and 9
   structured negative cases.
   `docs/research/concavity_conservation_law_test.py` also validates the
   pool-parameter `m` certificate boundary with 300 accepted certificates and
   11 structured negative cases. This supplies the deterministic endpoint-`m`
   certificate used by the tight argmax-radius chain. The exact-curvature
   follow-up adds 300 accepted exact-floor certificates, 11 structured
   mutation rejections, and a deterministic replay showing improvement over
   the endpoint floor in 296 of 300 seeded domains. The rational interval
   follow-up adds 300 accepted interval certificates, 15 structured mutation
   rejections, and exact arithmetic replay showing improvement over the
   endpoint floor in 296 of 300 seeded domains. The interval floor is a finite
   cover lower bound, not a proof of exact equality with `inf(T0+T1)`. The
   best-cover follow-up adds 300 generated certificates, improves over the
   uniform 64-interval certificate in 295 of 300 seeded domains, and reaches
   a maximum best-over-uniform improvement of `1.01264x`. The greedy
   refinement follow-up adds the Lean split-monotonicity theorem, 300 generated
   certificates, improvement over the base cover in 296 of 300 seeded domains,
   and a maximum refined-over-base improvement of `1.1129x`. The exact
   minimizer is still research replay rather than a Lean-proven formula; its
   float lane now rejects domains above the 128-bit research bound before
   conversion, and the second-derivative identity and Taylor-remainder bridge
   remain explicit obligations.
   Codex A grade achieved through a 4-iteration sub-loop
   (A- -> A- -> A- -> A), all findings were LOW scope-wording issues.
3. Turn the fixed-order no-gain evidence into a precise game definition.
   DONE: `MinOutCapGameTheory.lean` proves the fixed-order filled-user
   no-gain property (filled_user_no_profitable_deviation,
   batch_state_invariant_after_filled_deviation) with explicit non-claims
   (NOT a full Nash equilibrium for the (A,B) optimal ordering game).
4. Connect the Lipschitz increment theorem to the exact stateful CPMM attack
   model. DONE: `cpmm_stateful_gain_bound` and `cpmm_stateful_gain_bound_with_fee`
   in `ConcavityConservationLaw.lean` prove `gain <= L*a_A` for the exact
   stateful CPMM attack model (fee-free and with fee). The stateful security
   side is now formally proven, not just empirical.
5. Keep the Phases 4-6 evidence manifest current whenever a pinned artifact,
   replay command, or supported-scope statement changes.
