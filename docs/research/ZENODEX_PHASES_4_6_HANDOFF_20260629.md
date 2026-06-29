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

- `KPoolSplitConcavity.lean` proves 3-pool coordinate-wise continuous concavity.
- `DiscreteArgmaxProximity.lean` replaces the false discrete-concavity target
  with an abstract argmax-proximity theorem plus CPMM conditional instantiation.
- `KPoolDiscreteArgmaxProximity.lean` lifts the scalar proximity result to a
  K-pool scalar conditional theorem, with empirical simplex coverage for small
  K-pool domains.
- Python scripts under `docs/research/` provide deterministic empirical checks
  for K-pool concavity, discrete violations, non-CPMM curve families, and
  discrete argmax proximity.

### Phase 5

- `ConcavityConservationLaw.lean` proves the formal Lipschitz gain bound and
  CPMM algebraic window-depth identity.
- Empirical tests document that a second-order concavity approximation is
  falsified as a universal stateful attack bound.
- The honest security-side observation is that actual stateful gain decreases
  with pool depth in the tested model; the formal Lipschitz product alone is
  not claimed as a decreasing frontier.

### Phase 6

- `nash_equilibrium_min_out_cap_test.py` is intentionally scoped as a
  fixed-order filled-user no-gain check, not a full Nash equilibrium proof.
- Filled users cannot improve by lowering min_out under the fixed ordering in
  the deterministic test regime.
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
scope in this handoff: continuous CPMM and 3-pool concavity lemmas, abstract
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
  tests/research/test_concavity_conservation_law.py \
  tests/research/test_discrete_argmax_proximity.py \
  tests/research/test_kpool_discrete_argmax_proximity.py
```

Result: 36 pytest tests passed in 72.88s.

## Non-Claims

- The production ceiling-fee bounds are empirical, not Lean-proven.
- The K > 3 continuous K-pool proof is documented by separability but not
  formalized with Finset sums.
- The min-out-cap game-theory evidence is a fixed-order filled-user no-gain
  check, not a full Nash equilibrium proof.
- The concavity second-order approximation is not a universal stateful attack
  bound. The test suite intentionally includes falsification guards for that
  approximation.
- These files are research evidence and proof artifacts; they do not change
  consensus authority or production runtime behavior.

## Recommended GPT 5.5 Continuation

1. Formalize the K > 3 split concavity statement with Finset/List sums.
2. Model ceiling-fee rounding in Lean to replace the production empirical
   `2L + 2` and `3L + 2` constants with checked lemmas.
3. Turn the fixed-order no-gain evidence into a precise game definition before
   claiming equilibrium properties.
4. Connect the Lipschitz increment theorem to the exact stateful CPMM attack
   model, or keep the stateful security side explicitly empirical.
5. Add a compact evidence manifest for this Phases 4-6 packet once the next
   formalization step is selected.
