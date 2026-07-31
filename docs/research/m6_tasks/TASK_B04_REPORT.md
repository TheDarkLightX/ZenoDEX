# FCIS M6 Task B04 Report

TASK_ID: B04
BASE_SHA: `4ea8611852f2fe1aad0177bf4f7ea0e1c921c9b5`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B04-adaptive-trace-20260731`

IMPLEMENTATION_HEAD_SHA: `b182bdbdc842ef54f46194a31b3a76e3d6efc906`
IMPLEMENTATION_TREE: `fb91f2655b48e3b286b175e712e87b4b083832a9`

FILES_CHANGED:

- `lean-mathlib/Proofs/FCISFeeApportionmentSRGDAdaptiveTrace.lean`
- `lean-mathlib/Proofs.lean`
- `docs/research/m6_tasks/TASK_B04_REPORT.md`
- `docs/research/m6_tasks/TASK_B04_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B04_LEAN_PROOF_RECEIPT.json`
- `docs/research/m6_tasks/TASK_B04_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The B04 Lean module defines a typed authenticated-policy
witness, a policy-bearing SRGD occurrence, a three-coordinate deficit state,
an ordered segment fold, and a nested ordered SLNF word fold. It defines
state-indexed `ValidSegment` and `ValidWord` relations and proves that every
valid occurrence, segment, and finite word preserves zero-sum state and the
strict `(-D, D)` bound. Each occurrence carries its own denominator-bound
policy witness, so the theorem does not assume a fixed policy. The nested word
carrier preserves segment boundaries and never flattens the input.

COMMANDS_RUN:

- Ephemeral `external -> ../external` dependency link for the local mathlib
  checkout; the link was removed after each formal gate.
- `cd lean-mathlib && lake env lean Proofs/FCISFeeApportionmentSRGDAdaptiveTrace.lean`
- `cd lean-mathlib && lake build`
- The selected Lean proof audit and placeholder scan, recorded in
  `TASK_B04_LEAN_PROOF_RECEIPT.json`.
- A `#print axioms` audit for all three public B04 theorems.
- `rg -n -i 'sorry|admit|axiom|unsafe'` over the new theorem module.
- `git diff --check` and `git diff --cached --check`.

RESULTS:

- Focused Lean target: pass under Lean 4.27.0.
- Full package build: pass, 8,149 jobs.
- Placeholder audit: pass; no proof placeholders found.
- Explicit source scan: no `sorry`, `admit`, `axiom`, or `unsafe` in the new
  module.
- `one_occurrence_preserves_state` discharges each policy, fraction-bound, and
  SRGD-relation premise through the reviewed one-step theorem.
- `valid_segment_preserves_state` is an induction over the state-indexed
  occurrence relation.
- `valid_word_preserves_state` is an induction over the state-indexed nested
  segment relation.
- Axiom audit:
  - `one_occurrence_preserves_state`: `[propext, Classical.choice, Quot.sound]`
  - `valid_segment_preserves_state`: `[propext, Classical.choice, Quot.sound]`
  - `valid_word_preserves_state`: `[propext, Classical.choice, Quot.sound]`
  These are Lean's standard logical foundations. No user axiom or proof
  placeholder was introduced.
- No caller, datastore adapter, authority switch, deployment, or value-moving
  path was mounted.

MUTANTS_ADDED: None. B04 is a formal induction slice. The nested carrier and
state-indexed relations are explicit source-level obligations; production
flattening and authority bypass mutations remain later runtime tasks.

FORMAL_EVIDENCE: Lean compilation, full package build, placeholder scan, and
the per-theorem axiom audit are recorded. The theorem applies arbitrary
per-occurrence policy witnesses through the relation carrier.

REMAINING_NONCLAIMS:

- The `AuthenticatedPolicy` structure is a typed theorem carrier. It is not a
  production cryptographic verifier, authority grant, or mounted caller path.
- B04 does not prove the cumulative discrepancy/history identity theorem.
- B04 does not complete the general U256 Lean theorem or Python/Rust
  refinement.
- B04 does not prove a production allocator, datastore, consensus, API,
  migration, or runtime refinement.
- Local Lean success depends on the existing nearby mathlib checkout through an
  ephemeral uncommitted link; no dependency path was committed.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.
- The shared all-packet validator's historical-source-hash limitation remains
  from B02; this selected B04 packet is validated separately.
- M6 remains research-only, executable, and unmounted. Nothing here authorizes
  value movement.

REVIEW_RISKS: The policy root is a typed placeholder for the later proof-context
and verifier mounting work. Segment preservation is represented by the nested
word carrier and state-indexed relation; no production SLNF parser or runtime
adapter is claimed. The full production and cross-runtime refinement boundary
remains open.
