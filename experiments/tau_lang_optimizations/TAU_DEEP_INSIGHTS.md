# Tau Lang Deep Insights

This note captures the strongest optimization and modeling patterns I found
while studying the project specs and Tau itself.

## 1. The file-runner and the REPL path are not equivalent

- Tau's raw file-runner (`tau <file> -x`) rejects helper predicate/function
  definitions that the repo's REPL-based runner can handle after inlining.
- The project already works around this in
  [tau_runner.py](/home/trevormoc/Downloads/Autonomous%20Tau%20DEX/src/integration/tau_runner.py)
  by:
  - normalizing the spec,
  - parsing helper definitions,
  - inlining them into `always` expressions,
  - re-emitting a file-runner-safe or REPL-safe form.

Consequence:
- “Spec compiles” in Tau depends on which execution path you mean.
- For experiments, the authoritative path is the repo runner, not raw `tau -x`
  against the original file text.

## 2. Parenthesize the entire `always` body

- Tau does not safely infer that `always A && B && C` means `always (A && B && C)`.
- If the outer body is not wrapped, later conjuncts can be treated as unscoped
  top-level formulas and fail parsing or behave differently.

Pattern:
- Always use `always ( ... ).` with the full conjunction inside one pair of
  parentheses.

## 3. Avoid output-to-output composition inside the same `always`

- Referencing `o1[t]`, `o2[t]`, ... inside the definition of `oN[t]` makes the
  runtime behavior much less predictable.
- Flattening the final gate to duplicate the underlying conditions is more
  stable and often faster.

Observed result:
- `batching_v1_5_explained.tau` became much more stable after flattening.
- The compact single-gate batching variant is substantially faster than both the
  baseline and the explained multi-output variant.

## 4. Aligned-history inputs beat temporal lookback when the host already has history

- Several settlement specs document `i5..i7` as `prevprev/prev/curr`, but still
  use `t-2` and `t-1` indexing against one of those streams.
- If the host already supplies the 3-sample window at each step, same-step
  anti-sandwich checks are simpler and remove warmup clutter.

Pattern:
- Prefer same-step bundled history for short lookback properties.
- Use temporal indexing only when the history is genuinely stream-native.

## 5. Two operator families matter for optimization

- Formula logic: `&&`, `||`, `!`, `->`, `<->`
- Term algebra / boolean-as-data: `&`, `|`, `'`

Pattern:
- Use formula operators for logical predicates.
- Use `sbf` and term operators only when you intentionally want a boolean value
  as data.
- Avoid mixing these styles casually; it increases sort inference problems.

## 6. Multi-output observability and runtime speed trade off directly

- More outputs make traces much better, but they add cost.
- This is visible in the batching family:
  - baseline `batching_v1_4`: weaker semantics, single output
  - `batching_v1_5_explained`: stronger semantics, six outputs
  - `batching_v1_5_compact_single_gate`: stronger semantics, one output

Pattern:
- Keep both a compact production candidate and an explained debugging variant.

## 7. Host or module flags are a practical Tau optimization boundary

- Full CPMM arithmetic and composite tokenomics checks are expensive in Tau.
- Hybrid specs that consume host-computed or separately verified `sbf` flags are
  a realistic design pattern:
  - Tau retains the final fail-closed gate.
  - Heavy arithmetic can move to a more suitable engine or a separately checked
    witness pipeline.

Pattern:
- Use Tau for cheap cross-field structure and deterministic composition.
- Use host/module flags for expensive subproofs, but only if those flags are
  themselves produced by audited or independently checked logic.

## 8. bv[32] arithmetic remains the main pain point here

- The swap and settlement families are still timeout-prone in the current repo
  runner even after flattening and flag-gating.
- The batching family does not have the same issue.

Inference:
- Tau is much happier with compact membership/order logic than with wider
  bitvector arithmetic compositions in this project configuration.

## 9. Production posture for Tau specs in this repo

The strongest pattern I found is a three-tier split:

1. Compact production gate
- One output.
- Flattened logic.
- No output-to-output dependencies.
- Aligned inputs instead of temporal warmup where possible.

2. Explained debugging gate
- Multiple outputs for diagnostics.
- Same semantics as the compact gate where possible.
- Not assumed to be fastest.

3. Proof-gated or host-flag gate
- Tau composes high-level structure.
- Expensive arithmetic is discharged outside Tau and imported as `sbf` facts.

That split is now reflected in the experiment variants under this folder.

## 10. Positive witnesses can be harder than negative witnesses

- A failing batching witness (`1,2,3,5` against included `1,2,3,4`) runs
  quickly in the compact batching gate.
- A fully passing batching witness in that same monolithic compact gate stayed
  timeout-prone even with much larger budgets.

Practical consequence:
- Do not assume that a smaller spec is equally easy on positive and negative
  traces.
- When positive witnesses are expensive, split the gate into rails and compose
  the final answer explicitly.

## 11. External joins are not a workaround here, they are the optimization pattern

- For batching, swap, and settlement, the most reliable evidence posture ended
  up being:
  - tiny Tau rails with trace-backed outputs,
  - explicit composition outside Tau,
  - optional compact bundle specs where Tau can still handle the conjunction.

This is the main optimization insight from the second pass of work:
- “More complete” in Tau often means “more decomposed but still fail-closed,”
  not “stuff every condition back into one larger spec.”
