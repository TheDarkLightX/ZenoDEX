# Mac Agent Operating Loop

This is the direct instruction packet for the Codex agent running on the Mac.
Assume no prior chat context. Use this file to decide what to do.

## Mission

Use the local 128GB M3 Max machine to reduce disaster states for ZenoDEX,
ZenoOracle, and ZenoProof before spending Runpod money.

The immediate research target is derivatives and funding math:

- search for exotic but implementable derivative and funding shapes;
- tie any payout, burn, or funding flow to realized protocol activity;
- find counterexamples first;
- rerank survivors with heavier simulations;
- extract public regression tests and formal proof targets.

This is bounded evidence, not a safety proof. A run that finds no failure under
one seed only means no failure was found under those bounds.

## Repo Context

Important public surfaces:

- `docs/derivatives/`
- `docs/research/ZENODEX_YIELD_LIKE_FUNDING_SHAPES_V1.md`
- `docs/research/ZENODEX_ARISTOTLE_MATH_ANALYSIS_V1.md`
- `lean-mathlib/Proofs/`
- `tools/macos_scout/`
- `tools/run_derivatives_evidence.sh`
- `tools/perp_oracle_manipulation_sweep.py`
- `tools/perps_scientist_parallel_benchmark.py`

Use `internal/` for raw run outputs. It is git-ignored. Promote only distilled
reports, tests, proof targets, or tool improvements into tracked paths.

## Non-Negotiable Rules

- Do not commit raw `internal/macos_scout_runs/` outputs.
- Do not claim legal compliance from a simulation.
- Do not claim a design is safe without a formal target or regression evidence.
- Do not optimize only for score. Counterexamples are more valuable than high
  scores.
- Do not use private keys, production credentials, or live treasury data.
- Keep commits scoped. The repo may have unrelated dirty work.

## Loop 0: Environment And Reviewed Commit

Start from a reviewed, immutable handoff commit. Do not execute scout scripts from
`codex/macos-scout-handoff` merely because that mutable branch currently points
there; a force-push can change branch contents after review.

Preconditions before running any scout script:

- `HANDOFF_COMMIT` is the 40-hex commit SHA reviewed and approved for this run.
- The working tree is clean or contains only changes you intentionally preserve.
- `git rev-parse HEAD` must match `HANDOFF_COMMIT` after checkout.

```bash
HANDOFF_COMMIT=<reviewed-40-hex-commit-sha>
test "$HANDOFF_COMMIT" != "<reviewed-40-hex-commit-sha>"
printf '%s\n' "$HANDOFF_COMMIT" | grep -Eq '^[0-9a-fA-F]{40}$'
git fetch origin codex/macos-scout-handoff
git checkout --detach "$HANDOFF_COMMIT"
test "$(git rev-parse HEAD)" = "$HANDOFF_COMMIT"
git status --short --branch
```

If any command above fails, stop. Do not fall back to `git checkout
codex/macos-scout-handoff` or any other mutable branch checkout before running
local scripts.

Confirm tools only after the reviewed commit is checked out and verified:

```bash
julia --version
python3 --version
bash -n tools/macos_scout/run_macos_scout.sh
python3 -m py_compile tools/macos_scout/summarize_scout_outputs.py
```

If Julia is missing, install Julia for macOS first. Do not rewrite the scout in
Python just to avoid installing Julia.

## Loop 1: Machine Profile

Run the smoke job:

```bash
bash tools/macos_scout/run_macos_scout.sh smoke
```

Inspect:

```bash
ls -td internal/macos_scout_runs/*_smoke | head -n 1
sed -n '1,220p' "$(ls -td internal/macos_scout_runs/*_smoke | head -n 1)/review.md"
sed -n '1,220p' "$(ls -td internal/macos_scout_runs/*_smoke | head -n 1)/host_info.txt"
```

Confirm:

- Julia uses all expected threads;
- `review.md` has top candidates and reranked candidates;
- `counterexamples.jsonl` is non-empty or the bounds are too weak;
- no output was written outside `internal/`.

If threads are too low:

```bash
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_macos_scout.sh smoke
```

## Loop 2: CPU-Heavy Scout

Run the main scout:

```bash
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_macos_scout.sh scout
```

If the Mac is responsive and memory pressure is low, run:

```bash
bash tools/macos_scout/run_macos_scout.sh deep
```

For a maximum local campaign:

```bash
bash tools/macos_scout/run_macos_scout.sh soak
```

Manual tuning examples:

```bash
CANDIDATES=250000 PATHS=96 STEPS=128 RERANK_TOP=250 RERANK_PATHS=512 RERANK_STEPS=256 \
  bash tools/macos_scout/run_macos_scout.sh deep
```

```bash
CANDIDATES=1000000 PATHS=96 STEPS=128 RERANK_TOP=500 RERANK_PATHS=768 RERANK_STEPS=256 \
  bash tools/macos_scout/run_macos_scout.sh soak
```

The launcher already sets:

```text
OPENBLAS_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1
OMP_NUM_THREADS=1
JULIA_EXCLUSIVE=1
```

These settings keep nested math libraries from stealing cores from Julia's task
threads.

## Loop 3: Optional Metal GPU Prefilter

Metal is optional. CPU simulation remains authoritative.

Smoke-test Metal:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

If Metal.jl is missing and you want to test GPU:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl --install
```

If Metal works:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_prefilter.jl \
  --n 1000000 \
  --out internal/macos_scout_runs/metal_prefilter
```

Then run CPU reranking. Treat Metal output as candidate generation only.

## Loop 4: Review Outputs

For each run, open:

```bash
RUN_DIR="$(ls -td internal/macos_scout_runs/* | head -n 1)"
sed -n '1,240p' "$RUN_DIR/review.md"
head -n 20 "$RUN_DIR/counterexamples.jsonl"
head -n 20 "$RUN_DIR/reranked_top_candidates.jsonl"
```

Review order:

1. Counterexamples.
2. Reranked candidates.
3. Pareto front.
4. Initial top candidates.

Initial winners are allowed to fail under reranking. When that happens, record
the failure as useful evidence.

## Loop 5: Second-Seed Check

Do not promote a formula from one seed. Re-run with a second seed:

```bash
SEED=20260509 bash tools/macos_scout/run_macos_scout.sh scout
```

If the same candidate class survives two seeds, make a short tracked report.
If it fails, promote the repeated failure mode into a regression target.

## Loop 6: Promotion Decisions

Use this predicate:

```text
PromoteCandidate :=
  survives_two_seeds
  and rerank_disaster_rate_is_zero_or_explained
  and payout_source_is_realized_activity
  and burn_or_treasury_flow_is_capped
  and no_fixed_passive_return_claim
  and replay_inputs_are_recorded
  and proof_target_is_written
```

Practical meaning: the mechanism can be discussed only as a bounded candidate,
and it needs a proof target before it becomes a design claim.

Use this counterexample predicate:

```text
PromoteCounterexample :=
  appears_in_multiple_candidates
  or appears_after_reranking
  or violates a core safety intuition
```

Practical meaning: a repeated failure mode should become a regression test,
chaos scenario, Lean/SMT obligation, or research note.

## Loop 7: What To Write Back

Create one tracked report when a meaningful run finishes:

```text
docs/macos_scout/MACOS_SCOUT_RUN_REPORT_<YYYYMMDD>.md
```

The report should include:

- machine profile from `host_info.txt`;
- commands run;
- thread count;
- candidate/path/step counts;
- top reranked candidates;
- first counterexample classes;
- what failed under second seed;
- proposed public tests;
- proposed Lean/SMT proof targets;
- exact internal run directory names, without committing the raw directories.

If you improve scripts, commit only the script/docs changes and the report.

## Loop 8: Formal Targets To Extract

For each candidate worth keeping, write a proof target in plain English first:

```text
For all admissible states s and steps t:
  realized_fee_budget(s, t) >= burn(s, t) + insurance_credit(s, t)
```

The interpretation is that deflation and insurance funding cannot exceed
realized protocol activity.

Other useful targets:

```text
insurance_after >= 0
payout <= payout_cap_share * insurance_before
funding_abs <= funding_cap
oracle_gap > threshold -> risk_haircut is monotone
liquidity < floor -> action is rejected or capped
```

Convert only stable targets into Lean/SMT work. Do not formalize noisy formulas
that failed reranking.

## Loop 9: What Counts As Done

Minimum useful completion:

- smoke run completed;
- scout run completed;
- `review.md` inspected;
- second seed attempted or reason recorded;
- one report written under `docs/macos_scout/`;
- branch committed and pushed.

Strong completion:

- deep or soak run completed;
- Metal smoke result recorded;
- repeated counterexample classes identified;
- at least one public regression or proof target proposed;
- report committed and pushed.

## Commit And Push

Before committing:

```bash
git status --short
```

Stage only tracked handoff/report/tool files, never raw `internal/` runs:

```bash
git add docs/macos_scout tools/macos_scout
git commit -m "Record MacOS scout run findings"
git push
```

If there are unrelated dirty files, leave them alone.
