# Mac Agent Compute-Max Work Queue

This is the next work packet for a Codex session running on the 128GB M3 Max
Mac. The goal is to spend local compute on bounded evidence that can reduce
ZenoDEX, ZenoOracle, and ZenoProof disaster states before using paid remote
compute.

Treat every result as untrusted until replayed. Promote only distilled tests,
proof targets, receipts, and short reports. Keep raw run directories under
`internal/`.

## Shared State

```json
{
  "schema": "rlm-subagent-state/v1",
  "objective": "Use the Mac to run high-volume ZenoDEX disaster-state search and promote replayable hardening artifacts.",
  "constraints": {
    "must_hold": [
      "no raw internal run directories are committed",
      "candidate mechanisms need at least two surviving seeds before promotion",
      "counterexamples become regression tests before design claims",
      "proof or replay obligations fail closed on timeout, unknown, or missing dependencies"
    ],
    "must_not": [
      "claim legal compliance from a simulator",
      "loosen critical runtime guards to make a candidate pass",
      "rewrite consensus-critical core without isolated tests and a focused review"
    ],
    "formal_methods": {
      "preferred": true,
      "tooling": ["Lean", "SMT", "ESSO", "Julia"],
      "fail_closed": true
    }
  },
  "budget": {
    "max_depth": 2,
    "max_width": 3,
    "max_rounds": 6,
    "stop_when": [
      "one overnight compute campaign is summarized",
      "repeated counterexamples are promoted to public tests",
      "no high-signal candidate survives two seeds",
      "machine begins swapping or thermal throttling severely"
    ]
  }
}
```

## Track A: Derivatives And Funding Search

Run the campaign wrapper first:

```bash
git pull
chmod +x tools/macos_scout/run_compute_campaign.sh
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_compute_campaign.sh
```

If the machine stays responsive and memory pressure remains low:

```bash
RUN_SOAK=1 JULIA_NUM_THREADS=auto bash tools/macos_scout/run_compute_campaign.sh
```

If Metal.jl passes smoke testing:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
RUN_METAL_PREFILTER=1 METAL_PREFILTER_N=4000000 \
  RUN_SOAK=1 JULIA_NUM_THREADS=auto bash tools/macos_scout/run_compute_campaign.sh
```

The CPU Julia simulation is the authoritative evidence path. Metal output can
rank or prefilter candidates, then CPU reranking decides whether anything is
worth promoting.

Promotion target:

```text
Candidate survives seed A and seed B
  and disaster_rate = 0 under bounded scout
  and legal_shape_ok = true
  and min_insurance_ratio >= 1
  and no fixed passive-return promise
  and payout, burn, or treasury flow is sourced from realized protocol activity
```

The result can become a mechanism note only after the replay script and proof
target exist.

## Track B: Stateful Disaster And Fuzz Campaigns

Use the Mac for a deep acceptance/stateful fuzz pass:

```bash
python3 tools/acceptance_tcb_fuzz_campaign.py --help
python3 tools/acceptance_tcb_fuzz_campaign.py --gate-lane deep --stateful-exploration
```

If dependencies are missing, install only normal dev tooling from the repo's
requirements files. Do not skip the campaign silently. If the campaign fails,
preserve the failing receipt under `internal/` and promote the smallest public
regression test.

High-priority public lanes to inspect after the campaign:

```bash
python3 tools/dex_engine_sequence_grammar_fuzz.py --format json
python3 tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py --format json
python3 tools/dex_engine_settlement_sequence_grammar_fuzz.py --format json
python3 tools/route_certificate_sequence_grammar_fuzz.py --format json
python3 tools/settlement_attestation_sequence_grammar_fuzz.py --attestation-mode policy --format json
```

Promote only minimized, deterministic witnesses. A fuzz timeout is inconclusive,
and a passing fuzz campaign is bounded evidence.

## Track C: Proof Market And Proof-Mining Hardening

Spend remaining CPU on proof-market boundary checks. Focus on cases where a
seller could get paid for a proof that is copied, vacuous, weakly bound, or
unreviewed.

Run the existing proof-mining and verifier tests first:

```bash
python3 -m pytest -q \
  tests/core/test_proof_mining_manager.py \
  tests/core/test_proof_mining_claimability_gate.py \
  tests/tools/test_permissionless_solver_proof_mining_claim.py \
  tests/integration/test_proof_mining_claimability.py \
  tests/integration/test_proof_verifier.py \
  tests/test_zenoproof_reward_payout_replay.py
```

Then add public regression tests for any missing boundary:

- vacuous proof cannot pass unless the claimed theorem, assumptions, artifact
  hash, verifier root, and public inputs are bound;
- copied proof cannot earn a second reward for the same canonical
  `proposal_hash`;
- human signoff, if required by a market policy, is bound into the acceptance
  receipt before payment;
- proof quality rating cannot alter the safety gate and cannot override verifier
  rejection;
- reward pool balance drift blocks payout;
- buyer-visible proof disclosure happens only after the escrow or reveal
  condition that the policy specifies.

Pair any new Python regression with a Lean or SMT proof obligation when the
claim is simple enough to state. Good Lean targets include:

```text
ProofRewardNoDoubleSpend:
  same canonical proposal_hash -> at most one rewarded claim

VacuousProofGate:
  accepted_reward -> verifier_accepts artifact and theorem_binding_matches

EscrowRevealSafety:
  unpaid buyer view -> no transferable full proof payload is released
```

The theorem names are suggestions. The agent may choose better statements after
reading the code.

## Track D: Formal Follow-through

Run these checks before promoting any math or proof-market artifact:

```bash
cd lean-mathlib
lake env lean Proofs/PerpLiveRiskParamMonotonicity.lean
lake env lean Proofs/FIREBudgetSafety.lean
lake env lean Proofs/NoRisklessYieldLaw.lean
lake env lean Proofs/ZenoDEXDisasterSchemaInstantiations.lean
```

If a proposed theorem requires new formalization, add a narrow theorem file
under `lean-mathlib/Proofs/` and keep the statement honest. A checked theorem
with strong assumptions is useful; an impressive theorem whose premises do not
map to runtime gates is low value.

## Required Deliverables

Return a result packet in this shape:

```json
{
  "schema": "rlm-subagent-result/v1",
  "task_id": "macos-compute-max-20260508",
  "turn": 1,
  "status": "ok|blocked|failed",
  "summary": "One paragraph maximum.",
  "claims": [
    {
      "claim": "Specific checked claim.",
      "confidence": 0.0,
      "evidence": ["path/to/report.md", "command output summary"],
      "risk_if_wrong": "low|medium|high"
    }
  ],
  "issues": [
    {
      "severity": "blocker|warning|nit",
      "what": "Problem found.",
      "why": "Why it matters.",
      "how_to_verify": "Command or check.",
      "fix": "Minimal fix."
    }
  ],
  "artifacts_added": [
    {
      "kind": "report|test|proof|script",
      "summary": "What changed.",
      "path": "repo/path"
    }
  ]
}
```

Also commit and push only reviewed public improvements:

```bash
git add docs/macos_scout tools/macos_scout tests src lean-mathlib docs/claims_registry.yaml
git status --short
git commit -m "Record MacOS compute campaign findings"
git push
```

Scope `git add` further if unrelated dirty files exist. Never use `git add -A`
in a dirty checkout.
