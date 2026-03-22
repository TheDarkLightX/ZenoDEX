# Autotrader Candidate Completeness Plan (2026-03-21)

## Scope
This note narrows the next optimization / candidate-completeness lane for the current autotrader decision surface on `main`.

Relevant implementation files:
- `src/integration/autotrader_decision.py`
- `src/kernels/python/strategy_candidate_set_contract_v1_adapter.py`
- `src/kernels/python/strategy_decision_kernel_v1_adapter.py`
- `lean-mathlib/Proofs/ZenoDEXAutoTraderBinaryDecision.lean`
- `lean-mathlib/Proofs/ZenoDEXAutoTraderDecisionBinding.lean`

## Current Runtime Shape
The runtime decision surface is intentionally small.

Current candidate family in `src/integration/autotrader_decision.py`:
- candidate `0`: `NO_OP`
- candidate `1`: `EMIT_COMPILED_INTENT`

Current kernel posture in `src/kernels/python/strategy_decision_kernel_v1_adapter.py`:
- `noop_key = 0`
- `emit_key = 1` iff `emit_requested and emit_admissible`
- winner is `argmax(noop_key, emit_key)` with explicit steps / key witness material

Current candidate-set contract posture in `src/kernels/python/strategy_candidate_set_contract_v1_adapter.py`:
- candidate set hash and packet shape are checked
- binding between packet, winner index, and candidate key is checked
- completeness over a broader family is not claimed

## Honest Claim Boundary
The current system can honestly claim:
- deterministic two-candidate selection
- explicit candidate-set hashing
- explicit winner key / winner index emission
- proof-backed binding for the emitted winner against the hashed set

It cannot yet honestly claim:
- completeness for a wider search family
- optimality over a multi-candidate action space
- approximation guarantees against a richer candidate generator

## Next Proof Targets
### 1. Two-candidate completeness theorem
State and prove that, under the current runtime contract, the hashed candidate set is exactly:
- `NO_OP`
- `EMIT_COMPILED_INTENT`

Needed artifacts:
- Lean theorem tying the candidate-set packet fields to the exact two constructors
- regression over `strategy_candidate_set_contract_v1_adapter.py`

### 2. Winner = argmax(key, candidates)
Strengthen the current binding lane to the canonical form:
- `winner ∈ candidates`
- `forall c in candidates, key(winner) >= key(c)`
- tie-break is explicit and replayable

Needed artifacts:
- Lean theorem over the binary decision kernel
- focused Python certificate test with packet replay

### 3. Kill-switch completeness surface
The kill-switch path needs an explicit theorem that the admissible candidate family under kill-switch is still complete for the runtime surface, not merely that the chosen winner is bound to the hashed key.

Needed artifacts:
- theorem / certificate that candidate rewriting is not occurring off-ledger
- negative regression for hashed-key mismatch

### 4. Promotion boundary for future expansion
If the candidate family grows past two elements, stop claiming completeness until one of these lands:
- exact theorem over the expanded finite candidate family
- bounded brute-force oracle over the claimed domain
- approximation theorem with explicit gap bound

## Recommended PR Order
1. `docs:` publish this candidate-completeness plan
2. `formal:` add two-candidate completeness theorem/certificate slice
3. `tests:` add replay / negative mismatch regressions for kill-switch and candidate hash binding
4. only then expand the runtime candidate family

## Negative Knowledge
Do not overclaim:
- current proofs are not global autotrader optimality proofs
- current candidate-set contract is not multi-candidate completeness evidence
- current runtime surface is binary and should be described that way in docs and proofs
