# Production Implementation Guide: Multi-Pool Batch Clearing

Synthesizes 33 research breakthroughs from `run_4b50f1194600478f` (Phase 1) and
`run_0407b7a55a80412c` (Phase 2) into actionable implementation recommendations
for ZenoDEX production.

## Summary

Three components need production changes:

1. **Algorithm**: Ternary search DP with adaptive window (22x speedup, formally verified supporting lemmas including discrete concavity implies unimodal global maximum; the ternary search algorithm narrowing invariant and Lipschitz window sufficiency remain empirically validated, next proof targets; empirical validation for the adaptive-window implementation)
2. **Mechanism**: Commit-reveal for both `amount_in` AND `min_out` (100% single-user SP, formally verified; eliminates adaptive bid-parameter misreporting and the modeled sandwich vector; inclusion, censorship, reveal-withholding, and batch-boundary games are non-claims; does NOT prevent precommit collusion, 42.1% violation rate via off-protocol side payments)
3. **Collusion mitigation**: Min_out cap (0.0% precommit collusion violation rate in Phase 2 randomized replay, zero welfare impact; formally proven numeric witness demonstrating precommit collusion profitability for the modeled clearing rule; non-claim: universal mitigation beyond the tested replay model is not proven)

The algorithm's supporting lemmas (compressed-state sufficiency, concavity, floor proximity, discrete concavity implies unimodal global maximum) are formally verified in Lean 4; the ternary search algorithm narrowing invariant and Lipschitz window sufficiency remain empirically validated (next proof targets). The mechanism's single-user SP is formally verified in Lean 4; group SP was falsified by the precommit sacrifice attack (breakthrough 28). Phase 2 formally proved a constructive numeric witness demonstrating precommit collusion profitability for the modeled (A,B) clearing rule (concrete surplus and side-payment inequalities) and identified the min_out cap as the strongest mitigation.

---

## 1. Algorithm: Ternary Search DP

### Problem

The 2-pool batch clearing DP has O(D^2) inner loop complexity, making it
impractical for n > 10 users at D = 100 granularity.

### Solution

Replace the O(D) inner loop scan with O(1) ternary search, enabled by
the concavity of the CPMM split function. The adaptive window
`W = ceil(1/L_min)` limits the search range.

### Key Results

| Metric | Baseline | Optimized | Improvement |
|--------|----------|-----------|-------------|
| Inner loop | O(D) | O(1) | D-fold |
| State space | O(D^2) | O(D^1.5) | 200-1000x |
| Total speedup | 1x | 22x | 22x |
| Exactness | 100% | 96% empirical | 4% empirical gap (algorithm narrowing empirical; key unimodality property Lean-proven) |

### Formal Verification

- `CompressedStateSubsetDP.lean` (331 lines): DP pruning rule correctness
- `TernarySearchExactness.lean` (249 lines, Phase 2): Discrete concavity implies unimodal global maximum (key property for ternary search; algorithm itself not formalized)
- `WindowBound.lean` (128 lines): Floor proximity lemma
- `StrongConcavityWindowBound.lean` (136 lines): Quadratic decay tightness

All compile with zero errors, zero warnings, zero sorries.

### Implementation

```python
def compute_window(L_min: float) -> int:
    """Adaptive window: W = ceil(1/L_min).

    L_min is the minimum Lipschitz constant over all reachable states.
    For CPMM: L = y * (1 - fee/10000) / x.
    """
    return max(1, math.ceil(1.0 / L_min))

def ternary_search_dp(pool0, pool1, intents, D):
    """O(n * D * W) instead of O(n * D^2).

    For each state (k, a, y0r), find the optimal split b via
    ternary search within the window [b* - W, b* + W].
    """
    W = compute_window(min_lipschitz(pool0, pool1))
    # ... DP with ternary search in window of size W ...
```

### Production Parameters

- D = 100 (granularity): W = 1-3 for typical pools
- D = 1000 (high granularity): W = 1-3 (scales with L, not D)
- n = 20 (max users): 22x speedup makes this practical

---

## 2. Mechanism: Commit-Reveal for Both Parameters

### Problem

The baseline (A,B) optimal ordering mechanism has a 35.7% strategyproofness
violation rate. Users can profit by inflating `amount_in` (the inflate attack)
or manipulating `min_out` to change ordering.

### Solution

Commit-reveal for BOTH `amount_in` AND `min_out` before the batch. With both
parameters binding, there are no adaptive strategic parameters. The Lean result
covers single-user adaptive misreporting under binding commitment. It eliminates
adaptive bid-parameter misreporting and the modeled sandwich vector (inclusion,
censorship, reveal-withholding, and batch-boundary games are non-claims) but
does NOT prevent precommit collusion via off-protocol side payments.

### Key Results

| Mechanism | Single SP | Group SP | Welfare | Budget |
|-----------|-----------|----------|---------|--------|
| **CR (both params) + (A,B)** | **100%** | **57.9%** | **100%** | **0** |
| CR (amount_in) + fixed order | 100% | 77.5% (trial-level SP) | 99.84% | 0 |
| Burn 50% + CR | 100% | 100% | 0.2% | 1275.3 |
| (A,B) baseline | 50.9% | ~50% | 100% | 0 |

Note: CR (both params) group SP = 57.9% = 100% - 42.1% precommit collusion rate.
The 42.1% violation comes from the precommit sacrifice attack (breakthrough 28),
where A precommits high min_out, B precommits normally, and they split gains
off-protocol. Commit-reveal alone, in this off-protocol side-payment model, does not prevent precommit collusion.

### Critical Finding: Two Attack Surfaces

**Adaptive attacks (PREVENTED by CR both params):**
- MEV: changing bids after seeing other bids in the mempool
- Sandwich: front-running and back-running user transactions
- These are the main practical attack vectors in DeFi

**Precommit collusion (NOT prevented by CR both params):**
- A and B collude off-protocol before the commit phase
- A precommits high min_out (sacrifice), B precommits normally
- A doesn't fill, B gets better pool state
- They split gains via off-protocol side payment
- 42.1% violation rate (208/494 trials, seed=20260627)

### Formal Verification

- `CommitRevealStrategyproof.lean` (84 lines): Single-user SP for CR (amount_in)
- `CommitRevealBothParamsSP.lean` (108 lines): Single-user SP for CR (both params)

All compile with zero errors, zero warnings, zero sorries.

Note: The Lean proof proves single-user SP only. Group SP was falsified by the
precommit sacrifice attack (breakthrough 28, Codex round 1 finding 1).

### Welfare Under Pool Drift

Committing `min_out` before seeing the final pool state does NOT cause
welfare loss. At drift 0-2%, welfare ratio = 1.000 (identity check passes).
At higher drift, ratio > 1.0 (committing early actually improves welfare).
For block-to-block settlement (drift 1-5%), fill rates remain 100% for
moderate `min_out` (50-75%).

### Implementation

```solidity
// Commit phase: user submits hash commitment
function commit(bytes32 commitment) external {
    // commitment = keccak256(abi.encode(amount_in, min_out, nonce))
    commitments[msg.sender] = commitment;
}

// Reveal phase: user reveals parameters after batch closes
function reveal(uint256 amount_in, uint256 min_out, bytes32 nonce) external {
    require(keccak256(abi.encode(amount_in, min_out, nonce))
            == commitments[msg.sender], "Invalid reveal");
    // Add intent with binding amount_in and min_out
    intents.push(Intent(msg.sender, amount_in, min_out));
}

// Settlement: (A,B) optimal ordering on revealed intents
function settle() external {
    // ... batch_clear_ab with binding parameters ...
}
```

### Infrastructure Cost

Same as commit-reveal for `amount_in` only. Just add `min_out` to the hash
commitment: `hash(amount_in, min_out, nonce)`. Standard DeFi infrastructure.

---

## 3. Collusion Mitigation: Min_out Cap

### Problem

Commit-reveal for both parameters eliminates adaptive attacks but does NOT
prevent precommit collusion (42.1% violation rate, breakthrough 28). Phase 2
formally proved a constructive numeric witness: for the modeled (A,B) clearing
rule, the precommit sacrifice attack yields strictly higher group surplus than
truthful reporting, and a side payment exists making both users strictly better
off (breakthrough 33).

### Solution

The min_out cap: clamp each user's committed `min_out` to at most the expected
output for their `amount_in` at the current pool state. This prevents the
sacrificial user from committing a high `min_out` that guarantees non-execution,
eliminating the surplus that funds the side payment.

### Key Results

| Mitigation | Violation Rate (Phase 2 replay) | Welfare Impact | Verdict |
|------------|---------------|----------------|---------|
| **Min_out cap** | **0.0%** | **0.0%** | **RECOMMENDED** (Phase 2 replay model) |
| Slashing (D=100) | 9.7% | Moderate | Partial |
| Slashing (D=50) | 13.8% | Moderate | Partial |
| Batch randomization | 22.1% | Low | Insufficient |
| VCG payments | 70.2% | Negative | COUNTERPRODUCTIVE |

### Mechanism

The min_out cap works by clamping each user's committed `min_out` to at most
the expected output for their `amount_in` at the current pool state. This
prevents the sacrificial user from committing an absurdly high `min_out`
that guarantees non-execution. With `cap_factor=100`, the cap equals the
expected output, so the sacrificial user's `min_out` is clamped down to
their expected output, which in the Phase 2 replay model forces them to
fill and eliminates the collusion surplus.

### Implementation

```python
def apply_min_out_cap(intents, pool, cap_factor=100):
    """Clamp each user's min_out to at most cap_factor% of expected output.

    In the Phase 2 randomized replay model, this achieves 0.0% precommit
    collusion by preventing the sacrifice attack. The sacrificial user's
    high min_out is clamped down to the expected output, which forces them
    to fill in the tested scenarios.
    """
    for intent in intents:
        expected_out = cpmm_swap(pool.x, pool.y, intent.amount_in, pool.fee_bps)
        cap = expected_out * cap_factor // 100
        intent.min_out = min(intent.min_out, cap)
    return intents
```

In production, the cap is computed at settlement time using the pool state
at batch close. The `cap_factor=100` setting means `min_out <= expected_output`,
which in the Phase 2 replay model forces the sacrificial user to fill (their
output meets the clamped `min_out`). The `(A,B)` optimizer then prefers
orderings where both users fill, as volume maximization dominates. Non-claim:
this behavior is verified in the Phase 2 randomized replay (500 scenarios);
broader adversarial strategies or value profiles may exist that require
additional testing or formal proof.

### Formal Verification

- `PrecommitCollusionImpossibility.lean` (Phase 2): Constructive numeric witness for the modeled (A,B) clearing rule (precommit sacrifice yields higher group surplus + side payment exists)
- `impossibility_witness_test.py`: Python verification of the Lean witness values

All compile with zero errors, zero warnings, zero sorries.

---

## 4. What NOT to Use

### Falsified Mechanisms

| Mechanism | SP Rate | Why Not |
|-----------|---------|---------|
| Proper batch auction (UCP) | 43.3% | Worse than baseline |
| Posted-price TWAP | 50.5% | Manipulable |
| Fixed ordering alone | 50.4% | No SP improvement |
| VCG | Not SP | Non-monotone allocation |
| VCG as collusion mitigation | 70.2% violation | COUNTERPRODUCTIVE (Phase 2) |
| Burn 10% + CR | 73.7% | Makes collusion WORSE |
| Burn 50% + CR | 100% SP | Destroys welfare (0.2%) |

### Falsified Window Bounds

| Bound | Value | Why Not |
|-------|-------|---------|
| Global strong concavity | 130-632 | Impractical (m_min too small) |
| Local strong concavity | 130-632 | m* = m_min for CPMM |
| Floor proximity (L) | L | Correct but loose |

The empirical bound `ceil(1/L)` is the right one for production.

---

## 5. Integration Checklist

- [ ] Implement ternary search DP with adaptive window `W = ceil(1/L)`
- [ ] Implement commit-reveal for both `amount_in` AND `min_out`
- [ ] Implement min_out cap (enforce committed min_out at settlement)
- [ ] Use (A,B) optimal ordering for settlement
- [ ] Add commit/reveal phases to batch auction contract
- [ ] Test with n=20 users, D=100 granularity
- [ ] Verify 22x speedup vs baseline DP
- [ ] Verify 100% single-user SP with stress test suite
- [ ] Verify 0% precommit collusion with min_out cap (Phase 2 replay model, 500 scenarios)
- [ ] Document precommit collusion limitation without min_out cap (42.1% violation rate; constructive numeric witness proves precommit sacrifice is profitable for the modeled (A,B) clearing rule)
- [ ] Integrate Lean proofs into ESSO verification pipeline
- [ ] Run `lake env lean` on all 7 proof files (zero errors/sorries)
- [ ] Run all 27 Python scripts with fixed seeds for reproducibility

---

## 6. Evidence

### Lean Proofs (7 files, 1036 lines, all zero errors/sorries)

| File | Lines | Theorems |
|------|-------|----------|
| `CompressedStateSubsetDP.lean` | 331 | DP pruning rule correctness |
| `CommitRevealStrategyproof.lean` | 84 | Single-user SP (amount_in only) |
| `WindowBound.lean` | 128 | Floor proximity lemma |
| `CommitRevealBothParamsSP.lean` | 108 | Single-user SP (both params, scope-corrected) |
| `StrongConcavityWindowBound.lean` | 136 | Quadratic decay tightness |
| `PrecommitCollusionImpossibility.lean` | Phase 2 | Constructive numeric witness (precommit sacrifice yields higher group surplus + side payment exists for modeled (A,B) clearing rule) |
| `TernarySearchExactness.lean` | 249 | Discrete concavity implies unimodal global maximum (key property for ternary search; algorithm itself not formalized) |

### Python Scripts (27 files, all reproducible with fixed seeds)

Key scripts:
- `precommit_collusion_test.py`: Precommit sacrifice attack against CR (both params), 42.1% violation rate
- `mitigation_test.py`: 5 mitigation mechanisms tested (min_out cap, VCG, slashing, batch randomization)
- `impossibility_witness_test.py`: Python verification of Lean constructive numeric witness values
- `commit_reveal_both_params.py`: CR (both params) vs CR (amount_in) adaptive collusion test
- `collusion_resistance_test.py`: 8 mechanism variants, sacrifice attack (trial + check level)
- `welfare_drift_test.py`: Welfare under pool drift (paired counterfactual, identity check at drift=0)
- `stress_test_commit_reveal.py`: 49,200 checks, single-user SP
- `strong_concavity_parameter.py`: Theoretical vs empirical window bound
- `local_strong_concavity.py`: Local strong concavity falsification

### Research Kernel

28 atoms in `run_4b50f1194600478f` (Phase 1) + 5 atoms in `run_0407b7a55a80412c` (Phase 2),
all with evidence artifacts and SUPPORTS/REFUTES edges linking the compounding breakthroughs.
