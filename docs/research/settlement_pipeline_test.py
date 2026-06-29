#!/usr/bin/env python3
"""Phase 7A: End-to-End Settlement Pipeline Empirical Tests.

This file provides deterministic empirical verification of the Lean-proven
settlement pipeline theorems in `SettlementPipeline.lean`.

LEAN-PROVEN (in SettlementPipeline.lean):
1. foldSettlements_netFlow: Δ(fold(settlements)) = sum(Δ(s) for s in settlements)
2. foldSettlements_balanced: if all settlements are balanced, fold is balanced
3. foldSettlements_safe: if all settlements are safe (Δ >= 0), fold is safe
4. pipeline_conservation: if all swaps produce balanced settlements, batch is balanced
5. pipeline_non_negativity: if all swaps produce safe settlements, batch is safe
6. SwapChain.K_non_decreasing: K is non-decreasing across a swap chain
7. end_to_end_pipeline: both conservation and non-negativity hold together

EMPIRICAL (this file):
- Concrete CPMM swap batch conservation check
- Concrete CPMM swap batch non-negativity check
- K-preservation across multi-swap chains
- Delta aggregation additivity
- Pipeline determinism (same batch -> same settlement)

Non-claims:
- Intent validation rules are external hypotheses (not tested here).
- Batch clearing objective (A,B optimality) is not tested here.
- Fee handling uses the zero-fee model.
- Multi-pool routing is not tested here.
- LP operations are not tested here.
- Permutation invariance is not tested here (open gap in Lean).

Determinism: All tests use fixed seeds.
"""

import math
import random
from typing import List, Tuple
from dataclasses import dataclass


@dataclass(frozen=True)
class CPMMState:
    reserve_in: int
    reserve_out: int

    @property
    def k(self) -> int:
        return self.reserve_in * self.reserve_out


@dataclass(frozen=True)
class Settlement:
    dx: int  # change in input reserve
    dy: int  # change in output reserve

    @property
    def net_flow(self) -> int:
        return self.dx + self.dy

    @property
    def is_balanced(self) -> bool:
        return self.net_flow == 0

    @property
    def is_safe(self) -> bool:
        return self.net_flow >= 0


def swap_output_zero_fee(reserve_in: int, reserve_out: int, amount_in: int) -> int:
    """CPMM swap output (zero fee): out = (rout * ain) / (rin + ain)."""
    return (reserve_out * amount_in) // (reserve_in + amount_in)


def valid_swap(state: CPMMState, amount_in: int) -> Tuple[CPMMState, Settlement]:
    """Execute a valid CPMM swap, returning new state and settlement."""
    amount_out = swap_output_zero_fee(state.reserve_in, state.reserve_out, amount_in)
    new_state = CPMMState(state.reserve_in + amount_in, state.reserve_out - amount_out)
    settlement = Settlement(amount_in, -amount_out)
    return new_state, settlement


def fold_settlements(settlements: List[Settlement]) -> Settlement:
    """Fold a list of settlements into a single composed settlement."""
    total_dx = sum(s.dx for s in settlements)
    total_dy = sum(s.dy for s in settlements)
    return Settlement(total_dx, total_dy)


def batch_to_settlements(state: CPMMState, amounts: List[int]) -> List[Settlement]:
    """Convert a batch of swap amounts to settlements (all from same initial state)."""
    settlements = []
    for amt in amounts:
        _, settlement = valid_swap(state, amt)
        settlements.append(settlement)
    return settlements


def batch_settlement(state: CPMMState, amounts: List[int]) -> Settlement:
    """Compute the batch settlement from a list of swap amounts."""
    return fold_settlements(batch_to_settlements(state, amounts))


def swap_chain_k(state: CPMMState, amounts: List[int]) -> List[int]:
    """Execute a chain of swaps, returning K values at each step."""
    k_values = [state.k]
    s = state
    for amt in amounts:
        s, _ = valid_swap(s, amt)
        k_values.append(s.k)
    return k_values


# ---------------------------------------------------------------------------
# Test 1: Delta aggregation additivity
# ---------------------------------------------------------------------------

def test_delta_aggregation_additivity() -> None:
    """The net flow of a batch equals the sum of individual net flows.

    This is the empirical counterpart of foldSettlements_netFlow (Lean PROVEN).
    """
    rng = random.Random(20260629)
    for _ in range(200):
        rin = rng.randint(1000, 10000)
        rout = rng.randint(1000, 10000)
        state = CPMMState(rin, rout)
        n = rng.randint(1, 10)
        amounts = [rng.randint(10, min(100, rin // 10)) for _ in range(n)]
        settlements = batch_to_settlements(state, amounts)
        batch = fold_settlements(settlements)
        individual_sum = sum(s.net_flow for s in settlements)
        assert batch.net_flow == individual_sum, (
            f"Net flow mismatch: batch={batch.net_flow}, sum={individual_sum}")
    print(f"PASS: test_delta_aggregation_additivity (200 random batches)")


# ---------------------------------------------------------------------------
# Test 2: Pipeline conservation (balanced composition)
# ---------------------------------------------------------------------------

def test_pipeline_conservation() -> None:
    """If every swap produces a balanced settlement, the batch is balanced.

    A balanced settlement has dx + dy = 0, i.e., amount_in = amount_out.
    For CPMM, amount_out < amount_in always (due to slippage), so no
    real CPMM swap is balanced. We test with synthetic balanced settlements.

    This is the empirical counterpart of pipeline_conservation (Lean PROVEN).
    """
    rng = random.Random(20260629)
    for _ in range(200):
        n = rng.randint(1, 10)
        # Create synthetic balanced settlements (dx = -dy)
        settlements = []
        for _ in range(n):
            amt = rng.randint(10, 1000)
            settlements.append(Settlement(amt, -amt))
        batch = fold_settlements(settlements)
        assert batch.is_balanced, (
            f"Batch should be balanced: net_flow={batch.net_flow}")
        assert all(s.is_balanced for s in settlements), (
            "All individual settlements should be balanced")
    print(f"PASS: test_pipeline_conservation (200 synthetic balanced batches)")


# ---------------------------------------------------------------------------
# Test 3: Pipeline non-negativity (safe scalar flow)
# ---------------------------------------------------------------------------

def test_pipeline_non_negativity() -> None:
    """If every swap has amount_in >= amount_out (safe), the batch is safe.

    For CPMM with zero fee, amount_out = (rout * ain) / (rin + ain).
    When rout <= rin (balanced or input-heavy pool), amount_out <= ain
    since rout/(rin+ain) < 1. When rout >> rin, amount_out can exceed ain,
    making the swap unsafe (Δ < 0). The Lean theorem is conditional on
    amount_in >= amount_out, so we test with balanced pools where this holds.

    This is the empirical counterpart of pipeline_non_negativity (Lean PROVEN,
    conditional on each swap being safe).
    """
    rng = random.Random(20260629)
    for _ in range(200):
        rin = rng.randint(1000, 10000)
        rout = rng.randint(1000, rin)  # rout <= rin ensures amount_out <= ain
        state = CPMMState(rin, rout)
        n = rng.randint(1, 10)
        amounts = [rng.randint(10, min(100, rin // 10)) for _ in range(n)]
        settlements = batch_to_settlements(state, amounts)
        # Verify each swap is individually safe
        for s in settlements:
            assert s.is_safe, (
                f"Individual swap should be safe: dx={s.dx}, dy={s.dy}, "
                f"net_flow={s.net_flow}")
        batch = fold_settlements(settlements)
        assert batch.is_safe, (
            f"Batch should be safe: net_flow={batch.net_flow}")
    print(f"PASS: test_pipeline_non_negativity (200 balanced-pool CPMM batches)")


# ---------------------------------------------------------------------------
# Test 4: K-preservation across swap chains
# ---------------------------------------------------------------------------

def test_k_preservation_chain() -> None:
    """K is non-decreasing across a chain of valid CPMM swaps.

    This is the empirical counterpart of SwapChain.K_non_decreasing (Lean PROVEN).
    """
    rng = random.Random(20260629)
    for _ in range(200):
        rin = rng.randint(1000, 10000)
        rout = rng.randint(1000, 10000)
        state = CPMMState(rin, rout)
        n = rng.randint(1, 10)
        amounts = [rng.randint(10, min(100, rin // 10)) for _ in range(n)]
        k_values = swap_chain_k(state, amounts)
        for i in range(1, len(k_values)):
            assert k_values[i] >= k_values[i - 1], (
                f"K decreased at step {i}: {k_values[i]} < {k_values[i-1]}, "
                f"chain K values: {k_values}")
    print(f"PASS: test_k_preservation_chain (200 multi-swap chains)")


# ---------------------------------------------------------------------------
# Test 5: End-to-end pipeline (conservation + non-negativity)
# ---------------------------------------------------------------------------

def test_end_to_end_pipeline() -> None:
    """The end-to-end pipeline: safe swaps produce a safe batch settlement.

    For CPMM, every swap is safe (amount_in >= amount_out), so the batch
    is safe. Conservation (balanced) does NOT hold for real CPMM swaps
    (amount_out < amount_in due to slippage), so we only check non-negativity
    for real swaps and conservation for synthetic balanced swaps.

    This is the empirical counterpart of end_to_end_pipeline (Lean PROVEN).
    """
    rng = random.Random(20260629)
    # Real CPMM swaps: safe but not balanced (use balanced pools)
    for _ in range(200):
        rin = rng.randint(1000, 10000)
        rout = rng.randint(1000, rin)  # balanced pool for safety
        state = CPMMState(rin, rout)
        n = rng.randint(1, 10)
        amounts = [rng.randint(10, min(100, rin // 10)) for _ in range(n)]
        batch = batch_settlement(state, amounts)
        assert batch.is_safe, (
            f"Real CPMM batch should be safe: net_flow={batch.net_flow}")
    # Synthetic balanced swaps: both safe and balanced
    for _ in range(200):
        n = rng.randint(1, 10)
        settlements = [Settlement(rng.randint(10, 1000), -rng.randint(10, 1000))
                       for _ in range(n)]
        # Make them balanced
        settlements = [Settlement(s.dx, -s.dx) for s in settlements]
        batch = fold_settlements(settlements)
        assert batch.is_balanced and batch.is_safe, (
            f"Synthetic balanced batch should be both balanced and safe")
    print(f"PASS: test_end_to_end_pipeline (400 batches: 200 real + 200 synthetic)")


# ---------------------------------------------------------------------------
# Test 6: Pipeline determinism (same batch -> same settlement)
# ---------------------------------------------------------------------------

def test_pipeline_determinism() -> None:
    """The same batch of amounts always produces the same settlement.

    This is a determinism check: the pipeline is a pure function of inputs.
    """
    rng = random.Random(20260629)
    for _ in range(100):
        rin = rng.randint(1000, 10000)
        rout = rng.randint(1000, rin)  # balanced pool
        state = CPMMState(rin, rout)
        n = rng.randint(1, 10)
        amounts = [rng.randint(10, min(100, rin // 10)) for _ in range(n)]
        batch1 = batch_settlement(state, amounts)
        batch2 = batch_settlement(state, amounts)
        assert batch1 == batch2, (
            f"Same batch should produce same settlement: {batch1} != {batch2}")
    print(f"PASS: test_pipeline_determinism (100 determinism checks)")


# ---------------------------------------------------------------------------
# Test 7: Concrete K-preservation witnesses (matching Lean witnesses)
# ---------------------------------------------------------------------------

def test_concrete_k_witnesses() -> None:
    """Concrete K-preservation witnesses matching the Lean proofs.

    witness_chain_K_single: s=(1000,1000), swap 100
      amount_out = (1000*100)/1100 = 90
      new K = 1100 * 910 = 1,001,000 >= 1,000,000

    witness_chain_K_double: s=(1000,1000), swaps 100, 50
      swap1: out=90, s1=(1100,910), K1=1,001,000
      swap2: out=(910*50)/1150=39, s2=(1150,871), K2=1,001,650
    """
    # Single swap
    s = CPMMState(1000, 1000)
    s1, _ = valid_swap(s, 100)
    assert s1.k >= s.k, f"Single swap K: {s1.k} < {s.k}"
    assert s1.reserve_in == 1100 and s1.reserve_out == 910, (
        f"Single swap state: {s1}")
    assert s1.k == 1001000, f"Single swap K: {s1.k} != 1001000"

    # Double swap
    s2, _ = valid_swap(s1, 50)
    assert s2.k >= s1.k, f"Double swap K: {s2.k} < {s1.k}"
    assert s2.k >= s.k, f"Double swap K chain: {s2.k} < {s.k}"
    expected_out2 = (910 * 50) // 1150
    assert s2.reserve_out == 910 - expected_out2, (
        f"Double swap out: {s2.reserve_out} != {910 - expected_out2}")

    print(f"PASS: test_concrete_k_witnesses "
          f"(single: K={s1.k}, double: K={s2.k})")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    test_delta_aggregation_additivity()
    test_pipeline_conservation()
    test_pipeline_non_negativity()
    test_k_preservation_chain()
    test_end_to_end_pipeline()
    test_pipeline_determinism()
    test_concrete_k_witnesses()
    print("\nAll Phase 7A settlement pipeline tests passed.")
    print("Lean-proven (in SettlementPipeline.lean):")
    print("  1. foldSettlements_netFlow (delta additivity)")
    print("  2. foldSettlements_balanced (conservation composition)")
    print("  3. foldSettlements_safe (non-negativity composition)")
    print("  4. pipeline_conservation (batch conservation)")
    print("  5. pipeline_non_negativity (batch non-negativity)")
    print("  6. SwapChain.K_non_decreasing (K-preservation chain)")
    print("  7. end_to_end_pipeline (conservation + non-negativity)")
    print("Empirical (this file):")
    print("  8. Delta aggregation additivity [empirical]")
    print("  9. Pipeline conservation [empirical, synthetic balanced]")
    print("  10. Pipeline non-negativity [empirical, real CPMM]")
    print("  11. K-preservation chain [empirical]")
    print("  12. End-to-end pipeline [empirical]")
    print("  13. Pipeline determinism [empirical]")
    print("  14. Concrete K witnesses [empirical, matches Lean]")
