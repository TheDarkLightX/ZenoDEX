from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPERIMENTS = ROOT / "experiments" / "tau_lang_optimizations"
RECOMMENDED = ROOT / "src" / "tau_specs" / "recommended"


@dataclass(frozen=True)
class TauOptimizationTraceCase:
    case_id: str
    spec_path: Path
    steps: list[dict[str, int]]
    expected: list[dict[str, int]]
    mode: str = "repl"
    timeout_s: float = 10.0
    inline_defs: bool = True
    rationale: str = ""


def _sbf_step(width: int, *, zero_indices: set[int] | None = None) -> dict[str, int]:
    zeros = zero_indices or set()
    return {f"i{idx}": (0 if idx in zeros else 1) for idx in range(1, width + 1)}


def _sbf_outputs(width: int, *, zero_indices: set[int] | None = None) -> dict[str, int]:
    zeros = zero_indices or set()
    return {f"o{idx}": (0 if idx in zeros else 1) for idx in range(1, width + 1)}


def optimization_tau_trace_cases() -> list[TauOptimizationTraceCase]:
    return [
        TauOptimizationTraceCase(
            case_id="batching_all_distinct_included_pass",
            spec_path=EXPERIMENTS / "batching_all_distinct_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Included IDs are pairwise distinct.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_all_distinct_executed_pass",
            spec_path=EXPERIMENTS / "batching_all_distinct_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Executed IDs are pairwise distinct.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_all_distinct_fail_duplicate",
            spec_path=EXPERIMENTS / "batching_all_distinct_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 2, "i4": 4}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="A duplicate ID should fail the pairwise-distinctness rail.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_left_in_right_exec_in_included_pass",
            spec_path=EXPERIMENTS / "batching_left_in_right_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1, "i6": 2, "i7": 3, "i8": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Every executed ID appears in the included set.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_left_in_right_included_in_exec_pass",
            spec_path=EXPERIMENTS / "batching_left_in_right_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1, "i6": 2, "i7": 3, "i8": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Every included ID appears in the executed set.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_sorted_exec_pass",
            spec_path=EXPERIMENTS / "batching_executed_sorted_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Executed IDs are strictly increasing.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_sorted_exec_fail_equal_adjacent",
            spec_path=EXPERIMENTS / "batching_executed_sorted_4_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 2, "i4": 4}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="Equality at any adjacent position must fail the strict-order rail.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_compact_fail_not_permutation",
            spec_path=EXPERIMENTS / "batching_v1_5_compact_single_gate.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1, "i6": 2, "i7": 3, "i8": 5}],
            expected=[{"o1": 0}],
            timeout_s=30.0,
            rationale="Executed IDs are distinct and sorted, but `5` is not in the included set and `4` is missing.",
        ),
        TauOptimizationTraceCase(
            case_id="batching_explained_diagnostic_not_permutation",
            spec_path=EXPERIMENTS / "batching_v1_5_explained.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1, "i6": 2, "i7": 3, "i8": 5}],
            expected=[{"o1": 1, "o2": 1, "o3": 0, "o4": 0, "o5": 1, "o6": 0}],
            timeout_s=30.0,
            rationale="Both sides are internally distinct and executed IDs are sorted, but the two 4-element sets differ.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_pass",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 100, "i4": 180, "i5": 1100, "i6": 1820}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="All six bv[32] values are within the `0xFFFF` safe multiplication range.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_fail_large_values",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 70000, "i2": 200000, "i3": 100, "i4": 180, "i5": 70100, "i6": 199820}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="At least one value exceeds `0xFFFF`, so the isolated safe-range guard must fail.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_pass_exact_out",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 180, "i4": 100, "i5": 1100, "i6": 1820}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Exact-out style values still satisfy the isolated safe-range policy.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_fail_large_values_exact_out",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 70000, "i2": 200000, "i3": 180, "i4": 100, "i5": 70100, "i6": 199820}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="Exact-out style large values violate the same isolated safe-range policy.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_boundary_max_pass",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 65535, "i2": 65535, "i3": 65535, "i4": 65535, "i5": 65535, "i6": 65535}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="The safe-range guard should accept values exactly at the `0xFFFF` ceiling.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_range_guard_boundary_fail_65536",
            spec_path=EXPERIMENTS / "swap_bv32_safe_range_guard_v1.tau",
            steps=[{"i1": 65535, "i2": 65535, "i3": 65535, "i4": 65535, "i5": 65535, "i6": 65536}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="The safe-range guard should fail immediately once any value crosses `0xFFFF`.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_in_proof_gate_pass",
            spec_path=RECOMMENDED / "swap_exact_in_proof_gate_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 100, "i4": 30, "i5": 1, "i6": 180, "i7": 1100, "i8": 1820, "i9": 1, "i10": 1}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="All structural swap checks pass and the external proof/binding flags are asserted.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_in_proof_gate_fail_slippage",
            spec_path=RECOMMENDED / "swap_exact_in_proof_gate_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 100, "i4": 30, "i5": 200, "i6": 180, "i7": 1100, "i8": 1820, "i9": 1, "i10": 1}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="`amount_out` is below `min_amount_out`, so the structural gate must fail.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_in_proof_gate_large_values_pass",
            spec_path=RECOMMENDED / "swap_exact_in_proof_gate_v1.tau",
            steps=[{"i1": 70000, "i2": 200000, "i3": 100, "i4": 30, "i5": 1, "i6": 180, "i7": 70100, "i8": 199820, "i9": 1, "i10": 1}],
            expected=[{"o1": 1}],
            timeout_s=15.0,
            rationale="The proof gate does not include the extra safe-range policy, so these larger values still satisfy its structure.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_out_proof_gate_pass",
            spec_path=RECOMMENDED / "swap_exact_out_proof_gate_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 180, "i4": 30, "i5": 200, "i6": 100, "i7": 1100, "i8": 1820, "i9": 1, "i10": 1}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="All structural exact-out checks pass and the proof/binding flags are asserted.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_out_proof_gate_fail_max_in",
            spec_path=RECOMMENDED / "swap_exact_out_proof_gate_v1.tau",
            steps=[{"i1": 1000, "i2": 2000, "i3": 180, "i4": 30, "i5": 99, "i6": 100, "i7": 1100, "i8": 1820, "i9": 1, "i10": 1}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="`amount_in` exceeds `max_amount_in`, so the structural exact-out gate must fail.",
        ),
        TauOptimizationTraceCase(
            case_id="swap_exact_out_proof_gate_large_values_pass",
            spec_path=RECOMMENDED / "swap_exact_out_proof_gate_v1.tau",
            steps=[{"i1": 70000, "i2": 200000, "i3": 180, "i4": 30, "i5": 200, "i6": 100, "i7": 70100, "i8": 199820, "i9": 1, "i10": 1}],
            expected=[{"o1": 1}],
            timeout_s=15.0,
            rationale="The proof gate still accepts larger exact-out values when its structural constraints hold.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_canonical_order_pass",
            spec_path=EXPERIMENTS / "settlement_canonical_order_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="The order IDs are strictly increasing.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_canonical_order_fail",
            spec_path=EXPERIMENTS / "settlement_canonical_order_v1.tau",
            steps=[{"i1": 1, "i2": 3, "i3": 2, "i4": 4}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="The third ID breaks strict increase.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_no_sandwich_pass",
            spec_path=EXPERIMENTS / "settlement_no_sandwich_aligned_v1.tau",
            steps=[{"i1": 1000, "i2": 1001, "i3": 1002}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="Prices are monotone increasing over the aligned 3-sample window.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_no_sandwich_fail_zigzag",
            spec_path=EXPERIMENTS / "settlement_no_sandwich_aligned_v1.tau",
            steps=[{"i1": 1000, "i2": 1002, "i3": 1001}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="The price path zig-zags, so the anti-sandwich monotonicity rail fails.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_stability_pass",
            spec_path=EXPERIMENTS / "settlement_price_stability_v1.tau",
            steps=[{"i1": 1001, "i2": 1002}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="The price changes by only 1, which is below the `< 0x32` threshold.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_stability_fail_large_jump",
            spec_path=EXPERIMENTS / "settlement_price_stability_v1.tau",
            steps=[{"i1": 1000, "i2": 1100}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="The price jumps by 100, which exceeds the `< 0x32` threshold.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_stability_boundary_pass_49",
            spec_path=EXPERIMENTS / "settlement_price_stability_v1.tau",
            steps=[{"i1": 1000, "i2": 1049}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="A price move of 49 is still strictly below the `< 0x32` threshold.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_stability_boundary_fail_50",
            spec_path=EXPERIMENTS / "settlement_price_stability_v1.tau",
            steps=[{"i1": 1000, "i2": 1050}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="A price move of exactly 50 should fail because the guard is strict `< 0x32`.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_envelope_pass",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_v1.tau",
            steps=[_sbf_step(24, zero_indices={2, 3, 4})],
            expected=[_sbf_outputs(8)],
            timeout_s=90.0,
            rationale="One action is selected and every admission fiber passes.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_envelope_fail_two_actions",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_v1.tau",
            steps=[_sbf_step(24, zero_indices={3, 4})],
            expected=[_sbf_outputs(8, zero_indices={1, 8})],
            timeout_s=90.0,
            rationale="Two action flags are set, so the one-hot action fiber and final admission fail.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_envelope_fail_replay",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_v1.tau",
            steps=[_sbf_step(24, zero_indices={2, 3, 4, 8})],
            expected=[_sbf_outputs(8, zero_indices={2, 8})],
            timeout_s=90.0,
            rationale="Replay freshness fails, so identity/replay and final admission fail.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_envelope_fail_quote_and_risk",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_v1.tau",
            steps=[_sbf_step(24, zero_indices={2, 3, 4, 13, 20})],
            expected=[_sbf_outputs(8, zero_indices={4, 5, 8})],
            timeout_s=90.0,
            rationale="Quote receipt and risk-budget fibers fail independently before final admission fails.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_temporal_pass",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_temporal_v1.tau",
            steps=[_sbf_step(32, zero_indices={2, 3, 4})],
            expected=[_sbf_outputs(10)],
            timeout_s=90.0,
            rationale="Base admission, node progress, and governance/oracle fibers all pass.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_temporal_fail_chain_height",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_temporal_v1.tau",
            steps=[_sbf_step(32, zero_indices={2, 3, 4, 26})],
            expected=[_sbf_outputs(10, zero_indices={8, 10})],
            timeout_s=90.0,
            rationale="Chain-height monotonicity fails the node-progress fiber and final admission.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_temporal_fail_oracle_diversity",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_temporal_v1.tau",
            steps=[_sbf_step(32, zero_indices={2, 3, 4, 30})],
            expected=[_sbf_outputs(10, zero_indices={9, 10})],
            timeout_s=90.0,
            rationale="Oracle-source diversity fails the governance/oracle fiber and final admission.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_temporal_fail_pause",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_temporal_v1.tau",
            steps=[_sbf_step(32, zero_indices={2, 3, 4, 9})],
            expected=[_sbf_outputs(10, zero_indices={10})],
            timeout_s=90.0,
            rationale="A pause blocks final admission while preserving the diagnostic sub-fiber results.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_admission_temporal_fail_two_actions",
            spec_path=EXPERIMENTS / "settlement_admission_envelope_temporal_v1.tau",
            steps=[_sbf_step(32, zero_indices={3, 4})],
            expected=[_sbf_outputs(10, zero_indices={1, 10})],
            timeout_s=90.0,
            rationale="Two action flags fail the one-hot action fiber and final temporal admission.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_module_bundle_pass",
            spec_path=EXPERIMENTS / "settlement_module_flag_bundle_v1.tau",
            steps=[{"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1}],
            expected=[{"o1": 1}],
            timeout_s=10.0,
            rationale="All module/proof/binding flags are asserted.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_module_bundle_fail_rebate_flag",
            spec_path=EXPERIMENTS / "settlement_module_flag_bundle_v1.tau",
            steps=[{"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 0, "i7": 1, "i8": 1, "i9": 1}],
            expected=[{"o1": 0}],
            timeout_s=10.0,
            rationale="The rebate submodule flag is cleared, so the bundle must fail.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_rails_pass",
            spec_path=EXPERIMENTS / "settlement_price_rails_aligned_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1000, "i6": 1001, "i7": 1002}],
            expected=[{"o1": 1}],
            mode="spec",
            timeout_s=30.0,
            rationale="Canonical ordering, monotone prices, and bounded price movement all hold.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_price_rails_fail_stability",
            spec_path=EXPERIMENTS / "settlement_price_rails_aligned_v1.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1000, "i6": 1001, "i7": 1100}],
            expected=[{"o1": 0}],
            mode="spec",
            timeout_s=30.0,
            rationale="Ordering and monotonicity hold, but the last price jump is too large.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_aligned_compact_bundle_pass",
            spec_path=EXPERIMENTS / "settlement_v5_aligned_compact_bundle.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1000, "i6": 1001, "i7": 1002, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1, "i13": 1, "i14": 1, "i15": 1, "i16": 1}],
            expected=[{"o1": 1}],
            mode="spec",
            timeout_s=30.0,
            rationale="All aligned rails and all external settlement flags pass.",
        ),
        TauOptimizationTraceCase(
            case_id="settlement_aligned_compact_bundle_fail_rebate",
            spec_path=EXPERIMENTS / "settlement_v5_aligned_compact_bundle.tau",
            steps=[{"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 1000, "i6": 1001, "i7": 1002, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1, "i13": 0, "i14": 1, "i15": 1, "i16": 1}],
            expected=[{"o1": 0}],
            mode="spec",
            timeout_s=30.0,
            rationale="All price rails pass, but the rebate flag is cleared, so the compact bundle must fail.",
        ),
    ]
