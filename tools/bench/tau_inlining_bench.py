#!/usr/bin/env python3
"""
Tau Inlining Overhead Test

Test how definition inlining affects execution time.
"""

import subprocess
import time
import tempfile
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TAU_BIN = ROOT / "external" / "tau-lang" / "build-Release" / "tau"


def run_tau_repl(repl_input: str, timeout_s: float = 30.0) -> tuple[int, str, str, float]:
    """Run tau with REPL input."""
    start = time.monotonic()
    try:
        proc = subprocess.run(
            [str(TAU_BIN), "--charvar", "false", "--severity", "error"],
            input=repl_input,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        elapsed = time.monotonic() - start
        return proc.returncode, proc.stdout, proc.stderr, elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return -1, "", "TIMEOUT", elapsed


def measure_inline_expansion():
    """Measure how inlining affects formula size and execution time."""
    print("\n=== Inline Expansion Test ===")

    # Formula with nested definitions (similar to settlement spec structure)
    # Level 1: simple def
    # Level 2: def using level 1
    # Level 3: def using level 2
    # etc.

    test_cases = [
        # (name, inlined_formula, num_inputs)
        ("level_0", "(i1[t]:bv[16] <= i2[t]:bv[16])", 2),
        ("level_1", "((i1[t]:bv[16] <= i2[t]:bv[16]) && (i2[t]:bv[16] <= i3[t]:bv[16]))", 3),
        ("level_2", "((i1[t]:bv[16] <= i2[t]:bv[16]) && (i2[t]:bv[16] <= i3[t]:bv[16]) && (i3[t]:bv[16] <= i4[t]:bv[16]))", 4),
        ("level_3", """
            ((i1[t]:bv[16] <= i2[t]:bv[16]) &&
             (i2[t]:bv[16] <= i3[t]:bv[16]) &&
             (i3[t]:bv[16] <= i4[t]:bv[16]) &&
             (i4[t]:bv[16] <= i5[t]:bv[16]) &&
             ((i1[t]:bv[16] = i2[t]:bv[16]) -> (i3[t]:bv[16] >= i4[t]:bv[16])))
        """, 5),
        ("level_4_nested_impl", """
            ((i1[t]:bv[16] <= i2[t]:bv[16]) ->
             ((i2[t]:bv[16] <= i3[t]:bv[16]) ->
              ((i3[t]:bv[16] <= i4[t]:bv[16]) ->
               ((i4[t]:bv[16] <= i5[t]:bv[16]) ->
                (i5[t]:bv[16] <= i6[t]:bv[16])))))
        """, 6),
        ("settlement_like_simple", """
            ((i1[t]:bv[16] < i2[t]:bv[16]) && (i2[t]:bv[16] < i3[t]:bv[16]) && (i3[t]:bv[16] < i4[t]:bv[16]) &&
             ((i5[t]:bv[16] <= i6[t]:bv[16]) && (i6[t]:bv[16] <= i7[t]:bv[16])) &&
             (i8[t]:bv[16] * (i9[t]:bv[16] + i10[t]:bv[16]) <= i10[t]:bv[16] * i11[t]:bv[16]))
        """, 11),
    ]

    results = []
    for name, formula, num_inputs in test_cases:
        # Clean up formula
        formula = " ".join(formula.split())

        # Build input declarations
        input_decls = "\n".join([f"i{i} : bv[16] = in console" for i in range(1, num_inputs + 1)])
        input_values = "\n".join([str(i * 100) for i in range(1, num_inputs + 1)])

        repl_input = f"""
{input_decls}
o1 : sbf = out console
r (o1[t]:sbf = 1:sbf <-> {formula})
{input_values}
q
"""
        rc, out, err, elapsed = run_tau_repl(repl_input, timeout_s=60.0)
        status = "PASS" if rc == 0 else "TIMEOUT" if "TIMEOUT" in err else "FAIL"

        formula_size = len(formula)
        print(f"  {name}: {elapsed:.2f}s - {status} (formula size: {formula_size} chars, {num_inputs} inputs)")
        results.append((name, elapsed, status, formula_size, num_inputs))

    return results


def test_token_ok_pattern():
    """Test the token_ok pattern from settlement spec (the most complex part)."""
    print("\n=== token_ok Pattern Test ===")

    # This is the fully inlined token_ok pattern from settlement_v1
    # Simplified version with fewer inputs
    formula = """(
        (((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 0:sbf)) ||
         ((i1[t]:sbf = 0:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 0:sbf)) ||
         ((i1[t]:sbf = 0:sbf) && (i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 1:sbf))) &&
        ((i1[t]:sbf = 1:sbf ->
            ((i4[t]:bv[16] > { #x0000 }:bv[16]) || ((i4[t]:bv[16] = { #x0000 }:bv[16]) && (i5[t]:bv[16] > { #x0000 }:bv[16])))) ||
         (i2[t]:sbf = 1:sbf ->
            ((i4[t]:bv[16] > { #x0000 }:bv[16]) || ((i4[t]:bv[16] = { #x0000 }:bv[16]) && (i5[t]:bv[16] > { #x0000 }:bv[16])))) ||
         (i3[t]:sbf = 1:sbf ->
            ((i4[t]:bv[16] > { #x0000 }:bv[16]) || ((i4[t]:bv[16] = { #x0000 }:bv[16]) && (i5[t]:bv[16] > { #x0000 }:bv[16])))))
    )"""

    formula = " ".join(formula.split())

    repl_input = f"""
i1 : sbf = in console
i2 : sbf = in console
i3 : sbf = in console
i4 : bv[16] = in console
i5 : bv[16] = in console
o1 : sbf = out console
r (o1[t]:sbf = 1:sbf <-> {formula})
1
0
0
100
200
q
"""
    rc, out, err, elapsed = run_tau_repl(repl_input, timeout_s=60.0)
    status = "PASS" if rc == 0 else "TIMEOUT" if "TIMEOUT" in err else "FAIL"
    print(f"  token_ok simplified: {elapsed:.2f}s - {status} (formula size: {len(formula)} chars)")

    return elapsed, status


def test_add_32_pattern():
    """Test the add_32 pattern (32-bit addition via hi/lo limbs)."""
    print("\n=== add_32 Pattern Test ===")

    # add_32 inlined
    formula = """(
        (i5[t]:bv[16] = (i3[t]:bv[16] + i4[t]:bv[16])) &&
        (((i5[t]:bv[16] < i3[t]:bv[16]) -> (i6[t]:bv[16] = (i1[t]:bv[16] + i2[t]:bv[16] + { #x0001 }:bv[16]))) &&
         (!(i5[t]:bv[16] < i3[t]:bv[16]) -> (i6[t]:bv[16] = (i1[t]:bv[16] + i2[t]:bv[16]))))
    )"""

    formula = " ".join(formula.split())

    repl_input = f"""
i1 : bv[16] = in console
i2 : bv[16] = in console
i3 : bv[16] = in console
i4 : bv[16] = in console
i5 : bv[16] = in console
i6 : bv[16] = in console
o1 : sbf = out console
r (o1[t]:sbf = 1:sbf <-> {formula})
0
0
100
200
300
0
q
"""
    rc, out, err, elapsed = run_tau_repl(repl_input, timeout_s=60.0)
    status = "PASS" if rc == 0 else "TIMEOUT" if "TIMEOUT" in err else "FAIL"
    print(f"  add_32: {elapsed:.2f}s - {status} (formula size: {len(formula)} chars)")

    return elapsed, status


def test_many_conjunctions():
    """Test how the number of conjunctions affects performance."""
    print("\n=== Many Conjunctions Test ===")

    results = []
    for n_conj in [5, 10, 15, 20, 30, 40, 50]:
        # Build formula with n_conj conjunctions
        parts = [f"(i{i}[t]:bv[16] <= i{i+1}[t]:bv[16])" for i in range(1, n_conj + 1)]
        formula = " && ".join(parts)
        num_inputs = n_conj + 1

        input_decls = "\n".join([f"i{i} : bv[16] = in console" for i in range(1, num_inputs + 1)])
        input_values = "\n".join([str(i * 10) for i in range(1, num_inputs + 1)])

        repl_input = f"""
{input_decls}
o1 : sbf = out console
r (o1[t]:sbf = 1:sbf <-> ({formula}))
{input_values}
q
"""
        rc, out, err, elapsed = run_tau_repl(repl_input, timeout_s=120.0)
        status = "PASS" if rc == 0 else "TIMEOUT" if "TIMEOUT" in err else "FAIL"
        print(f"  {n_conj:2d} conjunctions ({num_inputs:2d} inputs): {elapsed:.2f}s - {status}")
        results.append((n_conj, elapsed, status))

        if status == "TIMEOUT":
            break

    return results


def test_implications_vs_disjunctions():
    """Test if implications are slower than equivalent disjunctions."""
    print("\n=== Implications vs Disjunctions ===")

    # Implication form: p -> q
    impl_formula = "((i1[t]:bv[16] <= i2[t]:bv[16]) -> (i3[t]:bv[16] <= i4[t]:bv[16]))"

    # Equivalent disjunction form: !p || q
    disj_formula = "(!(i1[t]:bv[16] <= i2[t]:bv[16]) || (i3[t]:bv[16] <= i4[t]:bv[16]))"

    for name, formula in [("implication", impl_formula), ("disjunction", disj_formula)]:
        repl_input = f"""
i1 : bv[16] = in console
i2 : bv[16] = in console
i3 : bv[16] = in console
i4 : bv[16] = in console
o1 : sbf = out console
r (o1[t]:sbf = 1:sbf <-> {formula})
100
200
150
250
q
"""
        rc, out, err, elapsed = run_tau_repl(repl_input, timeout_s=30.0)
        status = "PASS" if rc == 0 else "TIMEOUT" if "TIMEOUT" in err else "FAIL"
        print(f"  {name}: {elapsed:.2f}s - {status}")


def main():
    print("=" * 60)
    print("TAU INLINING OVERHEAD TEST")
    print("=" * 60)

    if not TAU_BIN.exists():
        print(f"ERROR: Tau binary not found at {TAU_BIN}")
        return 1

    measure_inline_expansion()
    test_token_ok_pattern()
    test_add_32_pattern()
    test_many_conjunctions()
    test_implications_vs_disjunctions()

    return 0


if __name__ == "__main__":
    exit(main())
