# Checked signed-delta arithmetic refinement

This result closes the branch-arithmetic proof obligation for the handwritten
Lean model of `checked_signed_delta_v1`. It contributes to V3 W09. It does not
close Rust implementation refinement, the formal core, or any value-movement
gate.

The inspected runtime source belongs to integration base
`6c574bd6ffc86ed6a74138b5d2801a14977bc303`. The new proof and executable comparison
are retained together with this note.

## Claim and evidence

For every pair of holdings in `[0, 2^128)`, the model succeeds exactly when
`post - pre` is in `[-2^127, 2^127 - 1]`, returning that exact integer. Otherwise
it returns the signed-state-delta bounds rejection. The proof derives this from
the ordered unsigned subtraction and conversion branches; it does not assume
the desired result. The input type carries the unsigned bound.

The proof also establishes that subtraction magnitudes fit `u128` and retains
nonvacuity witnesses: zero delta at every holding, the minimum signed difference,
both neighboring overflow cases, and a small difference between large holdings.
The minimum signed value is returned directly, avoiding its unrepresentable
positive signed magnitude.

The companion executes the unchanged extracted Rust function body and constant
using installed Rust 1.90.0, and evaluates the Lean definition using installed
Lean 4.27.0. An independent Python oracle performs exact integer subtraction and
an interval check. The 121 distinct boundary pairs include 86 successes and
35 rejections. The extraction uses a minimal error/result shell and does not
execute the enclosing Rust crate.

Two semantic mutants are retained: dropping the minimum-signed special case,
and narrowing absolute holdings before subtraction. Each must fail the unchanged
Lean theorem packet. Each must also compile in its executable Lean and Rust
forms and expose its specific wrong rejection against the independent oracle.
A proof-script failure alone cannot satisfy either mutant test.

## Exact subjects

| File | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean` | `3a0b3e18a069b14c8fec4e705178a73cb1b3356d9813195e5e7c35b09cf74a4d` |
| `tests/formal/test_lean_checked_signed_delta_refinement_v1.py` | `fa58801ec020c348661c3a1b984a900cb649f02fce21751e9c84b9c613d9cc32` |
| `zk/global_settlement_abi_v1/src/global_economic_state_delta.rs` | `3d9fc36a2af91853a3add785bb1f29a6ba3fcbea111fd4689303e045e935a530` |

## Verification and independent review

From `lean-mathlib`, this focused checker passed:

```sh
lean -DwarningAsError=true Proofs/CheckedSignedDeltaRefinementV1.lean
```

From the repository root, the companion passed with **4 tests**:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q --tb=short -p no:cacheprovider tests/formal/test_lean_checked_signed_delta_refinement_v1.py
python3 -m ruff check tests/formal/test_lean_checked_signed_delta_refinement_v1.py
python3 -m mypy --cache-dir=/dev/null tests/formal/test_lean_checked_signed_delta_refinement_v1.py
```

Ruff and focused mypy passed. The companion checks all ten theorem declarations
for placeholders and prints their axiom dependencies; only the permitted
standard axioms `propext`, `Quot.sound`, and `Classical.choice` are allowed.
An initial harness run detected a toolchain-context mismatch: the version probe
ran at the repository root while compilation ran under `lean-mathlib`. Both now
use the same pinned directory; no toolchain was downloaded or changed.

An independent Astra Max source review matched all three hashes, inspected the
Rust branches and theorem strength, and found no concrete mistakes. Its review
is advisory and did not run builds. The checker results above were run by the
integrator.

## Remaining obligations

The universal theorem concerns the handwritten Lean model. The executable
comparison samples the extracted production Rust body; it is not a formal
compiler, standard-library, or Rust-language refinement proof. Alternate targets
and optimized execution were not tested. Full-crate behavior, decoding,
aggregation, canonical roots, authenticated inputs, publication and recovery
remain outside this claim. No full Lake, RISC0, remote prover or whole-program
release gate was run for this arithmetic-only result.

The next refinement work must connect these arithmetic bounds to complete
command outcomes and the deployed implementation without using sampled parity
or source hashes as a substitute for that relation.
