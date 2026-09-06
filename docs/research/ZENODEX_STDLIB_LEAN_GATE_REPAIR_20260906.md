# ZenoDEX Std-only Lean gate repair

Date: 2026-09-06

This repair closes a stale external/mathlib4 skip guard in nine existing
formal tests on base `40d6b89ec6037bea7a57316aa84a62c286be2f23`. The nine
proof subjects are classified as Std-only by the source-closure review for
that base: each file's transitive `import Proofs.*` closure contains no
Mathlib import. The excluded `test_lean_exact_in_true_key_winner.py` remains
outside this gate because its transitive closure uses Mathlib. The change
touches only test guards, one shared test helper, one control test, one
evidence producer, one packet and this note. No Lean theorem, toolchain,
runtime, dependency or production source changes, and the nine proof subjects
and `lean-mathlib/lean-toolchain` remain byte-identical to their base pins.

## Gate mechanics

The shared helper `tests/formal/lean_stdlib_gate_v1.py` reads and verifies
`lean-mathlib/lean-toolchain`, then uses the installed Lean 4.27.0 executable
from the local Elan toolchain directory. For every subject it copies the proof
into a fresh temporary source tree and emits a fresh temporary `.olean`
library. A separate consumer module checks one named theorem against an
explicit type and runs `#print axioms`. The consumer receives only the fresh
artifact through a Lean setup manifest. The inherited `LEAN_PATH` and
`LEAN_SRC_PATH` values are removed from each compiler environment.

```text
ToolchainPinned && CompilerInstalled && SourceCompiles(fresh copy)
  && ConsumerTypechecks(named theorem, explicit type)
  && Axioms(theorem) <= {propext, Classical.choice, Quot.sound}
  -> LeanStdlibReceipt
```

Compiler nonzero exits, warnings under `-DwarningAsError=true`, a non-silent
source compile, consumer stderr, the 120-second timeout, forbidden source
tokens (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `sorryAx`,
`ofReduceBool`), missing or duplicate `#print axioms` reports and unapproved
axiom dependencies fail the test and yield no receipt. An absent pinned
compiler is an explicit pytest skip and supplies no evidence; a skipped run is
never positive evidence. The uniform batch optimality test also retains its
declaration inventory and placeholder scan.

## Controls

`tests/formal/test_lean_stdlib_gate_v1.py` retains a real pinned-Lean negative
control: the binary decision proof is compiled unchanged, then a consumer with
an incompatible type must fail with a type mismatch. Parser controls reject
missing, duplicated and nonstandard `#print axioms` output. Mocked subprocess
controls cover only nonzero-exit and timeout shell handling; they do not
qualify Lean execution. The nine subject tests and the six control cases form
one fifteen-test focused command.

## Evidence packet and producer

`experiments/v3_stdlib_lean_gate_repair_v1/render_evidence.py` reuses the
existing `_render` helper from
`experiments/v3_completion_followup_v1/render_evidence.py` and writes only
`tests/evidence/test_hygiene/THV1-20260906-stdlib-lean-gate-repair-v1.json`.
The packet pins the nine proof subjects, the ten tests, the shared helper,
`lean-mathlib/lean-toolchain`, the producer, the shared renderer and this
note by SHA-256, and declares the gate's claim, boundaries and non-claims. A
render pins declared sources; it runs no compiler or test, reads no log,
writes no result file and records no outcome. Earlier packets stay unchanged.

## Commands

From the repository root:

```bash
python3 -B -m pytest -q -rs -p no:cacheprovider \
  tests/formal/test_lean_autotrader_binary_decision.py \
  tests/formal/test_lean_autotrader_decision_binding.py \
  tests/formal/test_lean_autotrader_live_release_certificate.py \
  tests/formal/test_lean_autotrader_stage_certificate.py \
  tests/formal/test_lean_exact_in_route_certificate.py \
  tests/formal/test_lean_exact_out_route_certificate.py \
  tests/formal/test_lean_settlement_price_history_certificate.py \
  tests/formal/test_lean_split_routing_staircase.py \
  tests/formal/test_lean_uniform_batch_optimality.py \
  tests/formal/test_lean_stdlib_gate_v1.py
python3 -B -m experiments.v3_stdlib_lean_gate_repair_v1.render_evidence
python3 -m ruff check experiments/v3_stdlib_lean_gate_repair_v1/render_evidence.py
python3 tools/check_test_hygiene_v1.py --json \
  --changed-file M:tests/formal/test_lean_autotrader_binary_decision.py \
  --changed-file M:tests/formal/test_lean_autotrader_decision_binding.py \
  --changed-file M:tests/formal/test_lean_autotrader_live_release_certificate.py \
  --changed-file M:tests/formal/test_lean_autotrader_stage_certificate.py \
  --changed-file M:tests/formal/test_lean_exact_in_route_certificate.py \
  --changed-file M:tests/formal/test_lean_exact_out_route_certificate.py \
  --changed-file M:tests/formal/test_lean_settlement_price_history_certificate.py \
  --changed-file M:tests/formal/test_lean_split_routing_staircase.py \
  --changed-file M:tests/formal/test_lean_uniform_batch_optimality.py \
  --changed-file A:tests/formal/lean_stdlib_gate_v1.py \
  --changed-file A:tests/formal/test_lean_stdlib_gate_v1.py
git diff --check
```

The focused command reports skips with `-rs`; a result with any skip is not
final evidence. On a host without the pinned compiler the nine subject tests
and the real wrong-type control skip visibly.

## Retained material and acceptance

Before the repair, the nine subject tests skipped with `mathlib4 checkout
missing`. The implementation worker's focused runs after the repair recorded
nine passed with zero skips, then fifteen passed with zero skips including the
controls, with the pinned compiler reporting version 4.27.0. Those logs, the
before-and-after proof hashes and an earlier result digest are retained as
review material in the wave's task directory outside the repository. They are
not committed evidence and the packet does not reference them. The independent
reviewer replay in the integration checkout recorded `15 passed in 14.25s`
with zero skips. Ruff and MyPy passed on all eleven changed Python test/helper
files, and the nine proof sources and toolchain remained byte-identical to
the captured inputs. The full Lake build and Mathlib-dependent tests were not
run for this test-gate repair.

## Non-claims

The evidence boundary is the installed Lean compiler, core and standard
library plus the source-pinned named consumers. Those compiler and library
bytes remain trusted; no compiler or library image hash is qualified. One
named theorem per subject is consumed; the gate does not establish
Mathlib-dependent closures, runtime refinement, the complete formal core,
deployment, production authority, whole-program completeness or any theorem
source change. The mocked controls qualify shell and parser handling only.
Packet rendering is not testing, proof execution or release qualification.
