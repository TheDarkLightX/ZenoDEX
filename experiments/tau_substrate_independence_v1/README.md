# Tau substrate-independence conformance (prototype) — resilience gap #0

Turns "ZenoDEX *could* detach from Tau" into a **tested** property. Addresses the
#0 strategic gap in `internal/ZENOLEDGER_RESILIENCE_HARDENING_2026-06-18.md`
(§Substrate independence): the Tau-failure fallback was *designed*, not
*continuously exercised*. **Isolated prototype — imports the real core, wired into
nothing.**

## The principle

Tau is the *optimal* substrate, not a single point of failure. ZenoDEX must run
even if Tau **changes its rules** or **fails to launch**. That holds iff the two
things Tau provides are separable:

- **Validity (correctness)** — must be ZenoDEX's own and substrate-independent.
- **Ordering / DA / consensus** — a swappable backend (Tau preferred).

## What v1 proves (with the REAL core, 6 tests)

1. **The functional core's import graph is Tau-free** (`test_core_import_graph_is_tau_free`,
   run in a clean subprocess) — importing `src.core.batch_clearing`,
   `settlement_strong_validator`, `cpmm`, `src.state.state_root`, `balances`, `pools`
   pulls **zero** Tau modules. This is the **CI anti-bitrot guard**: it fails the
   day a Tau assumption creeps into the validity core.
2. **Validity is substrate-independent** — two distinct substrates
   (`LocalSequencerSubstrate`, `TauCheckpointSubstrate`) settling the same batch
   produce a **byte-identical real state root** (`compute_state_root`), via real
   `cpmm.swap_exact_in` math. The validity commitment carries no substrate identity.
3. **Settlement is deterministic / replayable** (pure function — same inputs, same root, every time).
4. **Substrate-independence survives input reordering** (a substrate canonicalizes, so submission order is irrelevant).
5. **Canonical ordering is *required*** (non-vacuous): a non-canonical
   submission-order substrate yields a **different** root — which is exactly why a
   deterministic, grinding-resistant tie-break (`experiments/neutral_tiebreak_v1/`)
   is load-bearing for portability.

Run:
```
PYTHONPATH=. pytest experiments/tau_substrate_independence_v1/test_substrate_independence.py -q   # 6 passed
```

## What v2 proves (production engine, 6 tests)

`engine_conformance.py` lifts the proof from the minimal swap apply to the **real
batch settlement engine** `src.core.batch_clearing.compute_settlement`, establishing
the stronger production-grade property:

> The settlement is a pure function of the intent **set** + pre-state, and is
> **invariant to the order a substrate delivers the intents in** — because the
> engine canonicalises internally.

So a Tau checkpoint, a non-Tau local sequencer, and even an **adversarial shuffler**
all yield the **byte-identical** settlement (verified across both `greedy_ab_refined`
and `optimal_ab_bounded`, 30 random delivery permutations, plus a non-vacuity check
that the settlement actually fills). The orderer cannot change *what* settles — only,
at most, inclusion/liveness. This is the "run the production engine off-Tau → same
result" half of the game day, done in-process.

A sixth test extends this to a **multi-batch trajectory**: a 3-batch sequence run
through `compute_settlement` + the pure `apply_settlement_pure`, carrying state
across batches, yields the **byte-identical REAL `compute_state_root` sequence**
under a Tau checkpoint vs non-Tau (reversed / adversarially-shuffled) delivery — so
not just one settlement but a whole *trajectory* is substrate-independent.

## Scope / honesty

v1 demonstrates the **validity half** with real core primitives (`cpmm` +
`compute_state_root`) in a **minimal** pool-swap settlement; v2 extends it to the
**production `compute_settlement` engine** — including a multi-batch trajectory —
but still **in-process**: **not** yet driven by a live alternative sequencer
*process*, and **not** yet RISC0 receipt replay. Together they prove the *property*
(validity/settlement is a pure, substrate-agnostic function of the batch) and
install the *guard* (core stays Tau-free).

## The full "Tau-failure game day" (remaining increments)

v2 closed the engine half **in-process** (order-invariance of `compute_settlement`).
To fully discharge gap #0, run periodically (and in CI), per the portable root
spine in `internal/ZENO_EXECUTION_LAYER_DECISION_MATRIX_2026_05_14.md`:

1. **(engine + trajectory — DONE in-process by v2)** `compute_settlement` is
   substrate-order-independent, and the **multi-batch trajectory** (state carried via
   `apply_settlement_pure`) is substrate-independent over the REAL state root; what
   remains is to drive it from a **live** non-Tau sequencer *process* (a local signed
   sequencer or the CometBFT appchain profile) rather than an in-process substrate.
2. **Replay the proof-carrying receipts** (RISC0, `zk/state_proof_risc0/`) and
   assert they verify **byte-identically** to the Tau-path receipts — proving
   correctness is portable, not just the state root.
3. **Tau gate off** (default) throughout; assert no degradation vs the Tau path.
4. **Keep it in CI** so the escape hatch cannot bitrot.

That converts "we could detach from Tau" into "we have detached, and it passes."

## Status

Isolated prototype: v1 (6 tests, minimal swap apply) + v2 (6 tests, production
`compute_settlement` incl. a multi-batch trajectory) = **12 tests**. Imports the
real core (read-only, pure calls);
imports nothing from `src/integration` (the Tau shell). No state mutation, no I/O
beyond the subprocess import-guard.
