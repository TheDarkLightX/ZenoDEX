# ZenoDEX Host-Independent Coverage V0

This document scopes the current host-independence target for ZenoDEX and
ZenoLedger.

```text
HostIndependent(surface) :=
  FailClosedBlocked(surface)
  or (PublicDataAvailable(surface)
      and (DeterministicReplay(surface) or ValidProof(surface)))
```

The host can be adversarial. Docker is a packaging and deployment tool, not a
correctness boundary. A transition is acceptable only when another machine can
replay it deterministically from public inputs and replay artifacts, verify a
valid proof bound to public inputs and proof artifacts, or reject it because the
required proof/replay lane is missing.

The current production-feasible posture is full-node host independence for the
bounded covered surfaces. Succinct verification for every value-moving surface
remains open. This mirrors the useful lesson from Lean/Beam-style Ethereum
work: move toward proof-backed validation, keep re-execution/replay available,
and promote mandatory proof verification only after coverage, performance, and
multi-implementation evidence are real.

## Current Boundary

- Full-node host independence: `supported_scoped`
- Succinct proof coverage for every critical transition: `frontier_open`
- Synchronous exchange admission: deterministic replay
- ZK proving: opt-in or asynchronous for currently covered kernels

The machine-readable manifest is
[`ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json`](ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json).

Run:

```bash
python3 tools/check_zenodex_host_independent_coverage.py --pretty
python3 tools/check_zenodex_batch_proof_coverage.py --pretty
python3 tools/check_zenodex_proof_substrate_obligations.py --pretty
python3 tools/check_zenodex_transition_profile_closure.py --pretty
python3 tools/check_zenodex_critical_value_surface_inventory.py --pretty
python3 tools/measure_zenodex_zk_transition_coverage.py --pretty
```

The checker rejects:

- Docker or process isolation as a correctness boundary.
- Metadata/report replay counted as transition correctness.
- Transition coverage without a public-data-availability mode appropriate to
  replay or proof verification.
- Covered surfaces without a supported/proved claim, proof-surface binding, or
  replay evidence path.
- Proof-surface ids that are absent from the ZenoLedger proof coverage matrix.
- Tau guard evidence counted as full execution-proof coverage.
- Admitted critical transition families missing a governed replay/proof profile,
  public-data mode, evidence path, or checker command.
- Proof-required profile operations that are marked `not_covered` but lack an
  explicit fail-closed unsupported-family entry.
- Critical transition-family claims that are not tied to live source files and
  required runtime/proof symbols.
- Any `full_zk_everywhere` style claim while known proof gaps remain.

## Tau And Proof Substrates

Tau is useful for bounded guard, policy, and admission obligations over
host-projected facts. It can reduce the non-zk backlog only where the remaining
obligation is a boolean guard or finite policy composition check, and only when
the fact producers are separately bound and fail-closed.

The machine-readable partition is
[`ZENODEX_PROOF_SUBSTRATE_OBLIGATIONS_V0.json`](ZENODEX_PROOF_SUBSTRATE_OBLIGATIONS_V0.json).
The checker requires every open proof gap and every unsupported proof-required
spot family to say which substrate is still required. Current result:

- `tau_guard_gap_count = 5`, covering scoped guard/admission evidence for
  oracle, zUSD, perps, proof-market, and finality-admission policy.
- `tau_closed_real_proof_gap_count = 0`.
- Value-moving open proof gaps still require `zkvm_execution` or deterministic
  replay for full-node validation.
- Light-client production finality still needs external consensus/finality
  evidence beyond a Tau dispute-window guard.

This is the answer to the Tau boundary question: use Tau for the parts that are
really policy guards; keep execution proofs, state-root transitions, oracle
truth, recursive aggregation, and production finality in replay, zkVM, or
external-consensus lanes.

## Batch Proof Path

Proof batching is now tracked as a separate coverage artifact:
[`ZENODEX_BATCH_PROOF_COVERAGE_V0.json`](ZENODEX_BATCH_PROOF_COVERAGE_V0.json).
It does not close the full-ZK frontier. It requires every open proof gap in the
ZenoLedger proof matrix to have a governed batch lane with:

- untrusted prover assumption;
- public input fields for chain/profile/proof ids, pre/post roots, batch root,
  transition count, and public-data root;
- a fail-closed proof-required rule for missing, mismatched, or uncovered
  proofs;
- a deterministic replay, checkpoint replay, or metadata replay fallback until
  the real proof is implemented;
- warm batched p95/p99 benchmark requirements with private hardware details
  kept out of public artifacts.

This captures the Ethereum-style tradeoff: specialized provers may parallelize
and aggregate work, while validators either verify public proof artifacts or
replay public artifacts. Batching improves performance and amortizes proving
cost; it is not itself a correctness boundary.

## Transition-Family Closure

The transition-family closure manifest is
[`ZENODEX_TRANSITION_PROFILE_CLOSURE_V0.json`](ZENODEX_TRANSITION_PROFILE_CLOSURE_V0.json).
It maps each covered value-moving surface to concrete admitted families and
records whether admission is by deterministic replay or by a governed zkVM proof
profile. It also records proof-required families that must reject fail-closed
because the current spot v1 Risc0 profile does not cover them, including
`swap_exact_out`, `upba_batch_clearing`, `multi_hop`, rejected receipt
execution, and native asset sync.

```text
AdmittedCriticalFamily -> PublicDataAvailable and (ReplayAccepted or ProofAccepted)
```

Unsupported proof-required families remain explicit non-admissions until a
profile adds real proof coverage and the checker is updated with replayable
evidence.

## Critical Value-Surface Inventory

The source inventory manifest is
[`ZENODEX_CRITICAL_VALUE_SURFACE_INVENTORY_V0.json`](ZENODEX_CRITICAL_VALUE_SURFACE_INVENTORY_V0.json).
It binds each admitted transition-family group to the runtime, proof, or
certificate files and symbols that currently implement that surface. It also
binds the current proof-required non-admissions to the proof-profile registry.

This is claim-control evidence. If a critical source path disappears, a required
symbol is renamed, a transition closure group loses its source mapping, or an
unsupported proof-required entry is omitted, the checker rejects the release.

## Performance Reading

Mandatory synchronous zkVM proving for every ZenoDEX transition would be the
wrong current target for ordinary DEX latency. Deterministic replay is cheap
enough for validators and full nodes. Proofs should be batched, cached,
generated asynchronously, or required only for scoped kernels until prover
latency and coverage support mandatory use.

The 2026-05-31 local release-CLI smoke measured `swap_exact_in` at 76.913s to
generate and 0.032s to verify on a private local developer workstation. The
useful signal is that verification is cheap while proof generation is still a
prover workload. See
[`ZENODEX_ZK_PERFORMANCE_SNAPSHOT_2026_05_31.md`](ZENODEX_ZK_PERFORMANCE_SNAPSHOT_2026_05_31.md).

The long-term target is stronger:

```text
EveryCriticalTransition -> PublicDataAvailable and (ReplayAccepted or ProofAccepted)
```

For light clients and compressed cross-machine verification, the target becomes:

```text
EveryCriticalTransition -> ValidSuccinctProof
```

That second statement is still a frontier target in this repo.
