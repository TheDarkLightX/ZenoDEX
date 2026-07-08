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
python3 tools/measure_zenodex_zk_transition_coverage.py --pretty
python3 tools/check_zeno_ledger_proof_coverage_matrix.py --require-full-zk --pretty
```

The `--require-full-zk` command is the strict readiness check. It is expected to
return nonzero while the matrix still lists open value-moving proof gaps.

The checker rejects:

- Docker or process isolation as a correctness boundary.
- Metadata/report replay counted as transition correctness.
- Transition coverage without a public-data-availability mode appropriate to
  replay or proof verification.
- Covered surfaces without a supported/proved claim, proof-surface binding, or
  replay evidence path.
- Proof-surface ids that are absent from the ZenoLedger proof coverage matrix.
- Any `full_zk_everywhere` style claim while known proof gaps remain.

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
