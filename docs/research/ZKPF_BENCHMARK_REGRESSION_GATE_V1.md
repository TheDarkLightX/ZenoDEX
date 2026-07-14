# ZKPF Benchmark Regression Gate V1

Date: 2026-07-14

Status: deterministic comparison gate implemented; live benchmark capture and production SLOs remain separate

## Purpose

Recursive-proof performance results are easy to misinterpret. Two records are
not comparable merely because they both contain a proving time. Program bytes,
proof profile, verifier, workload, machine, and toolchain all affect the result.

`tools/check_zkpf_benchmark_regression.py` first requires exact equality of those
identities. Only then does it compare performance metrics under an integer-only
policy.

The gate addresses three development problems:

1. performance claims made across different proof problems;
2. accidental proof-size, cycle, segment, or memory regressions hidden by a
   faster wall-clock result;
3. floating-point threshold differences across implementations.

## Architecture lessons

The design follows recurring practices in mature proof systems:

- SP1 treats recursion shape, arity, deferred proofs, and shrink stages as
  explicit performance identities rather than one undifferentiated proof;
- Plonky3 requires benchmark methodology and before/after evidence for
  performance changes;
- Stwo treats performance regressions as blocking and keeps reference and
  optimized implementations behaviorally aligned;
- RISC Zero exposes distinct segment, composite, succinct, and wrapped receipt
  stages, so their costs should not be combined into one ambiguous number.

ZKPF should therefore record each stage independently and compare only exact
like-for-like work.

## Record identity

A benchmark record binds:

```text
stage ID
program ID
proof-profile ID
verifier ID
workload digest
machine-profile digest
toolchain digest
implementation digest
sample and warmup counts
exact integer metrics
authority flags fixed false
```

The implementation digest may differ between baseline and candidate. Every
other identity must match. A candidate measured on a different CPU, workload,
guest program, verifier, or proof profile is rejected as incomparable rather
than accepted as an improvement.

## Metrics

The development policy currently requires:

```text
cycles_max
journal_bytes
peak_rss_bytes_max
proof_bytes
prove_time_ns_p50
prove_time_ns_p95
segment_count_max
verify_time_ns_p50
verify_time_ns_p95
```

Cycle, journal, proof-size, and segment-count growth is disallowed in the default
development policy. Proving and verification time have small relative budgets,
and peak resident memory has a five-percent budget. These are development
regression thresholds, not production service-level objectives.

Stage-specific production profiles may add hard maxima after representative
hardware and workload evidence exists.

## Integer comparison

For baseline value `b`, candidate value `c`, and permitted regression `r` basis
points, the checker accepts only when:

```text
c * 10000 <= b * (10000 + r)
```

No floating-point operation participates. A candidate one integer unit beyond
the boundary rejects.

Where a hard maximum exists, both the relative threshold and hard maximum must
pass.

## Benchmark capture obligation

This checker validates records; it does not authenticate how they were
produced. A future capture tool should:

1. run inside a governed machine profile;
2. bind executable, program, verifier, toolchain, and workload bytes before
   execution;
3. run declared warmups and samples;
4. collect monotonic wall time, cycles, segments, artifact sizes, and peak RSS;
5. publish raw samples as well as p50/p95 summaries;
6. retain failed and timed-out samples instead of silently discarding them;
7. produce a signed or independently replayable execution record.

Until that exists, benchmark records remain developer evidence.

## Use

```bash
python3 tools/check_zkpf_benchmark_regression.py \
  --policy config/proof_profiles/zkpf_benchmark_development_policy_v1.json \
  --baseline /private/baseline.json \
  --candidate /private/candidate.json \
  --require-pass \
  --pretty
```

Exit status is zero for a passing comparison, one for a valid but rejected
comparison when `--require-pass` is used, and two for malformed input.

## Integration with the other force multipliers

The soundness change gate should require benchmark evidence for prover and
performance paths. The reproof planner should emit a benchmark task whenever a
performance-sensitive stage is invalidated. The benchmark record should use the
same stage ID and exact program/profile identities as that task.

## Explicit nonclaims

A successful comparison does not establish:

- benchmark execution provenance;
- statistical representativeness;
- hardware stability or absence of thermal throttling;
- correctness of p50 or p95 values supplied by the producer;
- production capacity or a service-level objective;
- proof, release, settlement, or production authority.

All records and reports keep every authority field false.
