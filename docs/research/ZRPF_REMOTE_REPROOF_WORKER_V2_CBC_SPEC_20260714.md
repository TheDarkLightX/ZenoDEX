# ZRPF remote reproof worker V2 CBC specification

Status: implemented authority-neutral, one-stage worker over the ZRPF remote
reproof handoff implementation for the eleven supported stages below.

The worker implementation filename remains V2, while its compute-aware capture
wire schema and identity domain are V3. This ratchet revokes prior V2 worker
captures and prevents the new compute-profile field from being interpreted
under the older identity domain. The companion handoff specification records
the complete V2-to-V3 family ratchet.

The worker may execute only a task already fixed by the governed handoff
catalog. It does not accept an arbitrary executable, argv vector, resource
class, environment, input role, output role, or success predicate from the
operator.

## Positive claim

A successfully checked worker capture establishes these local metadata facts:

1. The handoff re-derived exactly from its C0 source and closed task catalog.
2. The execution packet ID, task ID, stage, ordinal, proof profile, worker
   commit/tree, authority map, non-claims, and ordered input artifact IDs match
   the validated handoff and current input bytes.
3. The repository worktree was at the exact worker commit with no tracked or
   untracked status entries before execution.
4. The declared inputs were copied through bounded stable reads into a fresh
   private snapshot. Executables became mode `0500`; data became mode `0400`.
5. The task used its exact catalog command template, one closed resource
   policy, and one content-bound prover-compute profile. Placeholder resolution
   selected declared input snapshots, declared output paths, exact C0 or worker
   commits, or the closed runtime-binding set.
6. Each subprocess exited zero before the next command began. Standard output
   and standard error stayed within their declared byte bounds. The process
   group was killed on timeout or capture failure.
7. The fresh output root contained exactly the declared output files and their
   necessary parent directories. Every output was a bounded, nonempty,
   single-link regular file with no symlink path component.
8. The capture ID commits to the handoff, packet, task, resource policy,
   prover-compute profile, command transcript digests, output artifact records,
   false authority map, and non-claims.

## Supported stages

The first worker profile supports only templates whose inputs and outputs are
already expressible through the packet ABI:

```text
identity_rebuild
ancestry_materialization
worker_prover_build
source_spot_proof
v2_adapter_receipt
v6_leaf_receipt
v6_l1_receipt
v6_l2_receipt
v6_settlement_receipt
v7_receipt
mutation_verification
```

These stages become `execution_adapter_status = implemented` in the catalog.

The following stage remains blocked:

```text
release_checks
  bundle-aware release adapter remains planned
```

The worker rejects a missing, planned, or unsupported execution adapter.

The mutation stage uses one declared executable artifact from a dedicated
workspace package rather than an ambient binary or shell command. Its exact
packet orders every program, receipt, guest input, retained mutation, and
output role. Mutation-only dependencies are excluded from the production V7
verifier and Firecracker graph. The Rust verifier cryptographically verifies
the leaf, L1, and L2 receipts, then requires the exact settlement envelope's
proposal bytes to equal the verified L2 journal before settlement verification.
It verifies the remaining positives under their governed program identities
and common Succinct profile before it creates any new mutation. It accepts only
a position-distinguishing seal-word-1, bit-0 change,
requires all five negatives to reject at the cryptographic receipt boundary,
and emits one canonical fixed-schema report with all authority fields false.
The report finalizer validates every fixed stage/profile/mutation/reject
invariant. Its active-witness test distinguishes all 17 input-derived scalar
leaves at all five stage positions; fixed schema, status, counts, authority,
and non-claim values are construction invariants committed by the report ID.
Each generated mutation is capped at 16 MiB and the report at 64 KiB by its
artifact contract in addition to the worker resource envelope.

The identity stage resolves `--source-commit` to exact C0. The worker-build
stage resolves it to the distinct exact worker/G commit. Worker build executes
two clean, pinned, no-network Docker builds: one V6 host bundle and one V7
program/host bundle. The adapter requires an exact ordered archive-member
inventory, ELF or R0BF magic, packet/runtime r0vm equality, a V7 image ID
recomputed by that r0vm, exact post-pin governance bytes, and a canonical
authority-false build report. The report binds all nine extracted outputs.
Ephemeral archive hashes are excluded from its reusable acceptance surface.
Complete build-input closure and malicious same-UID resistance remain false.

## Process contract

The one-shot CLI receives:

```text
canonical handoff JSON
canonical execution-packet JSON
exact repository worktree
input artifact root
fresh run root
fresh capture-output path
```

It creates:

```text
run-root/
  inputs/     exact private snapshots of declared inputs
  outputs/    only declared stage outputs
  home/       empty private HOME
```

Commands use an argv vector directly. No shell parses template text. A token
beginning with `@` must resolve to one declared input or output artifact role.
`@c0_commit` and `@worker_commit` resolve to their distinct validated source
commit fields. `@runtime_*` resolves only through the exact runtime-binding
inventory required by the selected task. Unknown placeholders reject. Fixed
runner names resolve through a closed absolute-path table; artifact runners
resolve to an executable input snapshot.

The subprocess environment is an allowlist:

```text
HOME
LC_ALL=C
PATH=/usr/bin:/bin
PYTHONDONTWRITEBYTECODE=1
TZ=UTC
```

`RISC0_HOME` may be derived only when a prover r0vm is a declared input. Every
proving stage declares the exact, separately content-addressed `prover_r0vm`
artifact as an input. The handoff selects one
of two closed profiles:

| Profile | Exact worker environment | Intended host |
| --- | --- | --- |
| `risc0_ipc_cpu_v1` | `RISC0_PROVER=ipc`, `RISC0_EXECUTOR=ipc`, `RISC0_SERVER_PATH=<packet-prover-r0vm>`, `CUDA_VISIBLE_DEVICES=-1` | bounded CPU fallback |
| `risc0_ipc_cuda_single_visible_device_build_request_v1` | `RISC0_PROVER=ipc`, `RISC0_EXECUTOR=ipc`, `RISC0_SERVER_PATH=<packet-prover-r0vm>`, `CUDA_VISIBLE_DEVICES=0` | one visible NVIDIA device with a separately built CUDA r0vm |

Both profiles use the exact external IPC prover path. RISC Zero 3.0.5 dispatches
both RV32IM and recursion proving through the CUDA HAL when that exact `r0vm`
was compiled with the `cuda` feature. IPC avoids the actor manager's additional
worker topology and wildcard listener. The IPC subprocess still uses a
loopback socket, so the paid runner must retain an isolated network namespace.

The CUDA profile is a build request. It does not assert that `prover_r0vm` was
compiled with CUDA, that a GPU exists, that the visible device is an H100, or
that an accelerated run will satisfy a latency budget. The official installed
RISC Zero 3.0.5 `r0vm` is CPU-only. The identity-rebuild r0vm therefore remains
a separate artifact and is not silently reused as accelerator evidence. A
governed CUDA build record must bind the exact prover-r0vm bytes before a paid
accelerator run. For H100, that record must bind the RISC Zero 3.0.5 source,
Rust toolchain, CUDA toolkit/container, and an explicit `sm_90` NVCC target;
ambient `-arch=native` on the local GTX 1060 is invalid for that purpose. The
capture binds the selected profile, exact prover-r0vm bytes, and observed
command duration. Separate preflight and benchmark evidence own hardware
identity and performance.

The CUDA handoff cannot be created without explicit `--prover-r0vm-sha256` and
`--prover-r0vm-bytes` values. It rejects the known official CPU-only binary
identity. The worker then rehashes the staged executable and requires exact
agreement with those values before starting a proving command. These checks
bind the selected bytes. They do not establish how the executable was built or
which hardware it exercised.

The paid-run sequence and H100 go/no-go budget are specified in
`ZRPF_PROVER_COMPUTE_QUALIFICATION_V1_20260714.md`.

Non-proving stages use `no_risc0_prover_compute_v1` and receive no
`RISC0_PROVER`, `RISC0_EXECUTOR`, `RISC0_SERVER_PATH`, or CUDA-device variable.
Ambient credentials, SSH agents, Cargo configuration, cloud variables, and
arbitrary operator variables are not forwarded.

Each resource class fixes:

```text
wall-clock timeout
maximum captured stdout bytes
maximum captured stderr bytes
maximum single output-file bytes
maximum open descriptors
core-file policy
address-space ceiling
resource-policy ID
```

The capture stores digests and byte counts for stdout and stderr. It does not
publish their raw contents.

## Failure behavior

Every malformed, substituted, stale, missing, surplus, oversized, timed-out,
nonzero-exit, path-escaping, symlinked, hard-linked, or type-ambiguous input
rejects. The capture output remains absent.

A failed run may leave its private run root for diagnosis. Reusing that root
rejects. The caller must choose a new path or explicitly remove the failed
root. The worker never silently cleans and reuses stale output.

## Authority boundary and non-claims

Every worker capture carries exact Boolean false for:

```text
data_availability_authority
ledger_authority
production_authority
proof_authority
release_authority
settlement_authority
```

The worker and capture do not establish:

```text
proof validity or semantic correctness
historical execution provenance outside the local process observation
operator authorization or packet freshness
source-to-binary provenance
runner or host release authority
network or filesystem sandboxing
resistance to a malicious same-UID host process
kernel cgroup or process-count isolation
data availability, finality, ledger admission, settlement, or production
atomic multi-stage publication
```

The capture is an unkeyed deterministic commitment. A publisher can synthesize
one. A separately governed verifier must verify every returned proof and bind
the final release before any authority can advance.

## Required negative controls

```text
command or runner substitution
task, packet, catalog, content, or resource-class substitution
integer-for-Boolean and Boolean-for-integer substitution
stale pre-existing run root
output path escape
output symlink or hard link
missing declared output
surplus output file or directory
oversized stdout or stderr
nonzero exit status
timeout with descendant cleanup
capture-ID or output-record substitution
C0 versus worker/G source-commit substitution
any identity or worker-build output flag/role permutation
worker-build report source, governance, output, image-ID, or authority substitution
unsupported or planned stage
```

## Promotion rule

This worker may be merged as authority-neutral execution tooling after focused
tests, static checks, exact-head assurance inclusion, and independent review.
It cannot promote a proof, release, settlement, ledger, or production claim.
