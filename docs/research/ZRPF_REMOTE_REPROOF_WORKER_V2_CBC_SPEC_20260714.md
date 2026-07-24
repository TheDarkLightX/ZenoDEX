# ZRPF remote reproof worker V2 CBC specification

Status: implemented authority-neutral, one-stage worker plus validated
publication boundary over the ZRPF remote reproof handoff implementation for
the fourteen supported stages below.

The worker orchestration filename remains V2. Authority-neutral filesystem
publication is isolated in `tools/zrpf_remote_reproof_worker_v2_publication.py`,
which depends only on the handoff and worker-contract modules and never imports
the worker. The capture wire schema and identity domain are V4 after adding an
effective resource-policy ID and timeout
to every command capture. The companion handoff/task family is V4 after adding
the source execution-profile predecessor. Execution-packet V5 additionally
binds the content IDs of every required internal producer-stage publication
marker. A V4 worker capture binds the exact V5 execution-packet ID and rejects
older V3 captures whose transcript cannot
establish the paid command deadline.

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
4. The declared inputs and canonical execution packet were copied through
   bounded stable reads into a fresh private snapshot. Executables became mode
   `0500`; data and the packet became mode `0400`.
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
9. `publish-stage` validates that complete capture before any publication
   effect, reopens only its declared outputs through stable no-follow reads,
   requires their records to match the capture, writes bounded unnamed
   `O_TMPFILE` descriptors, fsyncs them, and links each exact descriptor to an
   absent destination with `linkat(AT_EMPTY_PATH)`.
10. Each published parent directory is fsynced, and records recomputed from the
    shared artifact root must exactly equal the capture.
11. The repository and publication namespaces are rechecked, then a
    content-bound authority-false stage marker is linked from its exact unnamed
    descriptor after every output succeeds. Its parent is fsynced and the
    canonical marker/output set is revalidated. Its content ID is bound into
    every dependent execution packet, and the complete ordered marker-ID
    inventory is bound into Return V5 so the terminal marker is distinguished.
    All authority remains false.

## Supported stages

The first worker profile supports only templates whose inputs and outputs are
already expressible through the packet ABI:

```text
identity_rebuild
ancestry_materialization
worker_prover_build
source_execution_profile
source_spot_proof
v2_adapter_receipt
v6_leaf_receipt
v6_l1_receipt
v6_l2_receipt
v6_settlement_receipt
v7_execution_profile
v7_receipt
mutation_verification
release_checks
```

These stages become `execution_adapter_status = implemented` in CUDA handoffs.
CPU handoffs keep `source_spot_proof` explicitly blocked because the observed
CPU proving route exceeded the governed calibration envelope.

The two execution-profile stages run the exact guest environment without
generating a receipt. They bind exact program, guest-input, assumption, journal,
segment, cycle, and `r0vm` identities while keeping accelerator, proof, release,
settlement, and production authority false. The source and V7 proof stages each
run the independent profile checker before starting their expensive prover.
Source proving additionally runs the initial paid-calibration checker over the
private execution-packet snapshot, exact CUDA build record, current H100
preflight, explicit trusted epoch, and an external integer budget/price record.
The worker independently recomputes that result and caps the source proof
subprocess to the derived deadline. A valid execution profile alone cannot
start paid proof generation.

The release-check stage uses one unique artifact flag for each of its forty
returned-artifact roles plus one externally supplied canonical plan
expectation. Worker stage validation first authenticates the marker record for
each of the thirteen predecessors. The adapter then commits their ordered unique
digest list, validates the worker-build and mutation reports, derives every
exact word-one XOR-one relation from the returned receipt pairs, rechecks the
exact V7 program/image/profile/manifest bridge, reconstructs the release-closure
plan, and writes only the declared plan and authority-false evidence outputs. It
cannot consume Return V5 or its own terminal publication marker without making
the task graph cyclic. The worker publishes that marker after successful
execution, and the independent Return V5 checker binds it afterward.

The worker rejects a missing, planned, or unsupported execution adapter. The
current closed catalog has no planned stage.

The receipt relation checker uses the governed stage-specific journal bounds:
65,536 bytes for V6 value-node leaf and aggregate journals, the larger V6
settlement-admission bound for the settlement receipt, and the V7 output bound
for the V7 receipt. This prevents the 4,096-byte legacy structural bound from
silently rejecting a valid large V6 settlement journal. Each receipt is also
capped at the Rust verifier's 16 MiB receipt limit, and the claimed image ID in
each positive receipt must equal the stage's exact expected program image.
Direct adapter output creation is sequential; the worker capture and terminal
publication marker are the completion boundary for the two-file output set.

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
explicit trusted current epoch for a paid calibration stage
canonical attempt budget/price path for a paid calibration stage
```

It creates:

```text
run-root/
  inputs/     exact private snapshots of declared inputs and execution packet
  outputs/    only declared stage outputs
  home/       empty private HOME
```

`publish-stage` consumes that existing run root and capture. It first executes
the complete `check-capture` validation path. It then publishes only the
stage's closed output-contract paths into the existing shared artifact root.
Every destination must begin absent on an initial publication. Exact retry
reconciliation instead requires every existing output and marker byte to match
the original capture. Linux `O_TMPFILE` plus
`linkat(AT_EMPTY_PATH)` is the per-file commit primitive; an unavailable exact
descriptor primitive is a typed reject. Each output file and destination
parent is fsynced before the completion marker is committed. The marker's exact
unnamed descriptor is fsynced before linking, and its parent is fsynced after
linking. The worker then reopens the canonical marker and complete output set.
Every leaf reopen uses nonblocking no-follow flags before the regular-file
check, so a hostile FIFO or other special-file substitution rejects instead of
blocking reconciliation.
A failure after marker visibility is reported as `indeterminate` and requires
exact reconciliation. A retry accepts only the identical marker and outputs,
fsyncs every exact linked file and unique parent directory, and revalidates the
canonical namespace before acknowledging completion.
The final response carries the capture ID, published artifact IDs,
publication-marker ID, and the unchanged all-false authority map.

Per-file publication is no-overwrite and the marker supplies logical atomicity
for downstream stages. A crash or external race can leave a published strict
prefix, but packet preparation requires the absent marker even when the one
output it consumes already exists. Automatic retry cannot overwrite the
prefix. Explicit operator audit and a fresh artifact root are required.

Commands use an argv vector directly. No shell parses template text. A token
beginning with `@` must resolve to one declared input or output artifact role.
`@c0_commit` and `@worker_commit` resolve to their distinct validated source
commit fields. `@runtime_*` resolves only through the exact runtime-binding
inventory required by the selected task. Unknown placeholders reject. Fixed
runner names resolve through a closed absolute-path table; artifact runners
resolve to an executable input snapshot.

`@execution_packet_file` resolves only to the worker-created mode-`0400`
snapshot of the validated packet. `@trusted_current_epoch_seconds` requires one
explicit positive integer and is bound into the resolved command digest. The
attempt budget/price document is a runtime input because it commits to the
packet ID; including it in that packet would create a circular
content-addressing dependency. The worker copies it through a stable read into
the private runtime-input snapshot before any command runs. The emitted
qualification commits to those exact budget bytes, and the worker recomputes it
before proof launch.

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
| `risc0_ipc_cpu_v1` | `RISC0_PROVER=ipc`, `RISC0_EXECUTOR=ipc`, `RISC0_SERVER_PATH=<packet-prover-r0vm>`, `CUDA_VISIBLE_DEVICES=-1` | execution-only and worker tests; source proof is disqualified |
| `risc0_ipc_cuda_single_visible_device_build_request_v1` | `RISC0_PROVER=ipc`, `RISC0_EXECUTOR=ipc`, `RISC0_SERVER_PATH=<packet-prover-r0vm>`, `CUDA_VISIBLE_DEVICES=0` | one visible NVIDIA device with a separately built CUDA r0vm |

Both profiles use the exact external IPC prover path. RISC Zero 3.0.5 dispatches
both RV32IM and recursion proving through the CUDA HAL when that exact `r0vm`
was compiled with the `cuda` feature. IPC avoids the actor manager's additional
worker topology and wildcard listener. The IPC subprocess still uses a
loopback socket, so the paid runner must retain an isolated network namespace.

The planner retains the CPU profile for deterministic execution profiles and
worker tests. The governed worker rejects `source_spot_proof` under that
profile. This makes the observed Linux and Apple CPU nonqualification an
explicit execution rule instead of relying on operator discipline.

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

The initial paid attempt is capped at four dollars and 30 minutes. The worker
limits both pre-proof checkers to 60 seconds and uses the qualification's
integer deadline, rounded downward to whole seconds, for the source proof.
There is no continuation or additional-spend gate. Pod setup and deallocation
remain external, so a cloud controller must impose an independent allocation
TTL. That TTL is also the active stop boundary for a process-launch or pre-exec
stall. The worker rejects a completed command whose total measured elapsed time
exceeds its effective deadline, but it cannot interrupt Python `Popen` before
that call returns.

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

Publication additionally rejects an invalid capture before creating any
destination, a changed source output, a noncanonical or symlinked parent, a
pre-existing or concurrently raced destination, an unavailable unnamed-file or
exact-descriptor link primitive, a write or fsync failure, and any final
published-record mismatch. It never overwrites an existing artifact.
Repository, artifact, and run roots must be pairwise disjoint. No named
temporary is created, and cleanup closes descriptors without unlinking a
pathname that another publisher could replace.

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
bind-mount alias detection beyond canonical pathname disjointness
kernel cgroup or process-count isolation
PID/PGID reuse resistance or cgroup-owned descendant teardown
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
unsupported stage or execution-adapter mismatch
invalid capture before publication effects
changed captured output during publication
pre-existing or concurrently raced publication destination
publication unnamed-file, fsync, or exact-descriptor link failure
published artifact record differing from the validated capture
partial multi-output prefix without a completion marker
completion-marker content, producer-packet, task, or output substitution
competing publisher pathname substitution or cleanup deletion
post-marker failure requiring exact indeterminate reconciliation
repository mutation between capture validation and publication commit
FIFO or special-file marker/output substitution before stable read or reconciliation
```

## Promotion rule

This worker may be merged as authority-neutral execution tooling after focused
tests, static checks, exact-head assurance inclusion, and independent review.
It cannot promote a proof, release, settlement, ledger, or production claim.
