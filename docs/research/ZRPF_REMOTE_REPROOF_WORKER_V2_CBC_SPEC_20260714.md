# ZRPF remote reproof worker V2 CBC specification

Status: implemented authority-neutral, one-stage worker over the existing ZRPF
remote reproof handoff V2 packet ABI for the eight supported stages below.

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
5. The task used its exact catalog command template and one closed resource
   policy. Placeholder resolution selected only declared input snapshots or
   declared output paths.
6. Each subprocess exited zero before the next command began. Standard output
   and standard error stayed within their declared byte bounds. The process
   group was killed on timeout or capture failure.
7. The fresh output root contained exactly the declared output files and their
   necessary parent directories. Every output was a bounded, nonempty,
   single-link regular file with no symlink path component.
8. The capture ID commits to the handoff, packet, task, resource policy,
   command transcript digests, output artifact records, false authority map,
   and non-claims.

## Supported stages

The first worker profile supports only templates whose inputs and outputs are
already expressible through the packet ABI:

```text
ancestry_materialization
source_spot_proof
v2_adapter_receipt
v6_leaf_receipt
v6_l1_receipt
v6_l2_receipt
v6_settlement_receipt
v7_receipt
```

These stages become `execution_adapter_status = implemented` in the catalog.

The following stages remain blocked:

```text
identity_rebuild
  requires unbound Docker, Cargo-registry, and fixed external run-root inputs

worker_prover_build
  requires a governed Cargo-output collector and clean target contract

mutation_verification
  command template remains planned

release_checks
  bundle-aware release adapter remains planned
```

The worker rejects a missing, planned, or unsupported execution adapter.

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
Unknown placeholders reject. Fixed runner names resolve through a closed
absolute-path table; artifact runners resolve to an executable input snapshot.

The subprocess environment is an allowlist:

```text
HOME
LC_ALL=C
PATH=/usr/bin:/bin
PYTHONDONTWRITEBYTECODE=1
TZ=UTC
```

`RISC0_HOME` may be derived only when `r0vm` is a declared input. Ambient
credentials, SSH agents, Cargo configuration, cloud variables, and arbitrary
operator variables are not forwarded.

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
unsupported or planned stage
```

## Promotion rule

This worker may be merged as authority-neutral execution tooling after focused
tests, static checks, exact-head assurance inclusion, and independent review.
It cannot promote a proof, release, settlement, ledger, or production claim.
