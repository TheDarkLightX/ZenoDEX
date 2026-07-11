# ZRPF V3 Retained Replay Threat Model

Date: 2026-07-10

Status: normative for the experimental retained-receipt replay lane

Isolation profile: `unsandboxed_preexec_limited_subprocess_v1`
Machine-readable companion:
`docs/research/ZRPF_V3_RETAINED_REPLAY_CHANNEL_MATRIX_20260710.json`

## Purpose And Scope

This document defines the security boundary for the ZenoDEX ZRPF V3 retained
structural receipt replay lane. It governs the source-built host verifier,
Python build and replay tooling, eight retained receipt artifacts, replay
transcripts, and evidence records.

The exact positive execution claim is:

> A host verifier built from the governed repository source snapshot on the
> recorded host verifies seven retained RISC0 Succinct receipts forming four
> adapter leaves, two level-one structural nodes, and one level-two structural
> root. It independently recomposes the expected level-one and level-two
> journals and rejects the governed exact root-seal mutation.

The preferred status name is:

```text
source_built_retained_receipt_structural_replay_accepted
```

The claim applies to a recorded live run and to a fresh successful `--live`
run. Static evidence validation checks canonical record and material parity. It
does not execute the verifier or authenticate the historical execution event.

The evidence phrase `executing_binary_identity_authenticated` has one narrow
meaning in this schema: the live runner hashes stable built-verifier bytes,
copies those exact bytes into a fully sealed memfd, and executes that same
descriptor. It does not assert a signature, an independent builder, a
reproducible binary, or complete source-to-binary provenance. Those claims
remain false. Static validation also pins the complete canonical evidence
SHA-256 independently of the identity fields stored inside the evidence.

A fresh `--live` report records whether its built binary matches the historical
recorded binary. Binary mismatch remains possible because reproducible-build
status is false. The selected dependency graph must match the recorded graph
exactly, and the report distinguishes fresh structural verification from exact
recorded-evidence parity.

The source-built component is the native host replay verifier. The current
lane does not rebuild the guest programs, recompute image IDs from fresh guest
ELFs, regenerate proofs, or establish source-to-guest-image provenance.

The annotated tag `zrpf-v3-source-anchor-20260711` preserves the exact source
commit used by the source-built replay. Required CI verifies the tag target
before static validation or compilation. The separate
`zrpf-v1-retained-source-anchor-20260710` tag preserves the historical adapter
reference commit. The superseded `zrpf-v3-source-anchor-20260710` tag and its
2026-07-10 evidence record remain historical regression artifacts. These tags
must be pushed and retained with the branch.

## Authority Progression

The lane must preserve this progression:

```text
untrusted retained bytes
  -> bounded regular-file bytes
  -> exact name, size, and SHA-256 binding
  -> strict canonical receipt decoding
  -> pinned Succinct receipt-profile verification
  -> authenticated journal
  -> independently recomposed expected parent journal
  -> exact root and topology checks
  -> scoped structural replay evidence
  -> no ledger, settlement, release, or production authority
```

The source snapshot, build process, dependency cache, native executable,
transcript, and evidence metadata may propose facts. The receipt verifier and
exact journal recomposition establish only the scoped structural result.

## Current Isolation Profile

`unsandboxed_preexec_limited_subprocess_v1` accurately describes the
implementation at the date of this document.

Implemented controls:

- a fresh externally located target directory must not pre-exist;
- the target directory is required to be owned by the invoking user and mode
  `0700`;
- a detached source worktree is checked against a pinned commit and tree;
- checkout hooks are disabled;
- the exact selected compiler-visible repository inventory is hashed before
  and after compilation;
- selected Cargo packages disable automatic build, binary, example, test, and
  benchmark target discovery;
- the `execve` environment map is constructed from an allowlist;
- Cargo is invoked with `--frozen` and offline resolution settings;
- positive stdout and stderr are captured separately;
- the current positive stdout is bound to an exact length and SHA-256;
- current positive stderr must be empty;
- each captured stream has a byte cap;
- each subprocess has a wall-clock timeout;
- explicit build, replay, and tool process profiles install resource limits
  before `execve`;
- every process profile sets a private umask, disables core dumps, bounds CPU
  time, and installs `no_new_privs` before `execve`;
- the replay profile additionally bounds address space, output-file size, open
  descriptors, stack size, and process creation;
- replay `RLIMIT_NPROC=1` rejects a tested fork attempt;
- live replay requires identical nonzero real, effective, saved, and filesystem
  UID/GID values and zero inherited, permitted, effective, and ambient Linux
  capabilities before creating the build target;
- the built verifier is copied through stable descriptor reads into a fully
  sealed Linux memfd and executed from that descriptor;
- subprocesses begin in a new process session, with best-effort process-group
  termination on detected failure.

Unsupported isolation properties:

- no user, PID, mount, IPC, or network namespace is installed;
- no seccomp policy is installed;
- no cgroup or equivalent process-lifetime boundary is installed;
- build and tool profiles permit bounded process creation and do not provide a
  complete descendant-lifetime guarantee;
- pre-exec limits do not provide a writable-filesystem quota or mount policy;
- host filesystem reads and writes are available to the child process;
- host network socket creation and egress are not denied by the lane;
- parent-process state under `/proc` is not hidden;
- the Cargo registry and Git caches are linked from the invoking account;
- the dynamic loader, shared libraries, kernel, and runtime root filesystem are
  supplied by the host;
- process-group termination does not contain a child that creates a new
  session, and it does not provide a complete descendant-lifetime guarantee;
- no microarchitectural or hardware side-channel defense is established.

This profile is pre-exec-limited process execution on a shared host. It is not
a native binary sandbox.

## Confidentiality Policy

All retained receipts, journals, image IDs, policies, transcripts, and evidence
records in this lane are public inputs or public outputs. The lane makes no
confidentiality, witness-privacy, zero-knowledge privacy, covert-channel
freedom, constant-time, or hardware side-channel claim.

No secret is permitted in the build or replay execution environment. In
particular, the launcher must not make any of the following available:

- signing or release keys;
- repository write credentials;
- SSH agents or private keys;
- cloud credentials or metadata-service tokens;
- package-registry credentials;
- unrelated private source or data;
- a container or orchestration control socket;
- host-home mounts beyond inputs explicitly required by the recorded build.

An allowlisted child environment map is a useful input control. It does not
hide the parent environment, host filesystem, process table, or open resources
from a same-user native process. Secret absence therefore remains an operator
and CI-runner precondition under the current profile.

Signing and release authorization must execute in a separate trusted process.
That process may consume reviewed digests. It must not share credentials with
the build or replay process.

## Threat Actors

### Malicious receipt publisher

The publisher supplies malformed, substituted, noncanonical, oversized, or
cryptographically invalid receipt bytes. Exact artifact binding, bounded
descriptor-relative reads, strict decoding, pinned image IDs, and receipt
verification own this boundary.

### Malicious bundle or evidence author

The author may coherently change artifacts, metadata, claims, and expected
hashes. Canonical local checks detect accidental or partial drift. Independent
review and an external governed anchor are required to resist a coherent
rewrite. No external release anchor exists for this lane.

### Same-user local racer

A local process may replace source, toolchain, target, or executable paths
between checks and use. Private modes reduce exposure to other operating-system
users. They do not isolate processes running under the same user identity.
Stable descriptor reads and sealed-memfd execution narrow file and executable
path substitution. Immutable build mounts and a stronger same-user isolation
boundary remain promotion requirements.

### Compromised dependency, build script, compiler, or cache

Build-time code may read host resources, create processes, use the network, or
produce a verifier unrelated to reviewed source. The lockfile and offline Cargo
mode narrow dependency selection. The current lane does not authenticate the
complete dependency cache, compiler closure, linker, build scripts, proc
macros, runtime loader, or root filesystem.

### Malicious native verifier process

The process may attempt to flood output, consume resources, fork descendants,
read host files, inspect parent state, or use network channels. The replay
profile bounds output, time, address space, file size, descriptors, stack, and
process creation. Host-filesystem containment, network denial, and cgroup
ownership remain open.

### Malicious co-tenant

A co-tenant may observe timing, cache, branch-predictor, memory-pressure, or
shared-hardware effects. The current shared-host profile provides no defense or
claim for these channels.

## Protected Assets

- receipt and journal verification authority;
- exact root and topology identity;
- claim and non-claim integrity;
- source-to-build and toolchain provenance records;
- host integrity and availability;
- private host information outside the public replay inputs;
- repository and package credentials;
- release-signing and settlement authority;
- evidence reproducibility and auditability.

## Trust Assumptions

The experimental result assumes:

- the reviewed checker and verifier source are the source under evaluation;
- the pinned source commit and tree are available and have the recorded bytes;
- the invoking host, kernel, dynamic loader, system libraries, compiler closure,
  and dependency cache are trusted for the local run;
- the invoking account is not concurrently compromised;
- no secret is accessible to build or replay processes;
- the retained receipt bytes are public and may be adversarial;
- the expected RISC0 image IDs and receipt profile are reviewed protocol inputs;
- independent review supplies the trust root for a coherent repository change.

Failure of a host or build trust assumption invalidates the corresponding
provenance or containment claim. It does not upgrade any authority flag.

## Channel Policy

The machine-readable matrix records direct, filesystem, network, process,
timing, metadata, and microarchitectural channels. Each row identifies its
sender, receiver, observable signal, current bound, mitigation, residual risk,
test evidence, and claim status.

Current positive replay output has a strong direct-output bound:

```text
stdout size   = 5,920 bytes
stdout SHA-256 = 7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288
stderr size   = 0 bytes
verifier SHA-256 = 57725f52473e027c55f71f17abddc2ee043a006232da762bfc10a066d120d5b9
```

That bound authenticates one public transcript. It does not constrain timing,
network, filesystem, process, kernel, or microarchitectural channels.

Negative-control stderr has a 65,536-byte cap, one exact field set, strict JSON
decoding, and canonical-byte equality. Raw operating-system exception text must
not become public evidence because it may contain host paths.

Proof and receipt bytes are public artifacts. A string and credential-pattern
scan can detect common accidental disclosures. Such a scan cannot prove the
absence of deliberately encoded or high-entropy data in proof bytes. Proof
generation must therefore occur without secrets whenever receipts will be
published.

## Required Fail-Closed Rules

1. Unknown claim fields and non-Boolean substitutions must reject.
2. Every unsupported isolation, provenance, confidentiality, and authority
   property must remain an exact `false` Boolean.
3. A missing sandbox backend must select the actual weaker isolation profile.
4. A missing privacy scan must keep `artifact_privacy_scan_passed=false`.
5. A missing network boundary must keep build and replay network-disabled claims
   false.
6. A missing complete build-input closure must keep that claim false.
7. Static record validation must not set live execution true.
8. Failed or timed-out subprocesses must produce no scoped replay advancement.
9. Signing and release authority must remain outside build and replay.
10. Semantic, ledger, settlement, release, production, privacy, side-channel,
    and covert-channel claims remain false until separate evidence closes them.

## Current Evidence And Tests

Durable current evidence includes:

- `docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260711.json`;
- `evidence/zrpf-v3-retained-structural-replay-v1/receipts/`;
- `tools/check_zrpf_v3_replay_verifier_evidence.py`;
- `tools/zrpf_v3_artifact_privacy.py`;
- `tests/test_check_zrpf_v3_replay_verifier_evidence.py`.

The 2026-07-10 source-built replay record remains a historical source-anchor
artifact and is still included in the bounded public privacy scan.

Current tests cover environment-map filtering, private target creation, checkout
hook suppression, selected source and receipt symlink rejection, output-cap
rejection, strict evidence JSON, material mutation, exact report validation,
source-anchor parity, undeclared build-script rejection, sealed-memfd execution
after source-path replacement, `no_new_privs`, replay fork rejection under
`RLIMIT_NPROC=1`, canonical negative output, and bounded public-artifact privacy
scanning.

The current committed suite does not establish network denial, parent-process
invisibility, host-filesystem isolation, cgroup descendant containment,
constant-time behavior, or hardware side-channel resistance.

## Promotion Profiles

### Experimental structural evidence

This profile may retain the current bounded host runner when all authority and
confidentiality non-claims remain false, reviewers understand the trusted-host
assumption, and the live command runs in a disposable secretless environment.
The exact compiler-visible repository inventory and bounded public-artifact
privacy scan are enforced. Complete build inputs and stronger process isolation
remain promotion requirements.

### Required continuous integration replay

A required CI replay must use a secretless job, disable persisted checkout
credentials, deny network egress at the runtime boundary, use read-only source
and input mounts, bound writable storage and descendants, and record the actual
isolation tier. A hardened rootless OCI runtime is the minimum target for
reviewed source on a shared kernel.

### Strong public native replay

Execution of artifacts treated as hostile requires a stronger boundary such as
an application-kernel sandbox or disposable microVM. The evidence must record
the runtime image digest, policy digest, and isolation tier. Hardware side-
channel resistance remains false unless a separate profile establishes it.

The candidate Firecracker profile is
`config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json`. It pins the
Firecracker v1.16.1 x86_64 release archive, release binary, matching jailer,
annotated tag object, and tag commit. It also fixes the configurable device
policy: the jailer, built-in default seccomp, a new PID namespace, a fresh and
exclusive empty network namespace, no API, no NIC, no MMDS, no vsock, a
read-only guest rootfs drive and input drive, and a bounded raw output drive are
required. The profile separately inventories Firecracker's always-present or
non-configurable x86 serial, keyboard-controller, interrupt-controller, timer,
clock, VMGenID, and VMClock device types. VMGenID state changes per boot and
VMClock exposes time state, so neither supports a determinism or timing-channel
claim. The serial sink remains bounded because a guest can reactivate the 8250
device.

Firecracker v1.16.1 reverted `O_NOFOLLOW` for jailer cgroup and network-
namespace operations. The future launcher must independently reject symlinks,
verify a root-owned and non-writable full parent chain, bind the namespace type
and inode before use, and verify the joined namespace after launch. The jailer
also materializes host device nodes inside its jail. The candidate profile
therefore inventories `/dev/kvm`, `/dev/net/tun`, `/dev/urandom`, and conditional
`/dev/userfaultfd` exposure even though no guest NIC, randomness device, or
snapshot path is allowed.

The candidate also defines the future launcher contract. Release extraction
must start from a stable descriptor whose exact size and SHA-256 already match
the governed archive. The launcher must then enforce an exact member inventory,
reject traversal, duplicate members, links and special files, extract only the
selected regular files without archive ownership or timestamps, and rehash the
opened outputs. The exact candidate VM configuration is now frozen: one vCPU,
256 MiB, SMT and dirty tracking disabled, no huge pages, three ordered
synchronous VirtIO block drives, and fixed per-drive rate limiters. The root
configuration admits only `boot-source`, `drives`, and `machine-config`.

Network-namespace requirements are phase-specific. The fresh namespace has
zero processes before join, exactly the expected Firecracker process set while
active, and zero processes after teardown. Every phase must retain the same
namespace inode. The raw output protocol similarly requires a fresh fixed-size
object, request and input-root binding, a 256-bit run nonce, bounded length and
payload hash, a final commit marker flushed last, stable-descriptor reading
after VM exit, and canonical zero trailing bytes. Process exit status carries
no verifier authority.

The governed cgroup v2 attachment uses one launcher-created domain leaf. The
launcher must establish the exact leaf path, stable device and inode, an exact
`domain` type, empty `cgroup.subtree_control`, empty `cgroup.procs`,
`populated 0`, the required controller files, and exact numeric limits before
starting the jailer. It supplies `--cgroup-version=2` and `--parent-cgroup`
for that exact existing leaf, with zero jailer `--cgroup` property arguments.
An absent leaf is a launcher rejection because the jailer can otherwise
continue without moving the process. After launch, the supervisor must verify
the expected process set, `/proc/<pid>/cgroup` membership, unchanged leaf
identity, and unchanged limits. Teardown writes literal `1\n` to
`cgroup.kill`, then waits for parsed `cgroup.events` `populated 0` before
accepting output or removing the jail. Threaded cgroups reject because this
profile requires domain-cgroup termination semantics.

The candidate kernel, rootfs, input image, PID 1 verifier, runtime manifest, and
replay intent now have governed identities. Two same-host kernel builds and two
same-host SquashFS builds were byte-identical. The publisher reports that a
direct unjailed Firecracker run booted the candidate, verified the retained
receipts, committed the exact 5,920-byte transcript, and exited cleanly. The
static record checker reconstructs the expected output protocol without
establishing historical execution provenance. The measured numeric resource
envelope, root-owned jailer launcher, cgroup installation, namespace lifecycle,
sandbox escape controls, and independent reproduction remain pending. The
static checker therefore keeps `replay_runner_ready=false` and every release,
settlement, production, privacy, covert-channel, and hardware-side-channel
claim false.

The pinned checker rejects evidence-only claim promotion under its reviewed
policy. A coherent repository rewrite can also change the checker, expected
digests, tests, and CI, so independent review and a separately governed
external anchor remain required for that threat.

The checker's top-level `ok` means candidate-profile integrity only. Its
`candidate_profile_integrity_ok`, `decision`, and `replay_runner_ready` fields
make that scope explicit. An operational consumer must invoke the stricter
readiness gate, which intentionally rejects this incomplete profile:

```bash
python3 tools/check_zrpf_v3_firecracker_replay_profile.py --require-ready
```

Run the static profile check on any host:

```bash
python3 tools/check_zrpf_v3_firecracker_replay_profile.py
```

Run the non-authoritative host gate where KVM is expected:

```bash
python3 tools/check_zrpf_v3_firecracker_replay_profile.py --probe-host
```

The candidate host gate currently permits only the Firecracker-validated 6.18
host-kernel family. This narrower choice ensures the required KSM cleanliness
counters are available. The gate also fails closed when KVM or required cgroup
v2 controllers are unavailable, KSM is running, residual merged or zero pages
remain, KSM zero-page merging remains enabled, swap is active, or SMT remains
enabled. The probe also records CPU vendor, family, model, microcode, and the
CPUID hypervisor flag. A present or unavailable hypervisor observation rejects
the candidate prerequisites. CPU-platform allowlisting and stronger bare-metal
attestation remain pending. Passing this gate still does not attest artifact
staging, microVM execution, network denial, or replay correctness.

### Release and settlement

Release signing, ledger admission, and settlement remain separate governed
steps. They require source-to-binary provenance, complete build inputs,
independent reproduction, semantic proof obligations, data availability,
durable atomic admission, and external authorization.

## Explicit Non-Claims

This threat model does not claim:

- guest program or guest ELF rebuild;
- image-ID recomputation from current guest source;
- proof regeneration or receipt-byte determinism;
- complete or cross-host reproducible builds;
- dependency-cache, linker, loader, kernel, or rootfs authentication; the exact
  sealed verifier bytes are authenticated for the recorded execution;
- semantic composition, descendant uniqueness, asset conservation, data
  availability, schedule correctness, or carry continuity;
- durable ledger admission, settlement, release, or production authority;
- witness privacy or zero-knowledge privacy;
- host-secret isolation;
- network isolation;
- sandbox escape resistance;
- constant-time execution;
- covert-channel freedom;
- hardware or microarchitectural side-channel resistance.

## Next Safest Steps

1. Select and hash a supported minimal guest kernel and rootfs, then measure the
   numeric CPU, memory, process, I/O, file, output, and wall-clock envelope.
2. Implement the one-shot jailer runner with stable input reads, unique jails,
   verified cgroup membership, no network, and whole-cgroup termination.
3. Run the named network, filesystem, process, timeout, and output escape probes
   under that exact runner before changing the current isolation profile.
4. Bind dependency sources, compiler, linker, runtime image, and all build
   inputs before any complete provenance or release claim.
5. Rebuild guest ELFs and recompute image IDs before a guest source-to-image
   claim.
