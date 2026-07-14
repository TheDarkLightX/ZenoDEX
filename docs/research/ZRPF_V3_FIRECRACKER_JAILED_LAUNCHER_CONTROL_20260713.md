# ZRPF V3 Firecracker Jailed Launcher Control

Date: 2026-07-13

## Scope

Firecracker is the primary native replay isolation target for ZRPF. The
existing governed direct Firecracker replay remains unchanged. That retained
lane reports one direct, unjailed Firecracker run with an exact 5,920-byte
verified replay payload carried by the fixed 16 MiB output-device protocol.
Its historical execution provenance and sandbox authority remain false.

Docker is used for hermetic source builds and required CI replay. It is not a
replacement for the native Firecracker boundary.

This tranche adds the process-control portion of a future root-owned jailed
Firecracker runner. It does not execute the retained replay or promote any
authority claim.

The 2026-07-14 follow-up adds descriptor-retained, supervisor-prepared jail
staging and an outer request/output-bound lifecycle. Its exact V7 frontier is
recorded in
`ZRPF_SPOT_V7_ROOT_OWNED_FIRECRACKER_RUNNER_FRONTIER_20260714.md`.

## Implemented control

The new control implements and tests this bounded sequence:

```text
validate finite cgroup limits
  -> create one fresh cgroup-v2 domain leaf
  -> install and read back every numeric limit
  -> require empty process and descendant sets
  -> bind root-owned Firecracker and Jailer executable identities
  -> bind one nsfs network-namespace identity
  -> construct the exact Jailer argument vector
  -> pass --cgroup-version=2 and --parent-cgroup
  -> pass zero Jailer --cgroup properties
  -> request new PID namespace and the bound network namespace
  -> spawn with an empty environment and closed inherited descriptors
  -> reverify executable and namespace identities
  -> verify the exact cgroup descendant set and netns membership
  -> treat Jailer-parent exit as PID-namespace launch handoff
  -> wait for Firecracker to leave the cgroup naturally
  -> on timeout or failure, write cgroup.kill and reap the Jailer parent
  -> on successful completion, require cgroup.events populated=0 without kill
  -> require no remaining process or descendant
  -> remove the exact fresh leaf
```

The finite resource envelope binds:

- `cpu.max`;
- `cpuset.cpus` and `cpuset.mems`;
- one exact `io.max` row;
- `memory.high`, `memory.max`, and `memory.swap.max`;
- `memory.oom.group=1`;
- `pids.max`;
- Jailer `fsize=16777216` and a bounded file-descriptor limit.

All cgroup and trusted-path operations use descriptor-relative access,
`O_NOFOLLOW`, stable device/inode checks, bounded reads, and exact readback.
An existing leaf is rejected rather than reused. The Jailer command rejects
every `--cgroup` and `--cgroup=...` form so that Jailer cannot create an
ungoverned child below the preconfigured leaf.

The pinned Firecracker v1.16.1 Jailer source defines the relied-on attachment
behavior in
[`src/jailer/src/env.rs`](https://github.com/firecracker-microvm/firecracker/blob/v1.16.1/src/jailer/src/env.rs):
with cgroup v2 and no `--cgroup` properties, it writes its PID to the existing
`--parent-cgroup` leaf. A missing parent is not itself fatal in Jailer, so this
control precreates the leaf and requires exact post-spawn membership. The same
source derives the jail target as
`<chroot-base>/<exec-file-name>/<jail-id>/root`; the concrete candidate entry
verifies the root-owned base chain and rejects a pre-existing exact jail ID.

## Executed evidence

The new tranche has deterministic unit and fake-filesystem evidence for:

- fresh-leaf creation and exact limit readback;
- stale leaf, control symlink, and path replacement rejection;
- exact process membership and descendant-tree enforcement;
- rejection of unexpected or non-descendant processes;
- exact Jailer arguments with no cgroup property;
- executable mutation and replacement rejection;
- nsfs path and per-process network-namespace binding;
- spawn, placement, timeout, and teardown failure cleanup;
- the literal `1\n` cgroup-kill write, `populated=0`, and leaf removal;
- natural cgroup completion and removal with no successful-path cgroup kill;
- the `--new-pid-ns` Jailer-parent/Firecracker-child lifetime regression;
- granular authority fields remaining false.

This is code-level control evidence. It is not a live privileged jailed replay.
The bounded mutation atlases are offline bug-discovery evidence, not a
correctness proof.

## Live-host limitation

The current development host exposes `/dev/kvm`, and the governed Firecracker
and Jailer binaries are present. Their local bytes match the governed sizes and
SHA-256 identities:

```text
Firecracker  3527456 bytes  2fd0171309af7e24cf8dafc8a6f921c1434c49b5f9349bb996b7ed0a4deb8aa7
Jailer       2181264 bytes  1f3a0c1fe86212d0001819bfe0819071c01208b3ccc9398c3b3bc1b84cf21edd
```

Those local files are user-owned and do not satisfy the future root-owned
staging contract. The current user also cannot create the required leaf under
`/sys/fs/cgroup`, and passwordless noninteractive sudo is unavailable. A
truthful live run of the new root-owned control therefore was not possible on
this host.

## Explicit non-claims

The following remain false:

- live root-owned launcher verification;
- live Jailer and Firecracker execution under this control;
- live cgroup limit and membership verification;
- live empty network-namespace verification;
- live descriptor-bound execution handoff from the supervisor into Jailer;
- live descriptor-bound chroot-base and stale-jail evidence;
- an independently supervised crash-cleanup watchdog;
- live root-owned immutable artifact staging evidence;
- final Spot V7 configuration, guest, and payload integration;
- sandbox escape resistance;
- hardware side-channel resistance;
- covert-channel freedom;
- replay authenticity or historical execution provenance;
- release authority;
- settlement authority;
- production authority;
- zero-knowledge privacy.

The direct unjailed replay remains functional evidence. It does not acquire
these stronger claims from the existence of the new launcher code.

## Next executable promotion step

Run the control on a disposable privileged host with the pinned Firecracker and
Jailer bytes. The run must create a fresh network namespace, stage the kernel,
rootfs, request, input, output, and exact configuration from stable root-owned
descriptors, execute the exact Jailer command, validate the fixed output
protocol, exercise hostile negative controls, tear down the complete cgroup and
namespace, and retain the raw signed run record. Claim promotion remains
disabled until that evidence is independently checked.
