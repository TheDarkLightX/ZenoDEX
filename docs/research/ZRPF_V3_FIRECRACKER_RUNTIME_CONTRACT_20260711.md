# ZRPF V3 Firecracker Runtime Contract

Date: 2026-07-11
Status: bounded candidate implementation with direct local live evidence
Authority: experimental structural replay only

## Purpose

This profile runs the retained four-leaf, two-level ZRPF V3 receipt replay in a
minimal Firecracker microVM. It reduces the native replay process's access to
the host while preserving the existing receipt, image ID, journal, profile,
and mutation-control checks.

The authority sequence is:

```text
governed candidate profile
  -> governed runtime artifact manifest
  -> exact kernel, rootfs, and input-image bytes
  -> root-supplied fresh run nonce
  -> fixed 192-byte request
  -> one-vCPU Firecracker guest
  -> seven Succinct receipt verifications
  -> exact structural journal recomposition
  -> exact seal-mutation rejection
  -> fixed 16 MiB committed output
  -> strict host-side output validation
  -> scoped replay evidence
```

No step in this sequence admits a root to ZenoLedger or authorizes economic
state.

## Frozen candidate artifacts

The governed runtime manifest is
`config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v1.json`.
Its canonical SHA-256 is:

```text
cb19138eb6bb7dd404c860382e0c0f2b765d12ea8e734e9afb99caae381ff312
```

It binds these candidate artifacts:

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Amazon Linux `vmlinux` 6.1.174 | 32,217,024 | `c14602c653c76072ad17feef737edbf37e4ed3ae991148c1471a5270c9c4a94a` |
| Read-only SquashFS root | 1,024,000 | `a96822b5273e01e555b99db22c014b981d51a0c8940d9823cea4f54e9d84f59b` |
| Read-only SquashFS receipt input | 2,068,480 | `504c3a4c38e5109567d9d21f07bbc054324f3955fb4d5b07216f3c90e89e3af8` |
| Static PIE PID 1 and replay verifier | 3,366,800 | `08f99e4d6262f0028ec87a1b4fb7ee86be466244f33fce4713948dd695cec7dc` |

The guest binary has no `PT_INTERP` and no `DT_NEEDED` entries. Direct
execution outside PID 1 exits with status 125 and emits no output. The
SquashFS root contains only these paths:

```text
/
/dev
/input
/sbin
/sbin/zrpf-replay-init
```

The input image contains the exact eight retained receipt artifacts. Its
receipt-set root is:

```text
d5ecd5494318e21fa3da227409fdb5285c85ff8ae10815df5bcf0eb22fa1027f
```

## Kernel

The candidate kernel uses:

```text
repository:  https://github.com/amazonlinux/linux
tag:         microvm-kernel-6.1.174-37.345.amzn2023
tag object:  2997a6ddd99bfc73323763f2f8556b9312d554e1
commit:      3cd94355d352d212ddf85bfcd02b4cc0cbdf01c1
tree:        0dbc304b81f73446219f256481403b8c97fbc0c2
```

Firecracker's x86-64 6.1 config, Firecracker's CI config, and the ZRPF
hardening fragment are applied in that order. The resolved config SHA-256 is
`717469b88aa0e51492e4f3adad4e2dd65aa81e66a8a638c5b333de73a3b14fd5`.
Two clean builds on the same host and builder image produced byte-identical
kernel and config outputs.

The kernel enables ACPI, KVM guest support, VirtIO MMIO block devices,
devtmpfs, SquashFS with Zstd, and ELF execution. It disables loadable modules,
networking, VirtIO PCI, VirtIO network, VirtIO vsock, VirtIO RNG, user
namespaces, BPF syscalls, kexec, `/dev/mem`, and debugfs.

Firecracker's documented minimum support window for guest kernel 6.1 ends on
2026-09-02. The artifact checker rejects an evidence date after that boundary.
A future operational launcher must use a governed current date and repin when
the kernel line expires.

## Exact microVM configuration

The candidate uses Firecracker v1.16.1 with `--no-api` and a config containing
exactly these root keys:

```text
boot-source
drives
machine-config
```

Machine settings:

```text
vCPU count:         1
memory:             256 MiB
SMT:                false
dirty tracking:     false
huge pages:         None
CPU template:       None
```

Drive order and guest mapping:

| Position | ID | Guest device | Access | Purpose |
| ---: | --- | --- | --- | --- |
| 0 | `rootfs` | `/dev/vda` | read-only | SquashFS root |
| 1 | `input` | `/dev/vdb` | read-only | retained receipts |
| 2 | `output` | `/dev/vdc` | writable, exactly 16 MiB | request and committed result |

Every drive uses synchronous I/O, Writeback cache mode, 64 MiB/s bandwidth,
and 4,096 operations per second with a one-second refill period. These values
are initial candidate caps. They are not a measured production envelope.

The supplied boot arguments are:

```text
reboot=k panic=0 nomodule 8250.nr_uarts=0 i8042.noaux i8042.nomux i8042.dumbkbd swiotlb=noforce init=/sbin/zrpf-replay-init rootfstype=squashfs quiet loglevel=0 oops=panic panic_on_oops=1
```

Firecracker appends the root-device, read-only, PCI-off, and VirtIO MMIO
arguments. `panic=0` leaves a panicked guest for the host watchdog to reject.
The successful guest uses `Restart` with `reboot=k`, which follows
Firecracker's i8042 reset exit path.

## Request protocol

The root-owned launcher will create a fresh 16 MiB output object, write the
request into its first 192 bytes, flush it, and attach it as `/dev/vdc`.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | `ZRPFREQ1` |
| 8 | 2 | version 1 |
| 10 | 2 | request size 192 |
| 12 | 4 | zero flags |
| 16 | 32 | fresh run nonce |
| 48 | 32 | candidate profile canonical hash |
| 80 | 32 | runtime manifest canonical hash |
| 112 | 32 | exact input-image hash |
| 144 | 8 | output size, 16,777,216 |
| 152 | 4 | payload cap, 65,536 |
| 156 | 32 | exact replay-intent hash |
| 188 | 4 | zero reserved bytes |

The replay intent binds the expected 5,920-byte transcript and the exact input
image and receipt-set roots. Its SHA-256 is:

```text
2d43528a3a746e80437b63112f5cd8d6ca0beec1dbdc806d49f8e0437283d305
```

## Guest execution

The PID 1 guest performs these operations in order:

1. Require PID 1.
2. Open `/dev/vdc`, require its exact size, and decode the fixed request.
3. Open `/dev/vdb` and hash at most 16 MiB.
4. Require the observed input hash to equal the request.
5. Mount `/dev/vdb` read-only with `nosuid`, `nodev`, `noexec`, and `noatime`.
6. Verify all seven valid Succinct receipts and the exact seal mutation.
7. Recompose both level-one journals and the level-two journal.
8. Rehash the open input block device and require equality with the pre-replay hash.
9. Convert the verified report to the canonical CLI bytes, including one final LF.
10. Zero the output object, write the header and payload, flush, write the final commit marker, and flush again.
11. Restart through the Firecracker shutdown path.

Only `VerifiedReplayReport`, whose constructor is private to the verifier, can
enter the accepted-output writer.

## Output protocol

The output is always exactly 16,777,216 bytes:

```text
256-byte header
1..65,536-byte payload
canonical zero padding
32-byte final commit marker
```

The header binds the nonce, request hash, input hash, profile hash, runtime
manifest hash, payload size, and payload hash. The request hash transitively
binds the replay-intent hash. The marker is:

```text
SHA256("zenodex/zrpf_firecracker_output_commit/v1\0" || header || payload)
```

The marker provides a bounded completeness and atomicity check. It is an
unkeyed digest, so it does not attest to VM execution against a malicious host.
Runtime identity depends on the future root-owned launcher and stable artifact
staging.

## Local live evidence

A direct, unjailed Firecracker v1.16.1 `--no-api` run on 2026-07-11 verified:

```text
Firecracker exit code:         0
elapsed monotonic time:        697,652,562 ns
payload bytes:                 5,920
payload SHA-256:               7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288
output bytes:                  16,777,216
commit marker:                 exact
trailing zero bytes:           16,771,008
stable output read after exit: true
```

This establishes one local boot, device-mapping, SquashFS mount, receipt
verification, request/output, flush, and shutdown instance. The final governed
manifest and intent rerun is recorded in
`ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260711.json`. The
evidence record is 6,070 pretty-canonical JSON bytes with SHA-256
`abcbcf01f2f6df00f1fcc5eea5cb034fa2fc8c1edbfe0286b7d94d3ff163ece5`.
The exact 5,920-byte output payload is committed separately. The checker uses
it to reconstruct and validate the complete 16 MiB output bytes, including the
header, zero padding, marker, and output SHA-256. The checker establishes
static record integrity and internal binding. Historical VM execution
provenance remains a false claim because the raw output, executed host-path
configuration, and full local report are unpublished.

## Build and validation commands

Build both SquashFS images twice and require byte equality:

```bash
tools/build_zrpf_v3_firecracker_guest_images.sh \
  --guest-binary /trusted/input/zrpf-replay-init \
  --receipt-dir evidence/zrpf-v3-retained-structural-replay-v1/receipts \
  --output-dir /private/output/zrpf-images \
  --expected-guest-sha256 08f99e4d6262f0028ec87a1b4fb7ee86be466244f33fce4713948dd695cec7dc \
  --expected-receipt-set-sha256 d5ecd5494318e21fa3da227409fdb5285c85ff8ae10815df5bcf0eb22fa1027f \
  --expected-mksquashfs-sha256 47d5c1af3da11864e64c9dc6bb4e568719dcc315e6a744e79381ce3374fb7393
```

The helper consumes trusted private input paths. It rehashes the receipt set
before and after two byte-equality builds, but it does not provide a
descriptor-stable snapshot against a malicious local process that mutates and
restores those paths during capture. Its output carries no authority until the
resulting image sizes and SHA-256 identities exactly match the governed runtime
manifest. Complete build-input closure remains false.

Verify the resulting images explicitly:

```bash
sha256sum /private/output/zrpf-images/zrpf-replay-rootfs.squashfs \
  /private/output/zrpf-images/zrpf-replay-input.squashfs
stat --format='%n %s' \
  /private/output/zrpf-images/zrpf-replay-rootfs.squashfs \
  /private/output/zrpf-images/zrpf-replay-input.squashfs
```

The expected values are the root and input identities in the table above.

Check the governed identities and the kernel support date at evidence time:

```bash
python3 -I tools/check_zrpf_v3_firecracker_runtime_artifacts.py \
  --evidence-date 2026-07-11
python3 -I tools/check_zrpf_v3_firecracker_direct_replay_evidence.py
```

Compile a non-executable candidate plan:

```bash
python3 -I tools/check_zrpf_v3_firecracker_launch_preflight.py \
  --manifest config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v1.json \
  --expected-manifest-sha256 cb19138eb6bb7dd404c860382e0c0f2b765d12ea8e734e9afb99caae381ff312 \
  --intent config/proof_profiles/zrpf_v3_firecracker_replay_intent_v1.json
```

`--require-executable` deliberately exits nonzero. The preflight layer cannot
spawn a process, allocate a namespace, create a jail, or authorize a path for
runtime reuse.

## Current claim boundary

Established in this tranche:

- exact candidate profile and VM configuration;
- exact kernel, rootfs, input-image, and guest identities;
- same-host byte-identical kernel and SquashFS rebuilds;
- cross-language fixed request/output ABI parity;
- intent binding in the request;
- verified-report typestate before output commitment;
- one direct local Firecracker replay with clean exit and exact transcript;
- fail-closed kernel-support-date checker.

Remaining false:

- root-owned jailer launch;
- cgroup, namespace, and filesystem containment evidence;
- sandbox escape controls;
- malicious-host or hardware attestation;
- complete build-input closure;
- independent cross-host reproduction;
- complete artifact-path privacy, because generic toolchain builder paths remain;
- proof regeneration;
- semantic ZenoDEX composition;
- durable atomic ledger admission;
- data availability;
- settlement, release, and production authority;
- witness privacy, zero-knowledge privacy, covert-channel freedom, and hardware
  side-channel resistance.

## Next safest implementation step

Implement the root-owned one-shot jailer launcher around this exact contract.
It must stage immutable artifacts by stable descriptors, create a fresh nonce
and output object, install cgroup and namespace limits before execution, run
Firecracker under a watchdog, validate the exact output only after clean exit,
reap the complete cgroup, and delete the unique jail. The direct live evidence
does not substitute for those controls.
