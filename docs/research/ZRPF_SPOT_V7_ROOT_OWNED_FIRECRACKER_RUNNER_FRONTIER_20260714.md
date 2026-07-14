# ZRPF Spot V7 Root-Owned Firecracker Runner Frontier

Date: 2026-07-14

Status: descriptor-retained jail staging, the data-only prepared-Jailer
lifecycle, and exact authority-false Spot V7 config/manifest identity binding
are implemented; Spot V7 runtime authority remains unavailable

## Purpose

The Spot V7 production path needs one supervisor-owned lifecycle that binds the
governed runtime artifacts, fresh request, Firecracker execution, committed
output, teardown, and authenticated Spot V7 payload. Static JSON reports and
publisher assertions cannot create that authority.

Firecracker v1.16.1 Jailer creates
`<chroot-base>/<exec-name>/<jail-id>/root` and leaves an existing directory in
place. Its configuration and VM resources must already exist inside that root.
The operator is part of the trusted computing base and is responsible for
resource ownership and permissions. See the pinned
[`Jailer documentation`](https://github.com/firecracker-microvm/firecracker/blob/v1.16.1/docs/jailer.md)
and
[`Jailer implementation`](https://github.com/firecracker-microvm/firecracker/blob/v1.16.1/src/jailer/src/env.rs).

This means a correct one-shot runner must distinguish two cases:

```text
unknown pre-existing jail ID
  -> reject and preserve for investigation

supervisor-created unique jail ID with retained descriptors
  -> stage exact resources
  -> hand that same root to Jailer
```

Rejecting every pre-existing root after the supervisor has prepared its own
root makes `--config-file` execution impossible. Reusing an untrusted root
creates a path-substitution boundary. The new sealed prepared-root type carries
the distinction in process-local state.

## Implemented bounded slice

`tools/zrpf_v3_firecracker_jail_staging.py` now provides a data-only staging
capability with these checks:

```text
root-owned trusted directory chain
  -> fresh O_EXCL jail ID
  -> exact root/resources inventory
  -> stable source descriptors
  -> bounded copy plus source and staged SHA-256 checks
  -> root-owned read-only kernel, rootfs, input, and config
  -> runtime-owned fixed 16 MiB output
  -> canonical retained-V3 192-byte or Spot-V7 224-byte request at offset zero
  -> all remaining output bytes zero
  -> retained directory and resource descriptors
  -> prelaunch inode, mode, owner, link-count, size, and version checks
```

The canonical Firecracker configuration must bind exactly these paths:

```text
/resources/kernel
/resources/rootfs
/resources/input
/resources/output
```

The Spot V7-specific prepare path additionally requires one validated proposal
that retains the exact canonical machine configuration and runtime-manifest
bytes. The 224-byte raw request must commit their exact SHA-256 identities and
the staged input-drive identity before any jail directory is created. The
sealed prepare observation and canonical finish observation both retain the
exact proposal and its profile, request, config, and manifest hashes. Every
authority field remains false because no governed release has selected those
proposal bytes.

The shared prepared lifecycle in
`tools/zrpf_v3_firecracker_jailer_launcher.py` and the V7 identity layer in
`tools/zrpf_spot_v7_firecracker_jailer_lifecycle.py` require exact concrete
pinned Jailer, Firecracker, cgroup, network-namespace, and prepared-root types. They
requires root ownership, checks that launch parameters match the staged jail,
executes the existing live placement controls, reaps the short-lived Jailer
parent, waits for the Firecracker cgroup to become naturally empty, reads output
only after the empty cgroup has been removed, validates the request-bound outer
commit protocol through the retained output descriptor, and then removes the
jail.

With `--new-pid-ns`, Firecracker v1.16.1 clones the Firecracker child and the
original Jailer process exits after recording the child PID. Jailer-parent exit
therefore records launch handoff only. It is not VM completion. The runner does
not issue `cgroup.kill` on the accepted path. It uses whole-cgroup kill only
after timeout or a failed completion check.

If launch or teardown becomes uncertain, the jail remains quarantined. A
prelaunch rejection may remove the never-executed stage. The returned
`CompletedPreparedJailerRunV2` is ordinary data and carries no verifier,
settlement, or production authority.

## Evidence

Deterministic tests cover:

- exact resource inventory and fresh output;
- mutation of the original source after capture;
- staged resource mutation and same-byte path replacement;
- stale jail rejection without deletion;
- config path substitution;
- Spot V7 machine-config and runtime-manifest substitution before staging;
- stale Spot V7 runtime-profile identity and legacy 192/256 framing;
- post-prepare same-byte config-path replacement;
- config or manifest substitution in retained finish evidence;
- nonzero stale output and uncommitted output;
- stable committed-output validation through the retained descriptor;
- launch-before-read and teardown-before-cleanup ordering;
- Jailer-parent exit followed by child lifetime, natural cgroup completion, and
  output read without a successful-path `cgroup.kill`;
- prelaunch abandonment and uncertain-launch quarantine;
- non-copyable, non-serializable, immutable prepared capability;
- rejection of injected control doubles at the public runner entry.

The privileged ownership check is explicitly opt-in:

```bash
ZENODEX_RUN_PRIVILEGED_ZRPF_FIRECRACKER_STAGING=1 \
python3 -m pytest -q \
  tests/test_zrpf_v3_firecracker_jail_staging.py::test_privileged_root_owned_staging_uses_distinct_runtime_owner
```

This command checks staging ownership only. It does not boot a VM or advance an
authority claim.

## Exact blockers retained

The sealed Spot V7 Firecracker capability still has no production mint site.
The authority frontier now records these V7-specific missing inputs in addition
to the existing release, execution, teardown, and store blockers:

```text
governed release selection of the exact V7 runtime proposal
authority-capable PID-1 receipt verification
fresh V6/V7 receipt evidence under the final release source closure
```

The retained V3 replay guest is not a Spot V7 guest. Its raw profile digest and
`VerifiedReplayReport` output contract cannot be relabeled as V7 authority.
The V7 path now validates the exact proposed machine profile, runtime manifest,
input identity, and outer request/output protocol. It does not authenticate a
guest payload or receipt, prove that governance selected the proposal, bind a
release manifest, or establish a source-to-binary chain.

The high-level root supervisor also still needs to own creation and final
destruction of the fresh network namespace and preconfigured cgroup leaf.
Those controls exist separately; this tranche consumes exact live handles and
does not claim that the complete allocation owner is implemented.

## Non-claims

This tranche does not establish:

```text
live privileged Jailer or Firecracker execution
live hostile staging or same-UID resistance evidence
governed Spot V7 release artifact identity
Spot V7 guest execution or payload authentication
current V6/V7 image IDs or receipt evidence
source-to-binary or cross-host reproducibility
hardware attestation
data availability or finality
atomic economic settlement authority
release or revocation authority
sandbox escape resistance
hardware side-channel resistance
covert-channel freedom
production readiness
```

## Next safe implementation order

1. Freeze and govern the V7 runtime manifest and exact kernel, rootfs,
   guest-init, input, Firecracker, Jailer, machine-config, and raw-profile
   identities.
2. Replace the protocol-only PID-1 path with an authority-capable guest that
   verifies the exact V6/V7 receipts and derives the authenticated payload.
3. Add one root supervisor that creates the cgroup and network namespace,
   prepares the jail, runs the exact lifecycle, and destroys all three only
   after verified emptiness.
4. Run privileged hostile controls on a disposable KVM host.
5. Decode and authenticate the exact V7 payload inside that lifecycle. Only
   then may the module-private governed execution capability gain a mint site.

No long RISC0 proof run is needed for steps 1 and 3. Fresh proof evidence
belongs after the final V6/V7 guest source closure is frozen.
