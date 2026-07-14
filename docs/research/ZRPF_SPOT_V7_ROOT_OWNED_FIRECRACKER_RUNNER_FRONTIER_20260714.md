# ZRPF Spot V7 Root-Owned Firecracker Runner Frontier

Date: 2026-07-14

Status: descriptor-retained jail staging and a data-only prepared-Jailer
lifecycle are implemented; Spot V7 runtime authority remains unavailable

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
  -> canonical 192-byte request at offset zero
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

The public prepared lifecycle in
`tools/zrpf_v3_firecracker_jailer_launcher.py` requires exact concrete pinned
Jailer, Firecracker, cgroup, network-namespace, and prepared-root types. It
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
Spot V7 PID-1 guest init and three-file input image
Spot V7 governed raw output profile and verified writer
Spot V7 governed runtime manifest and exact artifact set
```

The retained V3 replay guest is not a Spot V7 guest. Its raw profile digest and
`VerifiedReplayReport` output contract cannot be relabeled as V7 authority.
The current generic stage validates canonical resource paths and the outer
request/output protocol. It does not validate a final Spot V7 machine profile,
guest payload, receipt, release manifest, or source-to-binary chain.

The high-level root supervisor also still needs to own creation and final
destruction of the fresh network namespace and preconfigured cgroup leaf.
Those controls exist separately; this tranche consumes exact live handles and
does not claim that the complete allocation owner is implemented.

## Non-claims

This tranche does not establish:

```text
live privileged Jailer or Firecracker execution
live hostile staging or same-UID resistance evidence
complete Spot V7 runtime artifact identity
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

1. Define a Spot V7-specific governed raw request/output profile without
   inheriting the retained structural V3 report type.
2. Build the static PID-1 Spot V7 guest init and deterministic three-file input
   image builder.
3. Freeze the V7 runtime manifest and exact kernel, rootfs, guest-init, input,
   Firecracker, and Jailer identities.
4. Add one root supervisor that creates the cgroup and network namespace,
   prepares the jail, runs the exact lifecycle, and destroys all three only
   after verified emptiness.
5. Run privileged hostile controls on a disposable KVM host.
6. Decode and authenticate the exact V7 payload inside that lifecycle. Only
   then may the module-private governed execution capability gain a mint site.

No long RISC0 proof run is needed for steps 1 through 4. Fresh proof evidence
belongs after the final V6/V7 guest source closure is frozen.
