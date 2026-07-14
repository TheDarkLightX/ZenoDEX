# ZRPF Spot V7 Root Supervisor Contract V1

Date: 2026-07-14

Status: authority-false imperative-shell contract and Linux composition adapter
implemented; concrete namespace-kernel effects and live evidence pending

## Scoped result

The V1 supervisor spends one descriptor-sourced Spot V7 launch capability and
enforces this order:

```text
sealed descriptor launch
  -> exact staged request decode
  -> cgroup-v2 leaf allocation
  -> network-namespace allocation
  -> prelaunch identity, limit, emptiness, and route checks through the OS port
  -> existing prepared Spot V7 Jailer lifecycle
  -> independent exact request-bound output validation
  -> whole-cgroup terminate-or-confirm-absent operation
  -> cgroup absence
  -> network-namespace emptiness
  -> namespace destruction and absence
  -> snapshot and executable descriptor cleanup
```

The supervisor retains the request from the sealed staged jail. It does not
accept a second caller-provided request. After the lifecycle returns, it checks
the full fixed-size output with
`validate_exact_committed_output_v1`. A port-supplied output with a stale nonce,
wrong request hash, changed commit marker, malformed payload, or nonzero trailing
region therefore rejects before a result exists.

The result is sealed, immutable, non-copyable, and non-serializable. It exposes
only the bounded V7 payload and fixed identities. These properties remain
false:

```text
live_execution_verified
live_ownership_verified
governed_cgroup_parent_verified
governed_cgroup_resource_policy_verified
governed_network_namespace_root_verified
runtime_authority
settlement_authority
release_authority
production_authority
```

## OS port contract

The injected port owns privileged effects. It must:

1. create the exact fresh cgroup leaf under the requested cgroup-v2 parent;
2. create the exact fresh network namespace under the requested root;
3. require the cgroup path/inode, domain type, empty descendant set, exact
   limits, and empty process set before launch;
4. require the namespace path/inode, exclusive empty membership, no configured
   addresses, and no routes before launch;
5. invoke the existing prepared Spot V7 lifecycle using the exact retained
   Jailer, Firecracker, prepared jail, cgroup, and namespace handles;
6. use whole-cgroup termination after timeout or failed completion;
7. require cgroup absence and namespace emptiness before namespace destruction;
8. require the namespace mount path to be absent after destruction.

The supervisor invokes the whole-cgroup termination operation on every path
that allocated a cgroup, including after a lifecycle returned successfully or
returned an output that later failed independent validation. A concrete port
may treat an already removed cgroup as an idempotent success only after it
verifies that the exact allocated path is absent.

Injected deterministic ports establish orchestration, reject precedence, and
cleanup ordering. They do not establish that a real kernel performed those
operations. `LinuxSpotV7RootSupervisorOsPortV1` now returns the exact existing
`CgroupLeafV1` and `PinnedNetworkNamespaceV1` controls and calls
`run_prepared_spot_v7_jailer_process_control_v1`. Persistent namespace
creation, route/address inventory, destruction, and absence remain behind a
narrow privileged-kernel port. A separately reviewed implementation and
privileged hostile-run evidence are required before any live claim changes.

## Disaster-state closures

| Disaster state | V1 closure |
| --- | --- |
| descriptor/path substitution | sealed descriptor handoff re-verifies snapshot and executables before allocation |
| prepared launch reused | one-shot handoff is spent before effects begin |
| cgroup absent or moved | port must reject before launch; stable adversarial tests cover both cases |
| numeric resource limit changes | prelaunch port check rejects; existing concrete cgroup control rechecks limits during membership and teardown |
| namespace mismatch, address, or route | prelaunch port check rejects; no fallback namespace exists |
| stale nonce or forged output marker | independent exact output validation rejects |
| timeout or remaining descendant | whole-cgroup termination plus absence check precedes file cleanup |
| teardown uncertainty | result is unavailable, capability is spent, and staged files remain quarantined |
| caller report claims authority | reports are hashed as ordinary observations only; every result authority property is constant false |

The V1 plan supplies the cgroup mount, parent, trusted UID, numeric limits, and
namespace root as bounded caller input. No governed release policy authenticates
those values yet. The corresponding governed-policy and live-ownership fields
remain false in every result.

## Evidence

Focused deterministic tests cover:

- exact successful operation order;
- cgroup absence, identity movement, and altered limits;
- namespace identity mismatch and a present route;
- descriptor snapshot mutation and capability reuse;
- lifecycle timeout and surviving-process rejection;
- stale nonce and forged output commit;
- cgroup and namespace teardown failures;
- Boolean substitution for a timeout;
- sealed result mutation, copying, and serialization.

Replay command:

```bash
python3 -m pytest -q \
  tests/test_zrpf_spot_v7_firecracker_linux_port.py \
  tests/test_zrpf_spot_v7_firecracker_root_supervisor.py \
  tests/test_zrpf_v3_firecracker_cgroup_v2.py \
  tests/test_zrpf_spot_v7_firecracker_descriptor_staging.py
```

## Non-claims and next evidence

This slice does not establish live cgroup ownership, live network-namespace
creation, live descendant membership, Jailer or Firecracker execution, sandbox
escape resistance, same-UID resistance, hardware attestation, current V6/V7
proof identities, governed release selection, settlement, or production
readiness. The supervisor retains a bounded integer-nanosecond timeout, while
the inherited lifecycle API receives floating-point seconds. That operational
conversion carries no deterministic timing or authority claim.

The next safe step is a concrete root-only namespace-kernel implementation
followed by an opt-in run on a disposable KVM host. That run must retain exact
cgroup files before, during, and after execution, namespace mount identity and
network inventory, the canonical request and output, the exact
Jailer/Firecracker command, and failure controls for timeout, surviving
descendants, namespace routes, and teardown failure.
