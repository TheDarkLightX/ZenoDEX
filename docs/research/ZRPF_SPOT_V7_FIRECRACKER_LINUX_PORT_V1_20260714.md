# ZRPF Spot V7 Firecracker Linux Port V1

Date: 2026-07-14

Status: authority-false Linux composition adapter implemented; concrete
namespace-kernel effects, live privileged evidence, and every authority claim
remain unavailable

## Scope

This slice implements the concrete composition adapter behind
`SpotV7RootSupervisorOsPortV1`. The adapter may consume only the existing exact
types:

```text
CgroupCreateRequestV1
  -> CgroupLeafV1

fresh persistent network namespace mount
  -> PinnedNetworkNamespaceV1

descriptor-bound Spot V7 lifecycle handoff
  + exact cgroup leaf
  + exact pinned namespace
  -> CompletedPreparedSpotV7JailerRunV1
```

The adapter owns ordering and typed rejection. The existing cgroup module owns
the precreated domain leaf, exact numeric limits, stable descriptor identity,
process membership, whole-group kill, `populated=0`, and removal. The existing
prepared Jailer lifecycle owns the fixed argument vector, including exactly one
`--cgroup-version=2`, exactly one `--parent-cgroup`, and zero `--cgroup`
properties.

Persistent network-namespace creation, address and route inspection, unmount,
and final absence require privileged kernel operations that deterministic unit
tests cannot establish. V1 therefore injects one narrow namespace-kernel port.
The Linux composition adapter still opens the result as the existing
descriptor-pinned `PinnedNetworkNamespaceV1`, verifies exclusive process
emptiness, and passes only that exact handle into the prepared lifecycle.

## Invariants

The adapter must enforce:

1. one final, non-copyable, non-serializable adapter instance owns at most one
   cgroup and one namespace;
2. the effective UID and every trusted control UID are root before effects;
3. the cgroup object is exactly the leaf returned from the exact requested
   parent, leaf name, limits, and trusted paths;
4. the namespace path equals the requested root plus the same bounded jail ID;
5. cgroup path/inode, domain type, empty process and descendant sets, and every
   numeric limit are checked before execution;
6. namespace path/inode, exclusive process emptiness, and an empty address and
   route inventory are checked before execution;
7. the exact descriptor-retained request supplied by the handoff is the only
   accepted request;
8. once live lifecycle execution begins, success or failure consumes the one
   lifecycle attempt;
9. the supervisor timeout begins as a bounded integer number of nanoseconds;
   the inherited lifecycle API receives a derived floating-point number of
   seconds as operational input and creates no authority from that conversion;
10. cgroup teardown either kills and removes the exact leaf or confirms through
   the descriptor-safe cgroup boundary that the exact lifecycle already removed
   it after natural completion;
11. namespace destruction occurs only after exclusive emptiness, and absence is
    checked after unmount;
12. no command is interpreted by a shell;
13. every result and observation remains ordinary authority-false data.

## Disaster-state ownership

| Disaster state | Closure in this slice |
| --- | --- |
| missing or substituted cgroup parent | descriptor-safe cgroup-v2 creation and exact path binding reject |
| Jailer creates an ungoverned child cgroup | fixed prepared launch emits zero `--cgroup` properties; existing argv validator rejects substitutions |
| resource limit changes before launch | `CgroupLeafV1.verify_prelaunch` checks every exact file value |
| namespace path swap | `PinnedNetworkNamespaceV1.reverify_path` checks the retained inode |
| namespace contains a process, address, or route | exact process-set check plus injected kernel inventory check reject |
| caller substitutes request bytes | equality with the descriptor-retained request rejects before execution |
| lifecycle times out or leaves descendants | existing lifecycle and supervisor use whole-cgroup teardown; uncertain teardown rejects and quarantines |
| natural lifecycle already removed the cgroup | idempotent success requires descriptor-safe absence of the exact requested leaf |
| namespace unmount fails | absence remains unverified, the supervisor returns teardown uncertainty, and no result exists |

## Evidence plan

Deterministic tests must cover the successful exact composition and active
distinguishing witnesses for:

- non-root effective UID and non-root trusted UID;
- substituted cgroup and namespace objects;
- wrong cgroup relative path or changed numeric limit;
- wrong namespace path, process membership, address, or route;
- request substitution and Boolean timeout substitution;
- lifecycle rejection;
- whole-cgroup kill/removal and the exact already-absent natural-completion
  case;
- namespace destroy and absence failures;
- adapter copy, serialization, reuse, and out-of-order calls;
- zero Jailer `--cgroup` property construction.

Coverage in this lane means that every acceptance-relevant representation
choice has an active distinguishing witness. Same-value replacement objects,
Boolean-as-integer timeouts, position-distinct request bytes, changed paths,
changed limits, and changed teardown outcomes must each alter acceptance at a
named boundary. Round-trip survival or field presence alone is insufficient.

The required ZRPF workflow must run Ruff, mypy, and the focused tests for this
module.

## Exact non-claims

This slice does not establish live root ownership, live namespace creation,
live address or route inspection, live cgroup membership, live Jailer or
Firecracker execution, runtime authority, release authority, settlement
authority, production authority, sandbox escape resistance, same-UID
resistance, hardware attestation, side-channel resistance, covert-channel
freedom, current V6/V7 proof identity, or integer-exact timeout enforcement at
the lower lifecycle boundary.

The next evidence step is an opt-in run on a disposable privileged KVM host
using a separately reviewed concrete namespace-kernel implementation. Until
that run and its negative controls are retained and independently checked, all
live and authority claims stay false.
