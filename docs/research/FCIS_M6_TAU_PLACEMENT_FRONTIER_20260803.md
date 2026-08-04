# FCIS M6 Tau Placement Frontier

Status: `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`

## Result

The latest observed Tau source can carry more of ZenoDEX's formal policy layer
than the repository's older embedded binary. It now executes direct bit-vector
stream arithmetic, including `bv[256]`. Compact Boolean admission and writer
state-machine relations also execute reliably.

The practical boundary remains narrow. Full-width arithmetic with the overflow
guard required by accounting exceeded the 30-second execution budget. The
existing perps risk relation exceeded both a 30-second campaign budget and a
60-second one-step budget. Tau is therefore suitable for small exact admission
relations and cached proof qualification at this checkpoint. Rust remains the
execution layer for global state, U256 accounting, concurrency, persistence,
and high-frequency market transitions.

## Exact upstream identity

```text
origin:          https://github.com/IDNI/tau-lang
source commit:   c43c66b84966aac0e2830aa778dfda79b2857608
source tree:     01829511c6961cde5b6121bb1cf205f106de9203
parser commit:   ec62e2b78c342c9265876fc6edbadc82806ee493
version:         Tau Language Framework version 0.7.0-alpha (c43c66b8)
binary SHA-256:  588ebf63dfbcf5101b30e02d149678143cbcb89e60e51e0aa8bed0f9d716b157
```

The upstream remote head was rechecked at that commit on 2026-08-03. The
release suite passed 316 of 316 tests. A debug build was excluded because the
host had less than 4 GiB free.

## What moved into Tau

Seven new relations define the substrate-independent continuity boundary:

1. exact Tau-profile compatibility;
2. per-operation Tau, ZenoLedger, or reject-or-pend disposition;
3. steady single-writer operation;
4. entry into quiescence;
5. activation of one writer from quiescence;
6. emergency Tau-to-ZenoLedger failover;
7. composition of the complete M6 value-safety certificate.

The emergency guard requires a precommitted permit, accepted finalized
checkpoint, current ZenoLedger ancestry, no in-flight publication, old-writer
revocation, epoch advance, cross-source parity, and an independently verified
fact that split-brain spending and dual issuance are impossible.

These inputs are verifier-owned facts. The Tau relations combine them and do
not establish source authenticity, currentness, cryptographic validity,
durability, or inventory completeness.

The global closure's first input means that the candidate decision is exactly
`Accept`. A request alone cannot satisfy the closure. Rejection purity remains
a separate verified relation, so a rejected outcome cannot be relabeled as an
accepted candidate.

## Runtime profile receipt refinement

The compact Tau relations now have an unmounted Python refinement. A public
`TauIntegrationProfileV1` is a canonical source and semantics description. It
grants no authority. A verifier-selected adapter may produce a
`TauIntegrationProfileReceiptV1` only after checking evidence bound to the
exact:

```text
promotion subject
current state
deployment configuration
authority epoch
profile, governance, and rule-history roots
required capability set
refinement root
verifier profile
```

The receipt is constructed through a module-controlled path, registered at
creation, and completely revalidated at each use. Negative observations such
as unavailable, changed, equivocal, or incompatible remain valid observation
receipts with `profile_usable = false`. A purported `verified_compatible`
observation rejects when any required profile fact is missing or crossed.

Operation disposition consumes the receipt-derived status. There is no
caller-supplied `profile_usable` field. The complete typed projection into the
14-input Tau relation is differentially tested against the exact pinned Tau
binary for Tau, ZenoLedger, and reject-or-pend branches. A valid reject-or-pend
decision explicitly carries `authorizes_execution = false`. The verifier-owned
disposition context also commits the expected operation root; crossed operation
evidence rejects before a decision is created.

`TauWriterProfileBindingV1` binds one usable receipt to an exact writer-profile
root, current-state root, deployment configuration, and authority epoch. It is
only a target-binding bridge. It is not a J07 writer token, commit capability,
or mounted writer-selection result.

## Substrate-neutral J07 writer eligibility

J07 writer-token issuance now consumes a substrate-neutral
`WriterProfileEligibilityReceiptV1`. Its canonical claim binds the exact:

```text
promotion subject
source schema, receipt, and binding roots
writer profile
J07 authority context
current state and deployment configuration
authority epoch and authority-state root
expected head and snapshot
eligibility policy
```

The claim is public canonical data and grants no authority. The module invokes
a shell-selected verifier with every expected field and requires exact `True`
before creating a registered receipt. The receipt and its complete claim are
revalidated at token issue and use.

The J07 writer-token language is now version 2. A token commits the eligibility
receipt, promotion subject, eligibility policy, writer profile, exact J07
context, epoch, authority state, head, snapshot, and migration-token root. The
old context-plus-profile V1 mint function remains only as a fail-closed
compatibility tombstone. It always rejects with an eligibility-required error.
No token is produced for a disabled writer, an unregistered receipt, claim data
without verifier provenance, crossed eligibility, or stale authority context.

`verify_tau_j07_writer_profile_eligibility_v1` refines the existing registered
Tau profile receipt and Tau writer binding into the neutral eligibility
language. It requires a usable Tau profile, exact source/binding agreement,
the active and target J07 writer, and matching state, deployment, and epoch.
It produces the neutral receipt only after the selected eligibility verifier
accepts. J07 does not import Tau-specific types.

The retained canonical vector is:

```text
source schema root: 931312071fb68f1bc102ba264e3a1f281b51ea64a5654c4ff02d04143d7d399a
Tau profile receipt: 1519c5bf5336cd8f9e6731a76beffedaa6283b810f401fef8094442e85a291a1
Tau writer binding:  6968f4cf61abe60c4b95426907640a2a69d0f7877f354f34a537c4bf1b7be1ff
eligibility claim:   2a63c540ec16214e5e2e5c93b892c9a16c2047d5c7764eca518b2e19651e0032
eligibility receipt: 57e88f7ce9bfbba52f0417e733eda345f7495a2c6f6d4a4732a66b619e881553
J07 V2 token:        a9cb54f3ac9a370c2ae9fc2592dc422978d8e9bd5b463814faa48ecbfa19ef7e
```

Verifier selection and authentication remain imperative-shell premises. The
module registries provide nominal in-process provenance and tamper detection.
They do not prove cryptographic verifier identity, store currentness, deployed
inventory completeness, or no-bypass. A mounted design still needs one
state-bound eligibility-policy/verifier registry in the promotion subject and
the unique publication capability.

The Python construction boundary provides nominal in-process provenance and
tamper detection. It is not cryptographic authenticity. Selection and
authentication of the external verifier, datastore currentness, strict wire
decoding, and mounted no-bypass remain open.

## Correct substrate model

The governing relation is:

```text
ZenoDEX behavior
  = platform-independent ZenoDEX constitution
  + verified capabilities of the active substrate profile
```

Tau is preferred when the exact profile is verified compatible. ZenoLedger is
available for operation classes with a proved continuity relation. A Tau-native
asset operation without a safe-exit and single-issuer proof must reject or
remain pending.

This yields operation-specific degradation:

| Operation | Tau unavailable |
| --- | --- |
| ZenoDEX-native accounting with current ZenoLedger ancestry | Continue on ZenoLedger |
| Tau computation with a retained portable certificate | Continue only after local certificate verification |
| Fresh Tau governance or an unreviewed Tau rule change | Retain the last adopted ZenoDEX semantics and disable dependent features |
| Tau-native asset movement without a safe-exit proof | Reject or pend |
| Tau-native asset movement with a closed safe-exit and single-issuer proof | Eligible for the emergency writer guard |

## Measured execution frontier

The 64-step resource campaign under the exact binary produced:

| Relation | Elapsed | Per step | Result |
| --- | ---: | ---: | --- |
| resource budget | 1.056 s | 16.50 ms | within budget |
| artifact binding | 0.919 s | 14.36 ms | within budget |
| load shedding | 2.310 s | 36.09 ms | within budget |
| swap execution regret | 1.567 s | 24.49 ms | within budget |
| perps risk envelope | 30.070 s | n/a | timeout |

Additional probes found:

* `bv[8]` stream addition produced `3` for `1 + 2` under the new binary. The
  repository's previous embedded binary failed to produce the output.
* `bv[256]` stream addition produced `3` for `1 + 2` and `0` for
  `max_u256 + 1`. This confirms modular semantics.
* Adding an explicit non-wrap check to the `bv[256]` execution relation caused
  a two-step probe to exceed 30 seconds.

The measured conclusion is narrow: expression support has improved, while
guarded U256 accounting and branch-heavy risk logic remain outside the
qualified hot path.

The existing per-spec profile registry still contains historical observations
from Tau `401d756b`. Those entries are not evidence that the same relations are
qualified under `c43c66b8`. This checkpoint preserves them as historical
evidence and requires per-spec requalification before any runtime-admission
status changes.

## Source-level limits

The exact source declares or exhibits these boundaries:

* functional quantifiers `fall` and `fex` are parsed and preserved but are not
  evaluated;
* pointwise revision can leave immediate post-update outputs unspecified when
  the new rule has lookback;
* recurrence and satisfiability fixpoint searches have 500-step bounds;
* one eventual-flag path returns `F` after a bounded failure while explicitly
  stating that the result is not a proof of unsatisfiability;
* minterm search can enumerate `2^vars` combinations without a resource budget;
* the public API is highly unstable and assumes serialized, single-threaded
  access;
* efficient tables and data storage remain future work;
* the build may fetch doctest from `master` and uses dependency tags for
  unordered_dense and FTXUI.

For ZenoDEX, every Tau error, timeout, bounded-failure diagnostic, unsupported
operation, or unknown profile must be treated as indeterminate and fail closed.

## Placement decision

Use Tau for:

* pinned profile and governance compatibility;
* compact capability and proof-context gates;
* writer phase transitions and one-writer exclusion;
* small conjunctions composing independently verified facts;
* bounded policy relations with retained resource receipts.

Use Rust for:

* the immutable canonical global-state carrier;
* dynamic maps, canonical codecs, roots, signatures, and hashing;
* U256 transition arithmetic and overflow checks;
* atomic publication, concurrency, recovery, networking, and outbox effects;
* high-frequency swaps, liquidations, and perpetuals execution.

Use Lean for parametric preservation and composition theorems. Use ESSO or an
equivalent dual-solver finite model for bounded adversarial state machines. Use
ZRPF to scale proof generation and verification after the semantics and
runtime refinement are closed.

## Runner and updater hardening

The integration shell now rejects Tau's ANSI-colored `(Error)` diagnostic even
when Tau exits with status zero. Spec-mode parsing accepts assignments from
stdout only, rejects duplicate assignments, and enables experimental Tau
features only through an explicit flag. The same diagnostic predicate is used
by the formal-completeness checker.

The updater now resolves an origin remote-tracking ref or full reachable commit
into a detached checkout. It verifies full root and parser pins, both origin
URLs, parser gitlink identity, clean nested worktrees, source/build path
containment, binary version, and binary SHA-256. Build parallelism defaults to
four jobs and rejects values outside `1..16`.

The integrated tooling evidence passed:

```text
31 runner and updater tests
Ruff
targeted strict mypy
Bash syntax
```

The updater's full real build was not repeated after integration because the
host had less than 4 GiB free. The independently built exact c43 binary and its
316-test upstream release result remain the retained binary evidence.

## Evidence and nonclaims

The focused ZenoDEX suite passed:

```text
12 placement tests passed
26 Tau-profile receipt, disposition, writer-binding, and exact-Tau parity tests passed
22 related Tau/ZenoLedger runtime-projection tests passed
234 recommended Tau specifications passed formal-plan and semantic-view checks
```

The writer-eligibility continuation additionally passed:

```text
6 substrate-neutral eligibility tests
19 J07 switch, issuance, use, mutation, and property tests
7 Tau-to-J07 refinement and canonical-vector tests
78 related focused tests passed; 14 exact-Tau parity cases skipped because the
pinned Tau binary was unavailable in this sparse worktree
Ruff, formatting, targeted strict mypy, Python compilation, and the J07 vector checker
security red-flag scan: 0 high, 0 medium, 0 low findings
```

This packet does not mount the relations, establish the authenticity of any
Tau observation or verifier, authorize a writer switch, create a zDEX escape
mechanism, prove runtime forward simulation, or complete M6. The 31 runner and
updater tests and the upstream 316-test Tau release receipt remain retained
evidence from the preceding exact-source commits.

The machine-readable companion is
`formal/tau/m6_tau_placement_frontier_v1.json`.
