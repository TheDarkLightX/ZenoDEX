# FCIS M6 Global-State Content Projection V1 Report

TASK_ID: M6-GLOBAL-STATE-CONTENT-PROJECTION-V1
BASE_SHA: 461de21929e867bc459265a75c144e81d72143d7
SOURCE_HEAD_SHA: b8b5f1990902dbd8f27d684c466bfb24cc7d293f
SOURCE_HEAD_TREE: 87f80e2bdf75eb5b442dc7db9b92cea8c255c042
BRANCH: codex/task-m6-managed-asset-policy-20260803

## Result

This research slice defines a source-neutral projection of the exact shared
spot content carried by the Tau application envelope and committed by
`zeno_ledger_v0.dex_state_root_v0`. It also defines a separate fail-closed
qualification boundary that rejects every receipt produced by this slice.

The implemented implication is:

```text
canonical Tau application or DEX-snapshot bytes
+ exact spot-state derivation
+ exact seven-component shared-spot coverage partition
+ matching claimed Tau application hash
+ structurally valid ZenoLedger header/body roots
+ matching ZenoLedger `dex_state_root_v0` post-state commitment
+ one observation of each declared source kind
+ equal source-neutral shared-spot content root
-> non-authoritative content-parity receipt
```

The receipt retains every known global-state gap and every unresolved authority
obligation. Consequently:

```text
ContentParityV1
-> Reject(INCOMPLETE_GLOBAL_STATE)
```

No path in this implementation returns an authoritative global-state witness.

## Exact shared carrier and desired application registry

The desired application-state registry has 14 components:

```text
account balances
AMM pools
LP ownership
LP mint age
LP duration risk
nonces
legacy fee accumulator
vault reward state
oracle freshness state
perps state
proof-mining state
zUSD monetary state
zUSD core state
zUSD protocol-fee scalar claim
```

The current ZenoLedger post-state root commits seven of those logical
components through six byte-framed root sections:

```text
account balances
AMM pools
LP ownership
LP mint age
LP duration risk
nonces
legacy fee accumulator
```

LP mint age and LP duration risk share the root's `LPA` section, so six section
labels correspond to seven logical application components. A permanent test
changes only LP mint age and requires both the ZenoLedger spot root and the
source-neutral content root to change.

The other seven components remain explicitly missing from every current shared
receipt. Optional subsystems that are absent from Tau are also recorded during
normalization. A bare DEX snapshot is accepted only in the exact runtime
encoding used when both proof mining and zUSD monetary state are absent. A
wrapped state with both optional values set to null is rejected as
non-canonical.

The shared content root is source-neutral. Source kind, schema, claimed
position, state commitment, chain identity, and observation-specific unmet
obligations remain in a separate observation root. This separation prevents
position or source metadata from changing semantic spot-content identity while
retaining that metadata for later authority binding.

The Tau observation retains the exact canonical full-envelope bytes and Tau
schema bound by its claimed application hash. The ZenoLedger observation
retains canonical spot-snapshot bytes and the DEX snapshot schema corresponding
to its narrower post-state root. Uncommitted Tau wrapper bytes are never labeled
as ZenoLedger source provenance.

Every canonical DEX snapshot field is covered by an exact field-to-component
registry or declared representation-only. Runtime and ESSO metadata must match
that registry exactly.

## Explicit global gaps

The application carrier is not treated as the complete M6 state. The receipt
retains this closed 14-gap registry:

```text
managed-asset policy
fee-role claim state
fee-apportionment state
fee-authority configuration
authenticated execution context
host-native custody
feature-activation profile
oracle-reporter authority
buy-and-burn lifecycle
sealed-bid lifecycle
sovereign-ledger carriers
writer epoch and migration
history, nullifier, and receipt
outbox and acknowledgment
```

It also retains nine unresolved authority/coherence obligations:

```text
Tau stable committed view
ZenoLedger selected head
ZenoLedger execution ancestry
cross-source handoff
deployment binding
current-writer binding
global economic coherence
sovereign-carrier refinement
requirements-registry completeness
```

These registries are duplicated in the two ESSO models and checked against the
runtime enums by an unskipped parity test. A registry omission is therefore a
failing test rather than an implicit reduction in scope.

## Native-custody input hardening

The Tau application entrypoint previously coerced or silently ignored malformed
host-native balance inputs. It also used canonicalized balances for native
state synchronization while later proof-mining logic could reread the original
map. The entrypoint now rejects:

```text
booleans
floats
strings
negative quantities
quantities above U256
duplicate decoded public-key identities in one map
```

One accepted map is canonicalized once. Native synchronization, proof-mining
pool lookup, claim application, and patch generation consume that same
canonical map. Raw, prefixed, and uppercase spellings produce byte-identical
application results when they denote the same unique input map. The patch
retains the host's original spelling only after unique decoded identity has
been established.

This closes one deterministic input ambiguity. It does not authenticate the
host balance map or prove its custody relation to the global economic state.

## Adversarial review disposition

Three independent read-only review passes initially returned `REVISE`.

### Carrier and adapter review

Findings included non-canonical wrapper handling, source-dependent semantic
roots, cross-component contradictions, weak ZenoLedger ancestry, two adapters
over one supplied envelope, chain-balance aliasing, and an incomplete carrier.

Disposition:

- bare and wrapped runtime encodings are distinguished canonically;
- component roots and the content root are source-neutral;
- economic coherence is an explicit authority obligation;
- ZenoLedger execution ancestry and selected-head authority remain explicit;
- both adapters are named as claimed/structural observations;
- duplicate native-balance identities and non-exact quantities reject;
- accepted native-balance spellings normalize once before every consumer;
- missing application components and global families remain exact registries.

The final carrier pass also found that the original adapter compared the full
Tau envelope against a ZenoLedger root that commits only spot DEX state. The
repair restricts parity to the exact committed subset. A follow-up source audit
found that the six state-root sections represent seven logical components
because LP mint age and duration risk share one section. Both distinctions are
now permanent registry tests.

### Authority review

The original design allowed self-created roots and headers to look like an
authority-bearing parity result.

Disposition:

- the public result is named `M6ProjectionContentParityReceiptV1`;
- construction provenance is controlled only inside the local verifier path;
- source coordinates are explicitly claimed or structural;
- every parity receipt retains all nine authority obligations;
- the qualification function can only return `INCOMPLETE_GLOBAL_STATE` for a
  valid current receipt and `INVALID_SOURCE` otherwise.

### Formal/specification review

The original completeness claim was tautological and lacked exact registry
binding and adversarial guard mutation. The first repaired model still allowed
future authority-closing actions that did not exist in the runtime, allowed
admission premises to change after admission, and lacked progress/reachability
mutation evidence.

Disposition:

- the qualification model exactly mirrors the current reject-only runtime;
- content admission freezes every premise needed by its receipt;
- runtime/model registry equality is tested directly;
- all intended admission, parity, invalidation, and rejection actions are
  reachable in the unmutated models;
- 35/35 retained formal and registry mutants are killed, including guard,
  post-admission, no-progress, rejection, and authority-issuance mutations;
- the formal notes state every excluded authority and durability surface.

All three independent reviewers then re-reviewed the repaired source head
`b8b5f1990902dbd8f27d684c466bfb24cc7d293f` and returned `PASS` for this
narrow content-only slice. The carrier reviewer reproduced one final defect at
the preceding `e5e7456...` head: a ledger observation retained uncommitted Tau
wrapper bytes while its header bound only spot state. Commit `b8b5f199...`
separates Tau full-envelope provenance from ZenoLedger spot-snapshot provenance.
The authority and formal reviewers confirmed that the rejection-only boundary,
registries, models, parity semantics, and nonclaims remain unchanged.

## Formal evidence

Pinned ESSO commit:

```text
7f80c6216be85c827e8d1cc2fa08ee3107a74588
```

Pinned solvers:

```text
Z3   4.15.4
CVC5 1.1.2
```

Results:

```text
content-parity model
  source SHA-256  7157fe140cf1b7665a4034736889ece660f3b9ce60082043cce030079563c238
  ESSO IR hash    sha256:be59ca645f6009b9c1e6363cf26528d550878e9bb1716ef866eed2502f8666ad
  fingerprint     ed68642b6f21ce7d59075b195c679fa280670c65ad272561620b0ba9a5d33208
  queries         14/14 passed
  reachable       549 states, 5,334 enabled transitions

qualification model
  source SHA-256  33bc52cd3d18a2ec4892a76f3bdf1987c93f0f8d4410da2f2e8a2656236621a8
  ESSO IR hash    sha256:8a965008457019d9516d9ec52887abfe7fdd534b817d76427c1d9d7e05f0412b
  fingerprint     d286dcfb3c44b5b4a52eaabfc70c795bae411395ae9ecb814aba496b8af10808
  queries         5/5 passed
  reachable       4 states, 7 enabled transitions
```

Both models were deterministic across two runs, both solvers agreed on every
query, and neither run returned unknown or timeout.

The models prove their finite guard implications. They do not prove source
authenticity, runtime refinement, requirements completeness, economic
coherence, durability, or mounted mediation.

## Commands and results

- Combined projection, formal, Tau application, recovery, and ZenoLedger suite:
  166 passed.
- Formal and registry mutants: 35/35 killed (27 solver-killed safety mutants,
  5 reachability-killed progress mutants, and 3 exact registry omissions).
- Direct ESSO proof queries: 19/19 passed with Z3/CVC5 agreement.
- Ruff: passed over all changed Python source and tests.
- Ruff formatting: passed over all new Python files. The inherited large Tau
  adapter was not reformatted because that would mix unrelated refactoring into
  this security change.
- Mypy: passed over six affected source modules.
- Python compilation: passed over six affected source modules.
- Security red-flag scan: zero findings over four authority-facing source
  modules.
- Git diff hygiene: passed.

The design metrics still identify the inherited Tau application adapter as a
large, complex boundary. This change adds one small validation helper and does
not broaden its responsibilities.

## Remaining nonclaims

- No Tau stable/current committed-view witness is implemented.
- No ZenoLedger selected-head, quorum/finality, or execution-ancestry witness is implemented.
- No cross-source failover or handoff relation is implemented.
- No deployment, writer epoch, migration phase, or current-head binding is implemented.
- No global economic coherence theorem is implemented.
- No proof establishes that the 14 global-gap families exhaust all user and protocol requirements.
- No canonical sovereign ZenoLedger application-state carrier is implemented.
- No authenticated host-native custody relation is implemented.
- No proof connects these Python projections to Rust, Tau, ZK, or deployed bytes.
- No receipt, bundle, history, nullifier, publication, reopen, outbox, acknowledgment, or no-bypass path consumes this receipt.
- No production runtime path is mounted or authorized by this slice.
- M6 remains research-only, unmounted, and non-promotable.

## Next safest step

Define verifier-owned `TauStableCommittedViewV1` and
`ZenoLedgerSelectedHeadViewV1` values, then bind them through an explicit
cross-source handoff/current-writer relation. In parallel, freeze the complete
global-state carrier that closes the 14 gap families. The parity receipt must
remain non-authoritative until both the state carrier and every authority
obligation are closed for one exact promotion subject.
