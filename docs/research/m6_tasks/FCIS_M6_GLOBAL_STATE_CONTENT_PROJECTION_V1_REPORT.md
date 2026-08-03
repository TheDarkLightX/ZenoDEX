# FCIS M6 Global-State Content Projection V1 Report

TASK_ID: M6-GLOBAL-STATE-CONTENT-PROJECTION-V1
BASE_SHA: 461de21929e867bc459265a75c144e81d72143d7
SOURCE_HEAD_SHA: e95f44061e2d4cd9fb3460cb50ee93460e702a76
SOURCE_HEAD_TREE: 61f213fc7f5cab327b99093467ce5a0b876bce97
BRANCH: codex/task-m6-managed-asset-policy-20260803

## Result

This research slice defines a source-neutral projection of the application
content currently serialized by the Tau application adapter and structurally
committed by a ZenoLedger header. It also defines a separate fail-closed
qualification boundary that rejects every receipt produced by this slice.

The implemented implication is:

```text
canonical application bytes
+ exact component derivation
+ exact application-component coverage partition
+ matching claimed Tau application hash
+ structurally valid ZenoLedger header/body roots
+ matching ZenoLedger post-state commitment
+ one observation of each declared source kind
+ equal source-neutral application-content root
-> non-authoritative content-parity receipt
```

The receipt retains every known global-state gap and every unresolved authority
obligation. Consequently:

```text
ContentParityV1
-> Reject(INCOMPLETE_APPLICATION_CONTENT
          | INCOMPLETE_GLOBAL_STATE
          | UNMET_AUTHORITY_OBLIGATIONS)
```

No path in this implementation returns an authoritative global-state witness.

## Closed application-content carrier

The current application carrier has a closed 14-component registry:

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

Optional subsystems that are absent are recorded as missing components. A bare
DEX snapshot is accepted only in the exact runtime encoding used when both
proof mining and zUSD monetary state are absent. A wrapped state with both
optional values set to null is rejected as non-canonical.

The content root is source-neutral. Source kind, schema, claimed position,
state commitment, chain identity, and observation-specific unmet obligations
remain in a separate observation root. This separation prevents position or
source metadata from changing the semantic content identity while retaining
that metadata for later authority binding.

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
host-native balance inputs. It also permitted raw and `0x`-prefixed spellings of
one public key to compete by input order. The entrypoint now rejects:

```text
booleans
floats
strings
negative quantities
quantities above U256
duplicate decoded public-key identities
```

Native synchronization and patch generation use sorted keys and exact integers.
The patch retains the host's original spelling only after unique decoded
identity has been established.

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
- native-balance aliases and coercions reject;
- missing application components and global families remain exact registries.

### Authority review

The original design allowed self-created roots and headers to look like an
authority-bearing parity result.

Disposition:

- the public result is named `M6ProjectionContentParityReceiptV1`;
- construction provenance is controlled only inside the local verifier path;
- source coordinates are explicitly claimed or structural;
- every parity receipt retains all nine authority obligations;
- the qualification function can only reject the current receipt type.

### Formal/specification review

The original completeness claim was tautological and lacked exact registry
binding and adversarial guard mutation.

Disposition:

- two small ESSO models separate content parity from authority qualification;
- runtime/model registry equality is tested directly;
- 18/18 guard-removal mutants are killed;
- the formal notes state every excluded authority and durability surface.

The reviewers did not perform a second pass over the final repaired tree. Their
initial findings and the implemented dispositions are preserved here for the
next independent review.

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
  source SHA-256  6714f8d45ac8de247f94fcef66e62329ff0fc2e7b4523703210a9cd1793b313b
  ESSO IR hash    sha256:999afe945e0fdc8429b93b45478ca60a671ad4f9d81e75fd0a4b3015815d50c5
  fingerprint     ed68642b6f21ce7d59075b195c679fa280670c65ad272561620b0ba9a5d33208
  queries         14/14 passed

qualification model
  source SHA-256  11a9c2c25c38e88660cf56ff84723b3a4b9ddf25d119a7041fd8b2823d3fd9f8
  ESSO IR hash    sha256:2c9eaac2fbdb23baf280736f2bd1515c4d1e5e7e47bfdbcda577d628fe6d32cc
  fingerprint     7df92385d1ff9191c9ed6c0c87b6f6c20fb693c415adbdaa3cbeddcba1d2d798
  queries         6/6 passed
```

Both models were deterministic across two runs, both solvers agreed on every
query, and neither run returned unknown or timeout.

The models prove their finite guard implications. They do not prove source
authenticity, runtime refinement, requirements completeness, economic
coherence, durability, or mounted mediation.

## Commands and results

- Projection/core/formal suite: 47 passed.
- Tau application, recovery, and ZenoLedger regression suite: 90 passed.
- ESSO semantic guard mutants: 18/18 killed.
- Direct ESSO proof queries: 20/20 passed with Z3/CVC5 agreement.
- Ruff: passed over all changed Python source and tests.
- Ruff formatting: passed over all new Python files. The inherited large Tau
  adapter was not reformatted because that would mix unrelated refactoring into
  this security change.
- Mypy: passed over six affected source modules.
- Python compilation: passed over six affected source modules.
- Security red-flag scan: zero findings over six affected source modules.
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
