# Consensus Time and Recursive Context V1

**Date:** 2026-07-18

**Status:** partial implementation; production release remains blocked

**Selected deployment profile:** `ZENO_LEDGER_TAU_CHECKPOINTED_V1`

**Immediate clock profile:** `HEIGHT_ONLY_V1`

## Claim scope

This specification defines the authority and commitment boundaries for protocol
time in ZenoDEX. The current implementation provides tested containment for
mounted zUSD execution: a user transaction cannot advance the epoch that
controls its own economics, and the mounted runner derives the logical epoch
from one governed ZenoLedger height.

The local Tau-app runner now constructs a V1 execution-header core, immutable
effect-plan candidate, and independently hashed execution context. When proof
metadata is supplied, it emits an explicitly unverified proof-journal-binding
candidate. It does not construct a final V1 header. The scoped RISC0 spot,
perps-NP, and zUSD transition journals carry the exact nonzero
execution-context tag supplied through a distinct verifier argument. One-block
recursive composition requires every child to carry that same tag.

Production admission still needs to reconstruct the authoritative
`ExecutionHeaderCoreV1` preimage, authenticate the receipt and raw journal,
compare journal roots with the header projection, produce
`VerifiedProofJournalBindingV1`, and only then construct `FinalHeaderV1`.
Multi-block recursive aggregation, consensus finality verification, Tau
checkpoint admission, and complete value-moving lane coverage remain release
blockers.

## Authority decision

The system that authorizes the state transition supplies its execution clock.
Under the selected deployment profile:

1. ZenoLedger consensus authorizes the immediate block height.
2. A committed clock-policy schedule derives the logical epoch from that
   height.
3. Deterministic execution and every proof lane consume the same execution
   context.
4. Validators finalize the resulting ZenoLedger header.
5. Tau may later authenticate an ordered finalized range for hard finality.

An application host, sequencer process, bridge, wallet, transaction, or proof
generator may transport a proposed context. It has no clock authority.

## Height-only clock policy

For the active policy:

```text
epoch = epoch_base
      + floor((height - activation_height) / blocks_per_epoch)
```

The governed policy binds at least:

```text
clock_policy_id
clock_policy_version
chain_id
deployment_profile
consensus_domain_id
activation_height
epoch_base
blocks_per_epoch
```

The schedule hash is an independently configured authority input at the
execution boundary. Callers cannot substitute a schedule and its matching hash
from the same untrusted request.

Policy activation must preserve epoch continuity and occur on an epoch
boundary. Arithmetic is checked in the unsigned 64-bit domain. A child height
is derived as `finalized_parent.height + 1`; it is not accepted as an unrelated
caller assertion.

## Construction phases

Current-block finality cannot be an execution precondition. The construction is:

```text
verified finalized parent
  -> governed candidate height and active clock policy
  -> deterministic transaction and body commitments
  -> candidate post-state and canonical effect plan
  -> execution-header core and execution-context hash
  -> leaf and recursive proof journals
  -> proof-backend verification and VerifiedProofJournalBindingV1
  -> final header containing the proof-journal hash
  -> validator finality certificate over the final-header hash
  -> optional Tau range checkpoint
```

The typed phase boundary is:

```text
VerifiedExecutionClockV1
  -> ExecutionHeaderCoreV1
  -> VerifiedExecutionContextV1
  -> VerifiedProofJournalBindingV1
  -> FinalHeaderV1
  -> FinalizedBlockContextV1
```

`VerifiedExecutionContextV1` represents post-execution, pre-proof admission.
It does not authenticate a proof. Only a configured proof verifier may produce
`VerifiedProofJournalBindingV1`, only that capability may produce a final-header
candidate, and only a finality-verifier boundary may produce a finalized block
context.

## Typed boundary rationale

The construction uses immutable transparent values for headers, contexts,
journals, and effects, with deterministic functions performing each
transition. Verifier-produced capabilities are the exception: their controlled
constructors witness that an authority condition was checked. This follows the
Witness and State Machine patterns described in
[Typed Design Patterns for the Functional Era](https://arxiv.org/abs/2307.07069).

Subsystem interfaces use simple canonical values and keep IO in the shell, in
line with the design described in
[Boundaries](https://www.destroyallsoftware.com/talks/boundaries). The design
does not promote raw dictionaries to authoritative state. Untrusted mappings
must be decoded into exact owned types with closed field sets before they enter
the functional core.

## Acyclic commitments

The proof journal cannot bind the final header hash when that header contains
the proof-journal hash. V1 uses:

```text
execution_context_hash =
  SHA256(domain_sep("execution_context", v1)
         || length_prefix(canonical_json(ExecutionHeaderCoreV1)))

proof_journal_hash =
  H(canonical(ProofJournalBindingV1 {
      execution_context_hash,
      proof_metadata_hash,
      raw_journal_hash
  }))

final_header_hash =
  H(canonical(FinalHeaderV1 {
      execution_header_core,
      execution_context_hash,
      proof_journal_hash
  }))

finality_certificate signs final_header_hash
```

Proof and finality material are excluded from the execution-header core. The
finality certificate is excluded from the hash that it authenticates.

## Mounted zUSD containment

The mounted bridge requires an exact `VerifiedExecutionClockV1`. Before any
user operation, it deterministically advances internal zUSD epoch state to the
epoch derived from the block height. Epoch regression rejects without changing
the pre-state. The clock value owns the immutable governed schedule, validates
its schedule hash during construction, and is re-derived against the schedule
hash committed in monetary state at the bridge boundary.

The public operation grammar and wallet surface exclude `advance_epoch`.
Advisory wallet preview uses a separately typed preview clock and explicitly
reports that no consensus clock is bound. A transaction-level
`block_timestamp` override is rejected by the local Tau-app runner.

This preserves the immediate invariant:

```text
UserOperationCannotAdvanceItsOwnEconomicEpoch
```

Compatibility adapters keep consensus height and legacy wall-clock seconds as
separate inputs. Mounted zUSD consumes only the verified height-derived epoch;
DEX, LP-age, and perps compatibility paths retain their existing seconds-based
contracts. The local runner still receives legacy header `time_ms` as an outer
input, so no production wall-clock authority is claimed.

## Recursive proof requirement

Every child proof for one block must bind the same:

```text
execution_context_hash
chain_id
consensus_domain_id
height
derived_epoch
clock_policy_hash
clock_policy_schedule_hash
pre_state_root
post_state_root
effect_plan_hash
```

A multi-block recursive proof must bind an ordered range:

```text
RecursiveEpochContextV1 {
    clock_policy_schedule_hash
    epoch_id
    start_height
    end_height
    first_parent_header_hash
    last_execution_context_hash
    ordered_block_contexts_root
    pre_state_root
    post_state_root
}
```

The verifier must establish contiguous heights, parent-hash continuity,
state-root continuity, exact epoch derivation for each child, ordered
exact-once inclusion, one chain/domain/policy schedule, and one aggregate
effect-plan commitment. Reordering, duplication, omission, or mixing contexts
must reject.

The current recursive ABI is deliberately scoped to:

```text
aggregation_scope = "single_block"
```

Any other scope rejects. The historical `recursive_epoch_v1` profile name does
not establish an epoch-range claim. A later multi-block ABI must introduce the
ordered range object above and prove its continuity obligations before that
scope can be admitted.

## Implemented in this slice

- frozen height-only clock policy and governed policy schedule;
- strict canonical policy decoding and tagged hashes;
- activation and epoch-boundary arithmetic with overflow rejection;
- policy-upgrade continuity and epoch-boundary activation checks;
- typed verified execution clock and execution-context construction;
- construction-time and bridge-boundary re-verification of every derived clock
  fact against the complete committed schedule;
- execution-header binding of the schedule hash, validator-set root, and
  finality-policy hash;
- canonical immutable native-balance effect-plan candidates with canonical
  principals, per-write expected values, and committed cross-shard references;
- independent rejection when an adapter-returned native-balance patch differs
  from the native balance transition encoded by the returned app state;
- sequential local execution against the balance effects of every earlier
  accepted transaction in the same block;
- acyclic execution-header-core, proof-journal-binding, verified-proof-binding,
  and final-header value objects;
- local Tau-app runner artifacts for the effect-plan candidate,
  execution-header core, execution context, and an explicitly unverified
  proof-journal-binding candidate; the runner does not emit a V1 final header;
- exact supplied-context matching before a proof-bearing local block can be
  emitted;
- RISC0 journal ABI version 2 context binding for the scoped spot, perps-NP,
  and zUSD transition surfaces;
- RISC0 host checks that compare a separately supplied expected context tag,
  request context, decoded journal context, and proof metadata context;
- nonzero RISC0 verifier process status for semantic rejection, with the
  structured rejection payload preserved;
- one-block recursive statement, child-summary, and root-journal context
  binding, with multi-block scopes rejected;
- explicit finality verifier boundary, signer/policy binding, and
  parent-derived child height;
- mounted zUSD epoch admission before user operations;
- pending Oracle observation epochs, with stale commit and liquidation
  rejection at the exact configured boundary;
- removal of public wallet, bridge, and UI `advance_epoch` actions;
- fail-closed rejection of zero-epoch staking activation delay;
- rejection of transaction timestamp substitution in the local runner;
- u64 operation-height deadlines with canonical decimal-string wallet input,
  while the separate Tau transaction-expiration field retains its existing
  u32 contract;
- exact preservation of existing staking entitlement when a pending top-up
  activates across an accumulator floor boundary;
- boundary-value, one-field mutation, reject-is-no-op, and mounted integration
  tests for the implemented scope.

## Open release blockers

1. **Consensus header admission:** the local Tau-app runner emits the
   compatibility v0 header and a V1 execution-context candidate. It deliberately
   does not emit a V1 final header. Production ZenoLedger consensus does not yet
   admit, finalize, or chain V1 headers.
2. **Parent authority:** non-genesis contexts reject a zero parent hash, while
   the generic context verifier still does not consume a certificate-verified
   V1 parent and prove exact parent-hash and pre/post-state continuity. The local
   runner links a legacy v0 header or an explicitly unverified trusted hash.
3. **Proof authenticity and projection:** no concrete production
   `ProofJournalVerifierV1` is mounted. The RISC0 boundary compares an
   independently supplied opaque context tag, but it does not reconstruct the
   authoritative execution-header preimage or prove that authenticated journal
   pre/post/transaction/effect roots equal that preimage.
4. **Leaf coverage:** the scoped RISC0 spot, perps-NP, and zUSD journals bind
   context. Other value-moving proof surfaces must migrate before an
   all-journals claim is available.
5. **Recursive range:** the recursive ABI rejects every scope except one block.
   It does not yet prove an ordered contiguous multi-block context range.
6. **Cross-language parity:** Python pins policy, schedule, execution-context,
   proof-journal, effect-plan, and final-header behavior. An ordered-range
   Python/Rust vector remains absent because that ABI is not implemented.
7. **Runtime coverage:** other value-moving streams still consume legacy raw
   time or epoch fields and need the same typed boundary.
8. **Oracle semantics:** pending price observations now retain their occurrence
   epoch, and stale observations cannot commit or liquidate. Strict zUSD wallet
   flows still lack complete finalized Oracle evidence in ordinary user
   previews and submissions, and the legacy monotone-down price rule remains a
   separate mechanism decision.
9. **Fee liabilities:** the protocol zUSD reserve has a configured-recipient
   claim, while terminal system exit and redemption-collateral disposition are
   incomplete. Ordinary exact repay cannot substitute for the specified
   final-vault terminal-settlement path. The mounted whole-token transport now
   rejects fractional fees atomically; consistent E8 base-unit transport across
   all value-moving lanes remains a separate release blocker.
10. **Schedule authority deployment:** the local runner accepts a custom policy
   schedule only with an expected schedule hash. Production deployment still
   needs that expected hash pinned by consensus or governed node configuration,
   outside the same untrusted request that supplies the schedule.
11. **Protocol claimant authentication:** the mounted claim checks that the
    transaction sender equals the committed recipient. The production outer
    admission path must prove that sender was authenticated for the exact
    transaction and chain context.
12. **Containment liveness:** fractional whole-token fees and accumulator
    residue currently reject the mint. E8 transport plus a bounded explicit
    carry is still required to prevent active stake topology from becoming a
    borrowing-liveness lever.
13. **Wallet proof phase:** current wallet calls do not possess a candidate
    block execution context. Strict context-bound wrappers therefore need a
    sequencer challenge/admission phase; direct wallet mounting currently fails
    closed.
14. **Effect application:** the effect-plan candidate has no authoritative
    executor, atomic multi-write CAS, finalized-header replay key, application
    receipt, or recovery protocol. It must not be treated as applied custody.
15. **Artifact publication:** standalone runner files use mutable height paths
    and sequential writes. Content-addressed staged publication remains open.
16. **Wrapper codec drift:** Tau app-root persistence can commit optional lanes
    that the execution adapter's exact wrapper decoder does not accept on the
    next block. One authoritative wrapper codec and two-block lane persistence
    tests are required.

## Evidence commands

Focused implementation evidence is produced by:

```text
pytest -q tests/core/test_consensus_time_context.py \
  tests/core/test_execution_effect_plan.py \
  tests/integration/test_zeno_ledger_v0.py \
  tests/integration/test_zusd_consensus_clock_binding.py \
  tests/integration/test_zusd_monetary_fee_liability.py \
  tests/integration/test_zusd_monetary_policy_persistence.py \
  tests/integration/test_tau_testnet_dex_plugin.py \
  tests/integration/test_zusd_monetary_wallet_api.py

cd lean-mathlib
lake env lean Proofs/ZUSDMonetaryPolicyBinding.lean
lake env lean Proofs/ZUSDPendingObservationFreshness.lean

cd zk/state_proof_risc0
cargo test -q -p tau-state-proof-risc0-shared --offline
RISC0_SKIP_BUILD=1 cargo test -q -p tau-state-proof-risc0-cli \
  execution_context_binding --offline
```

Passing these tests supports the implemented containment, typed Python
contracts, scoped RISC0 context ABI, and single-block recursive gate. A real
current-source receipt build and verification is still required because the
guest-linked ABI changed. These tests do not discharge finality, ordered
recursive range, Tau checkpoint, complete lane coverage, or fee-liability
obligations.

## Promotion flags

```text
HeightOnlyMountedZUSDContainment = true
ProtocolZUSDFeeClaimantReachable = true
ProtocolClaimantAuthenticationEndToEnd = false
LocalTauRunnerExecutionContextConstruction = true
VerifiedProofJournalCapabilityType = true
ConcreteProductionProofJournalVerifier = false
LocalTauRunnerAcyclicFinalHeaderBinding = false
ScopedRisc0SpotPerpsZUSDContextTagPropagation = true
Risc0IndependentExpectedTagAdmission = true
Risc0SemanticRejectExitNonzero = true
Risc0AuthoritativeHeaderProjectionAdmission = false
RecursiveSingleBlockScopeGate = true
AllLeafJournalContextBinding = false
OrderedRecursiveRangeBinding = false
TauCheckpointBinding = false
FinalityCertificateMountedRunner = false
AuthoritativeEffectApplication = false
AtomicArtifactBundlePublication = false
FeeLiabilityLifecycleClosed = false
ProductionReleaseAllowed = false
```
