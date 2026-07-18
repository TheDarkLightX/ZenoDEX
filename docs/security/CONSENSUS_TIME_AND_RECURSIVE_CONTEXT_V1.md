# Consensus Time and Recursive Context V1

**Date:** 2026-07-18

**Status:** partial implementation; production release remains blocked

**Selected deployment profile:** `ZENO_LEDGER_TAU_CHECKPOINTED_V1`

**Immediate clock profile:** `HEIGHT_ONLY_V1`

## Claim scope

This specification defines the authority and commitment boundaries for protocol
time in ZenoDEX. The current implementation provides a tested containment for
mounted zUSD execution: a user transaction cannot advance the epoch that
controls its own economics, and the mounted runner derives the logical epoch
from one governed ZenoLedger height.

This document does not claim that the final ZenoLedger header, RISC0 leaf
journals, recursive epoch proofs, or Tau checkpoints yet bind this context.
Those bindings remain release blockers.

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
  -> final header containing the proof-journal hash
  -> validator finality certificate over the final-header hash
  -> optional Tau range checkpoint
```

The typed phase boundary is:

```text
VerifiedExecutionClockV1
  -> ExecutionHeaderCoreV1
  -> VerifiedExecutionContextV1
  -> FinalHeaderV1
  -> FinalizedBlockContextV1
```

`VerifiedExecutionContextV1` represents post-execution, pre-proof admission.
Only a finality-verifier boundary may produce a finalized block context.

## Acyclic commitments

The proof journal cannot bind the final header hash when that header contains
the proof-journal hash. V1 uses:

```text
execution_context_hash =
  SHA256(domain_sep("execution_context", v1)
         || length_prefix(canonical_json(ExecutionHeaderCoreV1)))

proof_journal_hash = H(canonical proof journal binding execution_context_hash)

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
    first_parent_final_header_hash
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

## Implemented in this slice

- frozen height-only clock policy and governed policy schedule;
- strict canonical policy decoding and tagged hashes;
- activation and epoch-boundary arithmetic with overflow rejection;
- policy-upgrade continuity and epoch-boundary activation checks;
- typed verified execution clock and execution-context construction;
- construction-time and bridge-boundary re-verification of every derived clock
  fact against the complete committed schedule;
- acyclic execution-header-core and final-header value objects;
- execution-header binding of the schedule hash, validator-set root, and
  finality-policy hash;
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

1. **Header admission:** the mounted local runner still emits the legacy v0
   header. Its final header does not commit the clock-policy schedule hash or
   V1 execution-context hash.
2. **Parent authority:** the local compatibility path may use an explicitly
   trusted parent height/hash. Production admission still needs a verified
   finalized parent context and its consensus certificate.
3. **Leaf journals:** zUSD and other value-moving RISC0 journals do not yet bind
   the independently reconstructed execution-context hash.
4. **Recursive range:** the recursive statement still accepts a free
   `epoch_id`; it does not prove an ordered contiguous block-context range.
5. **Cross-language parity:** Python now pins policy, schedule,
   execution-context, and final-header hash vectors. Rust parity and the
   ordered-range vector remain absent.
6. **Runtime coverage:** other value-moving streams still consume legacy raw
   time or epoch fields and need the same typed boundary.
7. **Oracle semantics:** pending price observations now retain their occurrence
   epoch, and stale observations cannot commit or liquidate. Strict zUSD wallet
   flows still lack complete finalized Oracle evidence in ordinary user
   previews and submissions, and the legacy monotone-down price rule remains a
   separate mechanism decision.
8. **Fee liabilities:** the protocol zUSD reserve has a configured-recipient
   claim, while terminal system exit and redemption-collateral disposition are
   incomplete. Ordinary exact repay cannot substitute for the specified
   final-vault terminal-settlement path. The mounted whole-token transport now
   rejects fractional fees atomically; consistent E8 base-unit transport across
   all value-moving lanes remains a separate release blocker.
9. **Schedule authority deployment:** the local runner accepts a custom policy
   schedule only with an expected schedule hash. Production deployment still
   needs that expected hash pinned by consensus or governed node configuration,
   outside the same untrusted request that supplies the schedule.
10. **Protocol claimant authentication:** the mounted claim checks that the
    transaction sender equals the committed recipient. The production outer
    admission path must prove that sender was authenticated for the exact
    transaction and chain context.
11. **Containment liveness:** fractional whole-token fees and accumulator
    residue currently reject the mint. E8 transport plus a bounded explicit
    carry is still required to prevent active stake topology from becoming a
    borrowing-liveness lever.

## Evidence commands

Focused implementation evidence is produced by:

```text
pytest -q tests/core/test_consensus_time_context.py \
  tests/integration/test_zusd_consensus_clock_binding.py \
  tests/integration/test_zusd_monetary_fee_liability.py \
  tests/integration/test_zusd_monetary_policy_persistence.py \
  tests/integration/test_tau_testnet_dex_plugin.py \
  tests/integration/test_zusd_monetary_wallet_api.py

cd lean-mathlib
lake env lean Proofs/ZUSDMonetaryPolicyBinding.lean
lake env lean Proofs/ZUSDPendingObservationFreshness.lean
```

Passing these tests supports only the implemented containment and typed Python
contracts. It does not discharge the open proof, finality, recursive range, or
fee-liability obligations.

## Promotion flags

```text
HeightOnlyMountedZUSDContainment = true
ProtocolZUSDFeeClaimantReachable = true
ProtocolClaimantAuthenticationEndToEnd = false
FinalHeaderContextBinding = false
AllLeafJournalContextBinding = false
OrderedRecursiveRangeBinding = false
TauCheckpointBinding = false
FeeLiabilityLifecycleClosed = false
ProductionReleaseAllowed = false
```
