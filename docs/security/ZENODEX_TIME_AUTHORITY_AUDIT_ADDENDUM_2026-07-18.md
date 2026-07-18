# ZenoDEX Time Authority and Recursive Proof Audit Addendum

**Date:** 2026-07-18
**PR:** #453
**Reviewed input head:** `81fdad2b8ea177e9c291bdc2ea3d357eaaed3a40`
**Disposition:** **production release blocked**

## Implementation status in this PR update

This update contains the mounted zUSD containment and a mounted protocol-zUSD
reserve claim path:

- ZenoLedger candidate height constructs a governed
  `VerifiedExecutionClockV1`;
- the committed zUSD policy binds the complete clock-policy schedule hash;
- the Tau application bridge requires that typed clock for any state carrying
  zUSD monetary policy;
- the bridge re-derives clock facts from the committed schedule instead of
  trusting a nominal Python object;
- internal epoch admission occurs before user operations;
- public bridge, wallet, and UI grammars reject `advance_epoch`;
- the wallet labels local simulation as an unverified advisory preview and
  separates height expiry from Tau transaction expiry;
- height deadlines use canonical u64 values, including decimal-string wallet
  input, so the operation grammar does not halt at the u32 boundary;
- fee-bearing mint rejects unless the fee is representable by the current
  whole-token transport and has a committed claimant;
- the transaction sender must equal the committed protocol recipient before it
  can claim and drain the protocol zUSD fee reserve;
- fee accumulator events that would create unattributed residue reject
  atomically, and active-account stake top-ups preserve existing entitlement
  exactly across floor boundaries.
- pending Oracle prices retain their observation epoch, and stale commit or
  liquidation attempts reject without changing pre-state.

This closes the reported same-transaction epoch-advance trace and makes the
ordinary protocol zUSD reserve reachable when the outer transaction boundary
authenticates the committed sender. End-to-end claimant authentication remains
an outer admission obligation. This update does not close final-header,
RISC0-journal, recursive-range, Tau-checkpoint, host-entitlement,
redemption-collateral, confidential-request lifecycle, or system-shutdown
liabilities.

The fee fixes are fail-closed containment. Until E8 transport and an explicit
accumulator carry are mounted, a fractional fee or a stake topology that would
create residue rejects the fee-bearing mint. That prevents stranded debt and
locked stake while leaving a borrowing-liveness and stake-griefing risk.

## Executive decision

The suggestion that an application or ZK host should produce authoritative block
time is rejected.

A host may propose or pass a candidate value, but the selected consensus domain
must authorize the block context. The recursive proof fabric can prove that a
transition used the authorized context. It cannot discover time or make a block
final.

The returned correction was directionally right, but it still needed four
architectural repairs:

1. select exactly one execution clock authority per deployment profile;
2. separate candidate execution from current-block finality;
3. bind an execution-context hash rather than the final header hash to avoid a
   proof/header hash cycle;
4. make recursive epoch proofs bind an ordered range of per-block contexts, not
   only one caller-supplied `epoch_id`.

## Deployment profiles

```text
TAU_NATIVE_V1
  Tau consensus supplies the execution block context.

ZENO_LEDGER_SOVEREIGN_V1
  ZenoLedger consensus supplies the execution block context.

ZENO_LEDGER_TAU_CHECKPOINTED_V1
  ZenoLedger consensus supplies the immediate execution clock;
  Tau later authenticates a checkpoint or range for hard finality.
```

No fallback or comparison between host time, request time, Tau time, and
ZenoLedger time is allowed. The selected profile is committed in policy.

The recommended profile for the existing fast-ZenoLedger/slower-Tau topology is
`ZENO_LEDGER_TAU_CHECKPOINTED_V1`.

## Immediate safe clock

Use height-derived logical epochs now:

```text
epoch = epoch_base
      + floor((height - activation_height) / blocks_per_epoch)
```

Use this for stake activation, fee periods, redemption caps, cooldowns, proof
and reward epochs, and protocol scheduling. Prefer height deadlines and Oracle
accepted-height freshness.

Public `advance_epoch` must be unavailable. A transaction cannot advance the
clock that determines its own economics.

Wall-clock semantics require a later committed profile such as slot-derived or
quorum-attested consensus time. Proposer/host wall time is forbidden for
production value movement.

## Baseline gaps and post-update disposition

### ZenoLedger

`src/integration/zeno_ledger_v0.py` commits `height`, `time_ms`, parent/root
fields, and `proof_journal_hash` in the header. Current validation only requires
`time_ms` to be a nonnegative integer. Header-chain validation checks chain ID,
consecutive height, and parent hash, but not parent/child timestamp relations.

The local runner now derives a height-only zUSD execution clock from a governed
policy schedule and requires parent height/hash linkage above genesis. The V1
execution-header core binds the complete schedule hash, validator-set root,
and finality-policy hash. The mounted legacy v0 final header still lacks the V1
execution-context hash and does not yet connect those commitments to its proof
journal. Deterministic wall-clock rules also remain open.

Remaining additions:

```text
parent_time <= child_time
child_time <= deterministic_allowed_upper_bound
child_time - parent_time <= max_time_step
```

The allowed upper bound must come from a committed deterministic policy, not
only one validator's local wall clock.

### Recursive proof fabric

`zk/state_proof_risc0/shared/src/recursive.rs` carries `epoch_id`, chain ID,
policy and state roots, but lacks an independently authorized per-block context
or an ordered block-context range.

One-block recursive composition must bind one `execution_context_hash` across
all lane children. Multi-block epoch composition must additionally bind:

```text
start_height
end_height
first_parent_header_hash
last_execution_context_hash
ordered_block_contexts_root
start/end time when enabled
```

and prove height, parent-hash, state-root, time, and epoch-derivation continuity.

### zUSD proof and refinement projection

`zk/state_proof_risc0/shared/src/surfaces.rs` zUSD transition input and journal
lack height, timestamp, header/context hash, and derived epoch.

`zk/state_proof_risc0/shared/src/zusd_runtime_refinement.rs` includes
`block_timestamp` as caller-supplied operation projection data and explicitly
acknowledges that caller-supplied matching hashes do not establish external
authenticity. The missing independent context commitment must be added.

### Tau application bridge

The app bridge now passes `VerifiedExecutionClockV1` for mounted zUSD execution
and rejects a transaction-level timestamp override. Compatibility execution
keeps the verified height separate from seconds-based DEX, LP-age, and perps
contracts. Full V1 context binding still requires parent/context commitments,
a consensus-governed wall-clock profile where seconds are required, and
proof-journal integration.

## Execution/finality separation

Candidate block admission:

```text
ParentFinalityValid
and ExecutionContextValidAgainstParent
and ClockPolicyValid
and EpochDerivationValid
and ZkReceiptValid
and JournalExecutionContextHash = HeaderExecutionContextHash
and JournalPreStateRoot = HeaderPreStateRoot
and JournalPostStateRoot = HeaderPostStateRoot
and EffectPlanHashMatches
```

Finalized external use:

```text
CandidateBlockAdmissionValid
and FinalityCertificateValid(final_header_hash)
```

Requiring current-block finality before executing that same block is circular.

## Header/proof hash-cycle repair

The current header contains `proof_journal_hash`. Therefore a proof journal must
not directly bind the final hash of that same header.

Use:

```text
execution_context_hash = H(canonical execution-header core excluding proof and finality)
proof journal binds execution_context_hash
final header binds proof_journal_hash
finality certificate binds final_header_hash
```

The finality certificate must remain outside the hash it signs.

## Release-blocking findings

### TIME-AUTH-001

**Partially remediated.** Mounted zUSD uses a committed, height-derived
ZenoLedger clock and has no public `advance_epoch`. Other value-moving paths
still need the same typed context and proof binding.

### TIME-CONTEXT-002

Every value-moving transition and journal does not yet bind one independently
reconstructed execution-context hash.

### TIME-RECURSION-003

Recursive epoch composition does not prove ordered per-block context continuity.

### TIME-HASH-CYCLE-004

No versioned execution-header-core commitment currently separates proof input
context from the final header that contains `proof_journal_hash`.

## BVA requirements

At minimum, release evidence must cover:

- activation height and every epoch boundary at `-1`, exact, `+1`;
- `blocks_per_epoch` at `0`, `1`, maximum, and overflow;
- operation height deadlines at the u32 boundary, u64 maximum, boolean alias,
  and u64 overflow;
- parent timestamp at `-1`, exact, `+1`;
- future/step upper bounds at `-1`, exact, `+1`;
- host/request time substitution;
- one-field context mutations for chain, domain, height, epoch, time, parent,
  pre/post roots, transaction root, evidence root, policy, config, and module
  versions;
- mixed recursive children, height gaps, parent/root discontinuity, epoch-boundary
  crossing, context-root reordering, wrong-header finality, duplicate signer and
  insufficient quorum;
- reject-is-exact-no-op for every failed boundary.

## Immediate implementation order

1. **Implemented for mounted zUSD:** disable user `advance_epoch`.
2. **Implemented for mounted zUSD:** introduce and commit a
   `HEIGHT_ONLY_V1` clock policy.
3. **Pure value objects implemented; runtime binding open:** add a typed
   execution context and execution-context hash.
4. Thread height/derived epoch/context hash through mounted transitions and leaf
   journals.
5. Add the unsigned execution-header-core/final-header split.
6. Add ordered block-context range binding to recursive epoch proofs.
7. Add a wall-clock profile only after deterministic consensus timestamp rules
   and their BVA/sequence proofs exist.

```text
MountedZUSDHeightAuthorityContained = true
ProtocolZUSDFeeClaimantReachable = true
ProtocolClaimantAuthenticationEndToEnd = false
AllValueMovingContextBinding = false
AllFeeLiabilityLifecyclesClosed = false
ProductionReleaseAllowed = false
```
