# Settlement Attestation Governance v1

## Scope

This slice formalizes the settlement price-attestation trust boundary.

It does not claim that a signed spot-price attestation is a complete oracle-trust solution.
It narrows the local safety claim to a replayable policy-admission relation.

## ShapeForge State

```text
Φ := ⟨
  M = ZenoDEX,
  S = settlement spot-price attestation governance,
  A = signer-policy authority,
  T = replace operator-local allowlists with an explicit governed policy surface,
  V = {
    packet_hash,
    signer_pubkey,
    source_ids,
    signed_at_epoch,
    consumer_now_epoch,
    policy_id,
    policy_epoch,
    registry_root,
    effective_from_epoch,
    expires_at_epoch,
    min_distinct_signers,
    min_distinct_sources
  },
  O = { verify_attestation, verify_policy, build_value_packet, build_end_to_end_certificate },
  G = {
    governance_approved,
    timelock_elapsed,
    multisig_approved,
    policy_active,
    policy_unexpired,
    signer_allowlisted,
    source_policy_ok,
    distinct_signers_ok,
    distinct_sources_ok
  },
  Obs = { attestation_ok, packet_ok, policy_hash },
  K = { policy_hash = H(policy) },
  E = {
    contract: settlement_attestation_policy.py,
    contract: settlement_price_attestation.py,
    contract: settlement_*_packet.py,
    proved: settlement_attestation_policy_guard_v1.yaml,
    tested_discovery: focused integration regressions
  },
  Gap = {
    on-chain registry retrieval,
    multi-attestation bundle for signer quorum > 1,
    disagreement policy across independent signers/sources
  },
  N = {
    operator-local allowlist is not decentralized oracle governance,
    single-signer attestation is not a quorum oracle
  },
  Δ = explicit governed policy object + fail-closed policy gate
⟩
```

## Disaster Paths

### D1. Unpinned operator policy

If the settlement verifier accepts an operator-supplied signer map, then the operator can authorize any signer they control.

```text
D1 := attest_ok ∧ operator_controls_allowlist ∧ operator_controls_feed
```

Impact:
- attacker-controlled price packets can satisfy settlement value checks
- the settlement path is centralized even if signatures are valid

### D2. Instant governance rewrite

If signer additions can become active immediately, governance capture for one block is enough to authorize a malicious signer.

```text
D2 := allowlist_update_addition ∧ ¬timelock_elapsed ∧ policy_active_now
```

Impact:
- malicious signer can be whitelisted just before settlement
- users have no exit window

### D3. Pseudo-diversity

If one operator can whitelist multiple keys they control, a nominal quorum does not imply independence.

```text
D3 := quorum_ok_by_key_count ∧ ¬independent_source_policy
```

Impact:
- quorum claims overstate the actual trust split

## Local Admission Logic

We formalize the local gate as:

```text
PolicyActive(P, now)
  := P.governance_approved
   ∧ P.timelock_elapsed
   ∧ P.multisig_approved
   ∧ P.effective_from_epoch ≤ now
   ∧ now ≤ P.expires_at_epoch

SignerOK(P, s)
  := s ∈ dom(P.allowed_signers)

SourceOK(P, s, srcs)
  := srcs ⊆ P.allowed_signers[s]

QuorumOK(P, signers, srcs)
  := |distinct(signers)| ≥ P.min_distinct_signers
   ∧ |distinct(srcs)| ≥ P.min_distinct_sources

AttestationPolicyOK(P, a, now)
  := PolicyActive(P, now)
   ∧ SignerOK(P, a.signer_pubkey)
   ∧ SourceOK(P, a.signer_pubkey, source_ids(a.packet))
   ∧ QuorumOK(P, [a.signer_pubkey], source_ids(a.packet))
```

Current runtime consequence:
- single-attestation settlement only works when `P.min_distinct_signers = 1`
- if governance sets `P.min_distinct_signers > 1`, the current runtime rejects settlement until a multi-attestation bundle is implemented

That is intentional. It prevents the code from pretending to satisfy a decentralization posture it does not yet implement.

## Temporal Protocol Model

This slice now has a bounded infinite-trace protocol model in:

- `formal/tla/SettlementAttestationGovernance.tla`
- `formal/tla/SettlementAttestationGovernance.cfg`

The TLA+ model complements the local ESSO guard:

- ESSO proves the local admission relation is fail-closed for one policy snapshot.
- TLA+ checks the protocol lifecycle around proposal, timelock, activation, revocation, and settlement binding over time.

Pinned temporal obligations:

```text
AcceptedSettlementRequiresActiveGovernedPolicy
RevokedPolicyRejectsFutureSettlement
NoRetroactiveEpochDriftOnAcceptedSettlement
FairImpliesApprovedPolicyEventuallyActivates
```

Interpretation:
- accepted settlement must bind to the currently active governed policy,
- revoked policy blocks future acceptance,
- later policy evolution cannot retroactively rewrite the accepted policy epoch,
- under weak fairness of timelock progression and activation, an approved pending policy eventually activates.

## Game Theory

### Operator-only policy

Payoff:
- cheapest path for a malicious operator is to whitelist their own signer and publish manipulated prices
- defense cost is zero unless the verifier rejects operator-local policy entirely

Conclusion:
- operator-local allowlists are incompatible with a decentralization claim

### Timelocked multisig policy

Payoff shift:
- malicious additions become delayed
- users and watchers get an exit/challenge window
- one compromised operator key is no longer enough

Conclusion:
- timelocked multisig is a pragmatic minimum governance surface

### Token governance later

Token governance can broaden control, but only if:
- updates remain timelocked
- quorum/approval thresholds are non-trivial
- signer diversity rules prevent one actor from filling the set with its own keys

Otherwise the system only changes from `trust one operator` to `trust a concentrated token block`.

## Residual Limits

This slice still does not prove:
- that the governed signer set is independent in the real world
- that multiple source ids are economically independent
- that one signed packet is enough for decentralized price truth

Those require:
- on-chain registry retrieval / proof of current root
- multi-attestation bundle verification
- disagreement / median / quorum rules across independent signers
