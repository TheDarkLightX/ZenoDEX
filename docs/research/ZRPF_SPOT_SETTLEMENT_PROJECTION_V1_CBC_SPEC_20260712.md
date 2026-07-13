# ZRPF Ordinary Spot Settlement Projection V1 CBC Specification

Date: 2026-07-12

Status: proof-neutral reference projection and ordinary certificate
recomposition implemented and host-tested; receipt guest, ledger authority,
mint, burn, messages, carries, and rewards pending

## Purpose

The ordinary Spot projection closes the association between an economic
action's opaque `effect_commitment` and a settlement row set for one bounded
profile.

Its input is one self-consistent `ProposedValueAggregateV5`. The constructor
requires the exact Spot value profile and derives one aggregate economic action
for the complete state chain. The action represents up to 64 authenticated
transactions while the settlement plan applies one lane-state write and one
ordinary transfer row per represented asset.

## Deterministic mapping

```text
V5 scope.application_id       -> action.application_id
V5 scope.chain_or_domain_id   -> action.chain_or_domain_id
V5 single epoch               -> action validity and batch epoch
V5 raw subtree pre-state      -> action and batch pre-state
V5 transaction roots          -> consumed object IDs
V5 proposal and subtree roots -> action_semantics_hash
V5 lane and state endpoints   -> one canonical lane cell write
V5 ordinary asset flows       -> one canonical asset effect per asset
complete derived row material -> effect_commitment
exact V5 proposal bytes       -> source_semantic_journal_hash
```

Authorization subject, scope, nonce, and grant ID are explicit inputs. They
change the action and replay identities without changing the source-derived
effect commitment.

## Accepted profile

The initial profile requires:

```text
value profile             = governed Spot V1
accounting domain         = governed Spot V1
atoms unit                = governed Spot V1
state-root scheme         = governed Spot V1
asset flow count          > 0
issued atoms              = 0 for every asset
destroyed atoms           = 0 for every asset
outflow atoms             = inflow atoms > 0 for every asset
authority-use records     = empty
messages/carries/rewards  = empty
```

This restriction makes the effect projection non-circular and removes row
partition aliases for the accepted profile. Supply-changing and cross-domain
profiles require separately typed projections.

## Authority progression

```text
authenticated V5 receipt
  -> exact V5 proposal bytes
  -> derive_spot_settlement_projection_v1
  -> exact expected action batch and SettlementEffectPlanV2
  -> settlement certificate guest compares exact values
  -> sealed settlement receipt verifier
  -> atomic ledger commit capability
```

The implemented host/shared projection begins at the second line. The
proof-neutral composer rederives that projection and closes the exact
certificate field mapping. Neither function grants receipt or ledger
authority.

## Explicit non-claims

The current implementation supplies no receipt verification, current image ID,
state-tree write proof, authorization-grant existence proof, source-chain
finality, data availability, schedule certificate, carry continuity, durable
admission, mint/burn settlement, cross-domain settlement, reward settlement,
release authority, privacy, throughput, or production authority.

The certificate guest must rederive this projection from an authenticated V5
journal and compare exact plan bytes. Accepting a caller-supplied plan without
that recomposition remains forbidden.
