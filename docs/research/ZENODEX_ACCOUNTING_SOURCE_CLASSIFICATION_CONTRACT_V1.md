# ZenoDEX Accounting Source Classification Contract V1

Date: 2026-09-01

Status: `RESEARCH_CONTRACT_V1_WIRE_NAMES_BYTE_STABLE`

Authority: `NONE`

Machine-readable source of truth:
`docs/research/ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.json`, checked by
`tests/test_accounting_source_classification_contract_v1.py`.

## Why this exists

The word "custody" in `GlobalSettlementABI V1` names an accounting scope, never
possession of user keys. The normative safety claim (lines 84-96) states that key
control determines practical custody and that `custody_domain` means accounting
control domain only, and asks for a rename before the ABI freezes if the term
stays ambiguous. V1 wire bytes must stay stable, so the rename applies to new
code, models, and documents through the vocabulary below, with an alias table
back to the V1 field names.

## Vocabulary

| Term | Meaning | V1 wire name |
| --- | --- | --- |
| control_domain | same-ledger accounting control domain in which entitlements reconcile | `custody_domain` |
| controlled_location | atoms in a protocol-controlled location (pool, margin, escrow, fee residue) | `custody` table, `owner` = controlling_principal |
| claimant_entitlement | atoms a claimant may withdraw from a control domain | `liabilities` table, `owner` = claimant |
| unencumbered_reserve | named protocol-owned atoms with no claimant | `reserves` table |
| key_controlled_account | self-custody balance controlled by a key | `balances` table, domain `accounts` |
| pending_external_obligation | registered external delivery awaiting acknowledgment | `outbox` row (asset, amount absent in V1) |
| terminal_obligation | claim that must drain or tombstone | `terminal_obligations` row (control domain, principal absent in V1) |

## Normative partition and conservation

```text
controlled_atoms
  = claimant_entitlements
  + named_unencumbered_reserves
  + pending_registered_external_obligations

sum(balances) + sum(custody) + sum(reserves) = supply      (per asset)
```

Reserves are the claimant-free term. An unencumbered reserve atom can never
cover a missing claimant entitlement, and the current profile rejects
unencumbered controlled-location atoms, so the exact relation
`custody(control_domain) = claimant_entitlements(control_domain)` holds in every
domain with zero reserve and zero pending-external terms.

## Source classes

`CLAIMANT_ENTITLEMENT`, `UNENCUMBERED_CONTROLLED_LOCATION` (rejected under the
exact partition), `UNENCUMBERED_RESERVE`, `PENDING_EXTERNAL_OBLIGATION`, and
`TERMINAL_OBLIGATION`. Every controlled source atom is classified exactly once
per `(asset, control_domain)`; omission, duplication, and cross-domain assignment
reject. Each class binds asset, integer scale, u128 width, owner or claimant,
control domain, lane provenance, occurrence, profile and release roots, writer
epoch, and canonical order; terminal rows additionally bind terminal identity,
controlling principal, and lane state root; external rows bind destination and
commitment. Rounding is `NONE`; overflow rejects; residue is carried as a named
reserve row.

## Claimant-backing guard (implemented)

`ClaimantBackingViewV1` (Python `src/core/global_economic_state_effect_refinement_v1.py`,
Rust `zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs`)
folds only custody, entitlement, and OPEN terminal totals; it has no reserve or
balance column. Reject precedence is closed and shared:
`CLAIMANT_BACKING_TOTAL_OVERFLOW`, then
`LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING`, then
`OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS`. The shared vector
`tests/data/global_claimant_backing_guard_v1_golden.json` binds states, view
bytes, view roots, and exact codes and messages across both languages.

## Blocked pending policy

UP-01, UP-02, UP-04, UP-05, UP-09, UP-11, UP-13, UP-15, and UP-17 gate the
economic content of reserves, fees, hosting, zUSD, perps, proof rewards,
external finality, issuance, and scales. No value is selected from a fixture.

## Nonclaims

- Nothing on the V1 wire is renamed; every V1 field name and byte stays stable.
- The guard proves only the two state-visible necessary inequalities; exact
  all-lane reconciliation requires the `GlobalAccountingAllocationCertificateV1`
  producers.
- No production, release, settlement, verifier, migration, publication, or
  value-moving authority is granted.
