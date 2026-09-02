---
title: DERIVATIVES_AUTHORIZATION_COVERAGE_MATRIX
type: note
permalink: autonomous-tau-dex-review/docs/derivatives/derivatives-authorization-coverage-matrix
---

# Derivatives Authorization Coverage Matrix

This matrix records the current derivative assurance boundary for live-value
settlement authority. It separates bounded kernel evidence from the stronger
claim that a market can authorize production settlement from replay-bound inputs.

Replay:

```bash
python3 tools/check_derivatives_authorization_matrix.py
```

Machine-readable source:

```text
docs/derivatives/DERIVATIVES_AUTHORIZATION_COVERAGE_MATRIX.json
```

Core release condition:

```text
ProductionDerivativeOK :=
  BoundedKernelEvidence
  and AuthorizationCompleteSettlement
  and StateRootBinding
  and ReplayableSettlementReceipts
```

A derivative lane can have strong bounded evidence while still failing this
production condition if settlement values, revenue values, references, or state
roots are supplied by the environment instead of being derived from authorized
and replayable artifacts.

Current bounded status: all five derivative areas now close their local
authorization requirements in this matrix. Production readiness remains false
until live oracle governance, value-at-risk controls, operator rollout, ledger
replay integration, and incident-response runbooks are complete.

## Current Grades

| Area | Grade | Current posture | Production ready |
| --- | ---: | --- | --- |
| Perps core / clearinghouse perps | A- | bounded production-integration evidence present | no |
| Funding-rate derivatives | A-/B+ | bounded authorization-complete helper lane exists | no |
| IL futures | B+ | bounded authorization-complete receipt lane exists | no |
| Curve-selection market | B/B+ | bounded event-replay authorization lane exists | no |
| General CFMO / FIRE derivatives | B+ | bounded FIRE library and receipt lane exists | no |

## Covered And Open

### Perps Core / Clearinghouse Perps

Covered:

- deterministic epoch settlement
- fee-pool accumulation under mixed liquidation
- breaker and reduce-only behavior
- 2-party and 3-party clearinghouse conservation
- local runtime-shell oracle-bound settlement rejection tests
- SMT kernel evidence for isolated and clearinghouse postures
- full perps evidence runner covering pytest, ESSO kernels, assurance gates,
  Tau ingress, market version/prefix, and Lean proofs

Open:

- live oracle governance and incident response
- value-at-risk controls and operational runbooks

Promotion boundary: bounded production-candidate perps evidence is present.
Live-value release still needs oracle governance, operator rollout,
value-at-risk controls, and incident response.

### Funding-Rate Derivatives

Covered:

- phase/state transition shell evidence for `funding_rate_market_v1`
- v1.1 settlement witness arithmetic evidence
- runtime helper that verifies derived v1.1 witness values and rejects forged
  realized-rate, payout, and reference values
- production-facing helper that requires an oracle reference receipt plus the
  v1.1 settlement witness before settlement
- production dispatcher rejects raw settlement calls unless oracle and witness
  receipts are supplied
- parity/reference evidence for the monolithic v1.1 implementation

Open:

- live oracle governance and production runbooks remain outside this local
  authorization claim

Promotion boundary: keep this lane research or testnet until the disputed claim
is narrowed or the bounded helper lane is promoted through production
integration evidence.

### IL Futures

Covered:

- inductive state-machine evidence for `il_futures_market_v1`
- leverage, margin, and settlement-guard structure in the implementation lane
- epoch-start reserve snapshot helper bound to a state-root receipt
- settlement current-reserve helper bound to a state-root receipt
- epoch-bound TWAP/reference receipt helper with rejection tests
- strict settlement helper emits a verified authority receipt containing a
  balance-transfer root

Open:

- live pool-root source integration and oracle governance remain outside the
  local helper claims
- replay of the balance-transfer root by the ledger adapter remains an
  integration requirement

Promotion boundary: promising derivative lane, with pool-root, reference, and
receipt binding still required before live-value use.

### Curve-Selection Market

Covered:

- inductive state-machine evidence for `curve_selection_market_v1`
- deterministic winner shape once revenue values are accepted
- runtime helper that rejects forged pre/post revenue delta receipts
- fee-accumulator receipt helper requiring one receipt per curve
- pool-event replay helper that derives revenue from ordered, hash-bound event
  receipts
- winner receipt helper that recomputes the winning curve and payout values
  from current revenue and stake state

Open:

- live pool-event emitter integration, anti-wash-trading policy, and production
  runbooks remain outside the bounded helper claim

Promotion boundary: bounded authorization-complete testnet lane. Live
production still needs pool-event emitter integration, wash-trade economics,
and governance runbooks.

### General CFMO / FIRE Derivatives

Covered:

- certified-financial-object architecture notes
- local replay evidence for one ZenoCover FIRE object
- bounded reserve-solvency manifest evidence for that local object family
- checked-in FIRE stdlib with eight pinned object/interface entries
- compiler registry, object package, kernel settlement, settlement packet, apply
  report, and ledger adapter tests for the bounded stdlib lane
- release-assurance gate requiring `FIREVReceiptOK` as the settlement authority
  predicate
- generic derivative settlement receipt envelope for roots, payoff formula hash,
  witness hash, collateral bound, transfer root, and rejection semantics

Open:

- Python verifier proof discharge, live oracle/source governance, object-by-
  object rollout, and production runbooks remain outside the bounded helper
  claim

Promotion boundary: bounded FIRE stdlib and receipt lane. Live production still
needs verifier hardening, oracle/source governance, and object-by-object
rollout.

## Immediate Build Order

1. Connect curve-selection event roots to the live pool-event emitter.
2. Connect derivative receipt roots to ledger balance-transfer adapters.
3. Add production oracle governance, value-at-risk controls, and runbooks for
   perps, funding-rate, and IL.
4. Connect derivative settlement receipts to live ledger balance-transfer replay.
5. Promote claims only after deterministic replay, negative tests, and registry
   entries exist.
