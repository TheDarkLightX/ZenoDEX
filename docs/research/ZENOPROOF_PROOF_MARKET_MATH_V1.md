# ZenoProof Proof Market Math V1

This note pins the exact mathematical claim ZenoProof can safely use before a
blogpost, video, or whitepaper says that it can decentralize mathematics.

## Current Answer

The current public repo has enough machinery for a primary proof-demand market
shape: someone posts demand for a proof, funds the reward, a prover supplies a
verified artifact, the work is canonicalized, and the first valid settlement
gets paid.

The full user-to-user proof exchange requires an added transferable receipt
layer. That layer needs receipt ownership, transfer authorization, listing,
secondary settlement, cancellation, and replay protection rules before the
protocol can claim that users freely buy and sell proofs as assets.

## What A Lean Proof Verifies

The proof file is a Lean 4 proof checked by the Lean kernel through the repo's
pinned toolchain. The checker verifies that each theorem follows from its
definitions, imported library facts, and stated assumptions. It does not verify
that the real protocol implements every abstract field, that the verifier
network is sound, or that legal/economic claims are true.

The verification discipline is:

```text
Lean kernel check
AND no sorry/admit/axiom/unsafe/sorryAx
AND #print axioms audit
AND concrete non-vacuity witnesses
AND runtime refinement tests
```

The first three items check proof integrity. The non-vacuity witnesses check
that the assumptions are satisfiable. Runtime refinement tests are still needed
to show that deployed ZenoProof objects instantiate these formal structures.

## Core Formula

```text
PrimaryProofMarket :=
  PostedDemand
  AND EscrowedBudget
  AND VerifiedSupply
  AND CanonicalConsumedSet
  AND SettlementGate
```

A protocol bounty or posted buy order can instantiate this shape when the
reward is funded, the proof artifact is accepted by the verifier gate, and the
canonical work identifier has not already been consumed.

```text
FullProofExchange :=
  PrimaryProofMarket
  AND TransferableReceipts
```

Transferable receipts are the extra ingredient for user-to-user resale. They
are deliberately separated from the primary reward market so the public claim
does not overstate the current implementation.

## Settlement Contract

For an accepted proof-market trade, the Lean certificate requires:

```text
AcceptedTrade ->
  offer.verified
  AND offer.bindingOk
  AND offer.policyOk
  AND offer.verifierAdmitted
  AND order.sourceVerified
  AND order.sourceBounded
  AND order.noPassiveYield
  AND order.noProfitShare
  AND order.noFutureEntrant
  AND price <= order.escrow
  AND escrowAfter <= escrowBefore
  AND sellerCreditAfter = sellerCreditBefore + price
```

This is the important economic boundary. Payouts are earned by verified work,
funded from an escrowed and bounded source, and blocked if they rely on passive
yield, profit-share, future-entrant inflow, stale orders, unverified artifacts,
bad bindings, or over-escrow prices.

## Canonical Work Identity

Two proof artifacts can have different raw digests while representing the same
mathematical work. The market has to settle work identity through a canonical
tuple:

```text
ProofWork :=
  statementRoot
  assumptionRoot
  inputRoot
  outputRoot
  publicResultRoot
```

The deduplication law is:

```text
sameWork(a, b) AND canonicalizer respects sameWork
  -> settling a consumes the canonical id for b
```

This blocks duplicate payout by nonce churn, auxiliary-data churn, or raw hash
variation. It also gives the market a clean object of trade: the verified work
class, rather than an arbitrary file digest.

The Lean file includes a concrete duplicate-payout witness:

```text
safe order work = safe offer work
first settlement consumes canonical id
second settlement for the same work rejects
```

This proves the deduplication theorem is exercised on a satisfiable example.

## Truth Boundary

The market can pay for accepted verifier outputs. Mathematical truth requires a
separate soundness assumption:

```text
VerifierSound :=
  forall offer, ProofOfferAccepted(offer) -> Truth(offer.work)
```

Then:

```text
AcceptedTrade AND VerifierSound -> Truth(work)
```

Without verifier soundness, payment is only a claim about verifier admission and
policy compliance. This is the central whitepaper discipline: ZenoProof can
decentralize verified mathematical labor only to the extent that the verifier
network, proof checker, assumptions, and artifact bindings are sound for the
statement class.

## Vacuity Boundary

A theorem of the form:

```text
SettlementCert -> SafeConsequence
```

would be weak if no `SettlementCert` could exist. The V1 Lean file now includes
concrete witnesses:

```text
settlement_certificate_assumptions_nonvacuous
accepted_settlement_contract_nonvacuous
primary_market_without_secondary_exchange_nonvacuous
full_exchange_nonvacuous
```

These prove that the safe-settlement assumptions are consistent, that a primary
market can exist without secondary resale, and that a full exchange can exist
when transferable receipts are present. This does not finish the runtime
refinement proof, but it blocks the most common vacuous-proof failure mode.

## Disaster States Reduced

The V1 Lean model directly blocks these disaster states:

- Fake proof payout: rejected by `offer.verified`, `bindingOk`, `policyOk`, and
  `verifierAdmitted`.
- Underfunded settlement: rejected by `price <= order.escrow`.
- Stale reward capture: rejected by `nowEpoch <= order.expiryEpoch`.
- Duplicate proof payout: rejected by canonical consumed-set membership.
- Raw-hash uniqueness error: exposed by a counterexample where two artifacts
  have different raw digests and the same work identity.
- Passive-yield funding drift: rejected by `noPassiveYield`, `noProfitShare`,
  and `noFutureEntrant`.
- Truth overclaim: blocked unless `VerifierSound` is supplied explicitly.
- Secondary-market overclaim: blocked unless `TransferableReceipts = true`.
- Vacuous certificate overclaim: blocked by concrete satisfiable settlement and
  market-state witnesses.

## What The Repo Can Claim Now

ZenoProof can be described as a decentralized proof-work reward and proof-demand
market when these gates are live:

```text
posted demand
AND escrowed budget
AND verifier-admitted proof supply
AND canonical work deduplication
AND fail-closed settlement
```

The proof-mining reward gate and ZenoProof payout replay are the current public
implementation surface for this claim.

## What The Whitepaper Should Wait For

A stronger "users buy and sell proofs" whitepaper claim should wait for:

- A transferable proof-receipt object with canonical ownership.
- A secondary listing and acceptance calculus.
- Replay protection for receipt transfers and cancellations.
- Escrow or delivery-versus-payment rules for secondary trades.
- A refinement proof that runtime receipts instantiate the Lean exchange model.
- Soundness envelopes for each verifier class, including proof checker version,
  assumptions, trusted roots, and artifact availability.
- Counsel-reviewed language for rewards, bounties, service payments, and any
  market interfaces.

## Replay

The public Lean theorem surface is:

```text
lean-mathlib/Proofs/ZenoProofMarket.lean
```

Replay:

```bash
cd lean-mathlib && lake env lean Proofs/ZenoProofMarket.lean
cd lean-mathlib && lake build Proofs.ZenoProofMarket
pytest -q tests/formal/test_lean_zenoproof_market.py
```
