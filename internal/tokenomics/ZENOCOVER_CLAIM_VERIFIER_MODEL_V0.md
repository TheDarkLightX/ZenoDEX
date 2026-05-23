# ZenoCover Claim Verifier Model V0

Status: internal research/spec artifact. This is not a public ZenoCover product,
insurance claim, regulatory conclusion, live reserve claim, or production
claims workflow.

## Game Surface

Players:

- cover buyer or claim submitter;
- reserve LP or reserve controller;
- claim verifier;
- proof verifier;
- oracle reporter;
- challenge participant;
- attacker attempting to obtain payout without a covered event.

Actions:

- submit a claim against an active policy;
- provide proof, oracle, ledger, and settlement evidence;
- authorize a payout;
- reject stale, duplicate, excluded, unsupported, or over-cap claims;
- slash or penalize a verifier that accepts invalid claims in the bounded model.

Timing:

1. Policy and reserve caps are fixed.
2. A claim arrives inside or outside the claim window.
3. The verifier checks event evidence and duplicate keys.
4. The verifier recomputes payout from loss, requested amount, coverage limit,
   and per-claim cap.
5. Aggregate payout and reserve floors are checked.

## Attack Query

The checker rejects the candidate if any supplied claim or exhaustive bounded
sweep witnesses:

```text
ClaimAccepted(claim) and not CoveredEvent(claim)
```

or:

```text
Payout(claim) > min(requested_payout, loss_amount, coverage_limit, per_claim_cap)
```

or:

```text
SumAuthorizedPayouts > aggregate_payout_cap
```

or:

```text
MaxInvalidClaimGain > VerifierSlashAmount + FutureValueLost
```

The bounded verifier also rejects duplicate paid claim keys and reserve-floor
violations.

## Bounded Model

The executable model is `tools/check_zenocover_claim_verifier_model.py`. It uses
integer amounts only. It admits four narrow failure kinds:

- `settlement_invariant_failure`;
- `ledger_replay_failure`;
- `proof_metadata_binding_failure`;
- `oracle_policy_failure`.

For an accepted claim, the recomputed payout is:

```text
min(requested_payout, loss_amount, coverage_limit, per_claim_cap)
```

Invalid, stale, duplicate, excluded, unsupported, or already paid claims
recompute to zero. The manifest must state `expected_authorized_payout`, and
the checker rejects any mismatch.

## Evidence Lane

Replay command:

```bash
python3 -m pytest -q tests/tools/test_check_zenocover_claim_verifier_model.py
```

Direct manifest command:

```bash
python3 tools/check_zenocover_claim_verifier_model.py path/to/claim-verifier.json
```

The focused tests cover accepted settlement failure, invalid event positive
payout rejection, payout cap rejection, duplicate paid key rejection, aggregate
cap rejection, underbonded verifier rejection, acceptance of the three other
narrow failure kinds, and CLI replay.

Companion Lean payout-cap proof:

```bash
cd lean-mathlib
lake env lean Proofs/ZenoCoverPayoutCap.lean
lake build Proofs.ZenoCoverPayoutCap
lake env lean Proofs.lean
```

Pytest wrapper:

```bash
python3 -m pytest -q tests/formal/test_lean_zenocover_payout_cap.py
```

The Lean surface proves that the bounded payout function is nonnegative,
bounded by requested amount, loss, coverage limit, per-claim cap, and spendable
reserve. It also proves that one verified claim and any ordered list of verified
claims preserve the configured reserve floor when each claim is verified against
the current reserve.

Companion reserve-withdrawal replay command:

```bash
python3 -m pytest -q tests/tools/test_check_zenocover_reserve_withdrawal_safety.py
```

Direct reserve-withdrawal manifest command:

```bash
python3 tools/check_zenocover_reserve_withdrawal_safety.py path/to/withdrawal.json
```

That checker models the reserve LP withdrawal query:

```text
withdraw_before_claim_window_closed and remaining_reserve < active_liability
```

It admits a withdrawal only when cooldown is complete and:

```text
post_reserve >= active_liability + pending_claim_window_liability + min_surplus
```

If the claim window is closed, the pending claim-window liability term drops to
zero. The tests cover safe withdrawal, premature underfunding, missing cooldown,
closed-window floor release, sequential overdraw, initially underfunded pool,
and CLI replay.

## Promotion Boundary

This artifact supports internal design iteration for proof-triggered cover. It
does not prove actuarial solvency, oracle truth, regulatory status, production
claims operations, live reserves, premium pricing, external-protocol coverage,
or complete ZenoCover implementation.

Promotion would require real policy manifests, reserve accounting integration,
oracle/proof/verifier receipts, broader attack simulations, counsel review, and
production runtime gates. The Lean payout-cap proof covers only arithmetic
clamping and reserve-floor preservation for the internal model.
