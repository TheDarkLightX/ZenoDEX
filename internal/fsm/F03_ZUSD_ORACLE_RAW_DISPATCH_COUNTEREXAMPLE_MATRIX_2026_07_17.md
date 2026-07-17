# F03 zUSD Raw Stream-11 Dispatch Counterexample Matrix

Status: implementation closure for the raw-dispatch bypass; no F02 or F03
completion claim.

## Authority boundary

The mounted Tau stream-11 bridge previously translated caller fields directly
into zUSD oracle commands. A configured sender or operator was treated as the
authority for price, observed epoch, and epoch delta. That path lacked the F01
oracle-policy-domain receipt, F02 finalized-consensus-context receipt, and the
F03 snapshot provenance required by the completion registry.

The repair commits one exact evidence profile in monetary state:

- `zenodex/zusd-oracle-evidence/finalized-o3-v1` is the default. The current
  shell has no F02/F03 receipt ports, so raw oracle-sensitive actions reject
  without nonce, balance, monetary-state, or effect mutation.
- `zenodex/zusd-oracle-evidence/configured-signer-dev-v0` preserves the old
  configured-signer behavior only after an exact configuration opt-in. It is a
  lower-assurance development profile and is never inferred from chain ID,
  sender, operation fields, or friendly aliases.

The strict profile's trusted receipt-graph root is committed in runtime policy.
`None` is an explicit disabled sentinel: the shared O3 checker rejects every
authorization until a canonical root is provisioned and committed. A submitted
operation can never supply or replace that trust anchor.

## Counterexample and closure matrix

| Raw action | Previously accepted authority | Missing normative evidence | Strict-profile closure | Explicit dev behavior |
| --- | --- | --- | --- | --- |
| `advance_epoch` | configured operator plus caller `delta` | F02 authenticated finalized context; exact height/epoch/time/block/finality projection | rejects with `finalized_context_required`; caller delta has no strict authority | retains the legacy unit-delta/operator rule |
| `bootstrap_oracle` | configured oracle plus caller price/observed epoch | F01 policy domain, F02 finalized context, verified aggregate bootstrap proposal | rejects with port-level `finalized_context_required` and `aggregate_proposal_required` | retains configured-oracle bootstrap |
| `oracle_report` | configured oracle plus caller price/observed epoch | F01 policy domain, F02 finalized context, verified aggregate proposal and full snapshot provenance | rejects with port-level `finalized_context_required` and `aggregate_proposal_required` | retains configured-oracle report |
| `oracle_commit` | configured oracle | F02 finalized context and exact authenticated pending snapshot/root/freshness/prestate/sequence | permissionless in the abstract relation after both ports bind; current shell rejects because neither port exists | retains the legacy configured-oracle commit rule |
| `liquidate` | any sender using the current active scalar price | F02 context, exact committed active-snapshot provenance, and cataloged O3 `liquidate_vault` authorization bound to exact action/prestate | rejects with `finalized_context_required`, `committed_active_snapshot_required`, and `critical_action_authorization_required` | retains the pre-existing liquidation ingress semantics |
| `mint_zusd` | vault owner using the current active scalar price, without mounted-path O3 enforcement | F02 context, exact committed active-snapshot provenance, and cataloged O3 `mint` authorization bound to exact action/prestate/value | rejects with `finalized_context_required`, `committed_active_snapshot_required`, and `critical_action_authorization_required` | retains the pre-existing configured-signer development lifecycle |

The original bypass was reproduced before the repair with focused tests that
accepted configured-signer bootstrap/report, operator-chosen epoch advance, and
the raw report/commit/liquidate lifecycle. The closure regression suite now
checks all six strict actions, including mint, for rejection and observational
no-op behavior, plus the explicit dev opt-in and production-default profile
parser.

## Port-admission kernel scope

`zusd_oracle_ingress_admission_v1` is a finite profile/port admission kernel.
It is exhaustive over two profiles, six action classes, and all assignments of
its six normalized Boolean port facts (768 cases). Its violation set is
lossless only at that normalized port boundary.

The facts intentionally compress lower-level obligations:

- `finalized_context_bound` combines F02 receipt authentication, finality, and
  exact context projection.
- `aggregate_proposal_bound` combines aggregate authentication, F01
  profile/chain/asset/source-set binding, positive and fresh price, monotone
  round, exact prestate/sequence, and source-nullifier uniqueness.
- `pending_snapshot_bound` combines pending existence, exact root, freshness,
  expected prestate/sequence, and inherited proposal provenance.
- `committed_active_snapshot_bound` combines committed snapshot provenance,
  exact projection, freshness, and expected context/root binding.
- `critical_action_authorization_bound` combines the O3 adapter result and
  typed authorization binding for exact action, prestate, profile, query,
  value, freshness, and trusted receipt-graph root.

Individual verifier failure details remain outside this abstraction. The shell
may set a bit only after the entire corresponding conjunction verifies.

## Evidence

- Pure Python relation and generated ESSO reference are compared over all 768
  control cases.
- ESSO `validate` accepts the IR.
- Z3 and CVC5 agree on the inductive checks with deterministic fingerprints.
- Integration regressions verify strict rejection is atomic and that the raw
  plugin default cannot fall back to configured-signer semantics.

## Explicit nonclaims and remaining work

- This artifact does not complete the F02 consensus projection FSM.
- This port-admission kernel is not the complete F03 oracle lifecycle FSM.
- It does not authenticate receipts, establish finality, prove oracle truth, or
  distinguish lower-level verifier failure reasons.
- It does not prove Python-shell refinement merely because ESSO verifies the
  finite control relation; exhaustive parity only covers the normalized 768-case
  control domain.
- The mounted strict profile is intentionally unavailable for oracle-sensitive
  value movement until typed F02/F03 input ports and their verifiers are wired.
- The environment profile/root parser is only an explicit development and
  deployment adapter. First-use environment binding is not an F01 consensus or
  deployment refinement and can fork nodes when monetary state is initially
  unbound. Production promotion requires a genesis- or migration-committed
  policy profile and trusted root shared by every node; later drift is rejected.
- No F03 registry status is promoted by this repair. Full snapshot types,
  round/source/nullifier ownership, pending supersession, committed projection,
  and production liveness remain separate obligations.
