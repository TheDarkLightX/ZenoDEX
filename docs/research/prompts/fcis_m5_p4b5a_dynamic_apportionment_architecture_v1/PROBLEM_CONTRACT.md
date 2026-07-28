# P4B5A dynamic protocol-fee apportionment problem contract

**Status:** `SEMANTICALLY_APPROVED_FOR_RESEARCH`

**Prompt kind:** research, algorithm design, and architecture decision

**Visibility:** repository-local and suitable for the public ZenoDEX branch

**Contract version:** `fcis-m5-p4b5a-dynamic-apportionment/v1`

**Execution authorized:** review-only research and local evidence

## Intent mirror

### User's real job

Resolve the protocol-fee apportionment architecture blocker so P4B5A can
proceed with one design that remains safe under adversarial policy changes,
cross-language execution, account rotation, and U256 amounts.

### Desired result

One independently reviewable architecture decision:

```text
SELECT(candidate, exact laws, policy lifecycle, state, migration, evidence)
```

or:

```text
NO_GO(counterexample, missing premise, next smallest research question)
```

### Decision enabled

The result decides whether the P4B5A packet can be amended and which
apportionment semantics Python, Rust, receipts, roots, and formal models must
implement later.

### Non-goals

- Runtime implementation or authority mounting.
- Production datastore or outbox proof.
- Legal custody claims.
- Cross-asset conversion.
- A novelty or global-optimality claim.
- Repairing unrelated M5 findings.

## Semantic traceability

| ID | Requirement or decision | Origin | Status | Consequence if wrong |
| --- | --- | --- | --- | --- |
| R1 | Commit the blocker and context for independent agents | user-stated | approved | Agents solve different problems |
| R2 | Preserve FCIS typed immutable values and one atomic candidate | repository contract | approved | Partial or reconstructed authority |
| R3 | Apportion only replay-derived protocol fees by asset | source and audit | approved | LP funds or mixed units can be spent |
| R4 | Treat a compromised policy operator as in scope | latest independent review | approved for research | Adaptive rounding attack is missed |
| R5 | Use a stable distribution-domain key independent of keyholder rotation | latest independent review | approved for research | Fresh-state reset amplification |
| R6 | Make V2 same-batch spend semantics explicit | source and latest review | open architecture choice | Silent accepted-language change |
| R7 | Require Python/Rust exact integer semantics | frozen P4B5A packet | approved | Consensus divergence |
| R8 | Keep runtime edits and mounting outside this checkpoint | frozen checkpoint order | approved | Review evidence becomes authority |
| R9 | Evaluate same-key temporal fragmentation explicitly | agent-proposed from a new counterexample | open | A batching-dependent policy is accepted unknowingly |

R9 is an evaluation requirement. The research may conclude that exact
same-key fragmentation invariance is unnecessary, impossible with another
hard requirement, or achievable. The conclusion must state the observable
economic consequence and the versioned rule.

## Fixed composition boundary

The following boundary survives all completed reviews:

```text
SettlementPhase(
    pre_state,
    admitted_command,
    authenticated_context,
)
  -> Reject(reason)
  | (
      staged_settlement_candidate,
      exact_provisional_protocol_fee_values,
      replacement_lineage_witnesses,
    )

ApportionmentPhase(
    staged_settlement_candidate,
    provisional_values,
    authenticated_distribution_policy,
    stable_apportionment_state,
)
  -> Reject(reason)
  | (
      post_state,
      canonical_destination_distributions,
      next_apportionment_state,
      one_net_balance_patch,
    )

TopLevelStep
  -> Reject with no successor authority
  | one accepted candidate committed at one linearization point
```

Distribution records are receipt evidence of balance changes already present
in the accepted candidate. They are never shell transfer instructions.

## Algorithmic object

### Typed input for one accounting key

Let:

- `D = 10_000`, the fixed basis-point denominator.
- `Roles = (buyback, treasury, rewards)`, fixed by `AlgorithmVersion`.
- `n` be a nonnegative U256 provisional fee amount.
- `w = (w0,w1,w2)`, with every `wi` an integer in `[0,D]` and
  `w0+w1+w2=D`.
- `dest = (d0,d1,d2)`, authenticated destination accounts.
- `k = (fee_distribution_domain_id, asset)`, the stable accounting key.
- `m` be the bounded non-monetary apportionment state for `k`.
- `p` be the authenticated policy and algorithm version.

The policy authority may choose future valid weights after observing all
public state, prior allocations, and current apportionment state.

### Required output

Return:

```text
(a0,a1,a2, m')
```

where each `ai` is a nonnegative integer destination credit and `m'` is the
next bounded non-monetary state.

### Core correctness laws

#### L1. Per-step exact conservation

```text
a0 + a1 + a2 = n
```

No value is deferred as monetary dust, an IOU, or a later debit.

#### L2. Dimensional and authority closure

Every input and output remains under the same `(domain_id, asset)` key.
Destination accounts and weights come from authenticated policy. A command or
keyholder cannot choose them.

#### L3. Adaptive-policy discrepancy

An acceptable dynamic allocator must state and prove a cumulative discrepancy
bound for every role over every valid adaptive sequence:

```text
Q_i(T) = sum[t < T](n_t * w_t,i / D)
A_i(T) = sum[t < T](a_t,i)

abs(A_i(T) - Q_i(T)) <= B_i
```

`B_i` must be a finite protocol constant independent of `T`, amounts, policy
sequence, public state, and policy-operator strategy.

An alternative design may forbid adaptive activation by construction. It must
then prove that every active key uses fixed weights over the declared interval
and specify pending policy, activation, dormant-key, rollback, and liveness
semantics.

#### L4. Stable-domain continuity

Ordinary account, destination, or policy rotation cannot create a fresh
apportionment state. Domain creation, split, merge, and retirement require an
explicit migration relation proving that no parallel fresh domain can claim
the same fee stream.

#### L5. Determinism and canonical order

The same canonical inputs produce byte-identical allocation, state, and
receipt evidence. Every tie-break and iteration order is versioned.

#### L6. U256 closure

No intermediate relies on `q+n`, `n*D`, `n*wi`, or a signed narrowing
operation that exceeds the declared runtime domain. Periodic decomposition is
available:

```text
cycles, r = divmod(n,D)
q' = (q + r) mod D
```

Python and Rust pseudocode must identify every checked operation and use
identical floor, remainder, and tie-break semantics.

#### L7. Bounded resources

Worst-case work and state are explicit and independent of the numeric magnitude
of `n`. A per-atom loop over a U256 amount is forbidden. A loop bounded only by
the fixed denominator must be justified against the per-step key limit.

#### L8. Rejection atomicity

Any invalid policy, state, lineage, amount, migration, or resource bound
returns a typed reject with no successor, patch, distribution, receipt
authority, or partial state.

#### L9. Replacement provisional lineage

Each provisional fee must bind one settlement occurrence and prove:

```text
sender_input_debit
  = pool_input_reserve_credit + provisional_protocol_fee_credit
```

The witness also binds intent, pool, asset, authenticated quote, fee policy,
and exact replay identity. The global candidate consumes every witness exactly
once.

#### L10. Explicit V2 accepted language

V1 permits a protocol-recipient fee credit from an earlier fill to fund a later
same-batch intent. A non-spendable provisional value removes that behavior.
Any selected V2 design must explicitly choose one rule:

1. V2 forbids same-batch spending of provisional fees and is versioned as a
   different accepted language.
2. V2 permits such spending and defines exact provisional consumption without
   double allocation.

The first rule is the current smaller default. The research may reject it only
with a complete alternative relation.

#### L11. Same-key temporal fragmentation

The report must test:

```text
allocate(m,w,a+b)
```

against:

```text
(x,m1)=allocate(m,w,a)
(y,m2)=allocate(m1,w,b)
```

and state whether `(x+y,m2)` must equal the one-step result. A failure is
acceptable only when the protocol deliberately permits schedule-dependent
rounding, quantifies its bound, and explains why callers cannot obtain an
unauthorized economic advantage.

#### L12. Versioning and migration

State, policy, algorithm, tie-break, role order, encoding, and activation
rules are versioned. V1 scalar dust migrates only when `dust=0`; nonzero dust
rejects because it has no recoverable unit or authority owner.

## Known counterexamples and negative knowledge

### C1. Adaptive scalar cursor

For `D=4`, one atom per epoch, and public cursor `q`, choosing:

```text
q=0 -> (3,0,1)
q=1 -> (1,1,2)
q=2 -> (2,0,2)
q=3 -> (4,0,0)
```

gives role 2 an excess of `7/4` atoms every four epochs. The excess is
unbounded under repetition.

### C2. Source-account rotation

Keying state by `(protocol_fee_recipient,asset)` lets ordinary recipient
rotation create a fresh zero state. Repeated rotation recreates reset
amplification.

### C3. V1 same-batch spending

The existing regression
`test_strong_validator_exact_out_protocol_fee_credit_feeds_later_replay`
shows an earlier fee credit funding a later same-batch intent. Removing the
balance credit changes acceptance.

### C4. Provisional lineage

The current replay witness depends on the protocol-recipient balance atom.
Removing that atom requires the replacement conservation witness in L9.

### C5. Hierarchical mechanical-word interval bound

At `D=10_000`, weights `(1,9998,1)`, cursor `1`, amount `9998`, role 1
interval discrepancy is `1.9996`. A `<1` claim is false.

### C6. U256 cursor intermediate

For `n=2^256-1` and positive cursor, `q+n` needs 257 bits. Use the remainder
formula in L6.

### C7. Dynamic deficit-vector fragmentation

The leading dynamic error-vector hypothesis can preserve a sub-one-atom
cumulative error while failing exact same-policy fragmentation.

With `D=4`, weights `(1,1,2)`, zero initial deficit, and fixed tie-break:

```text
one step n=3 -> allocation (1,1,1)
split n=1;2 -> combined allocation (1,0,2)
```

This counterexample does not refute bounded discrepancy. It forces an explicit
L11 decision or a stronger allocator.

## Candidate families to compare

At minimum:

1. **Cycle-closed fixed-weight mechanical cursor.**
   - Scalar state and exact fixed-policy fragmentation.
   - Must solve pending activation, dormant keys, synchronized policy
     semantics, rollback, and liveness.
2. **Dynamic cumulative deficit or entitlement vector.**
   - Likely two independent signed numerators for three roles.
   - Must prove the adaptive bound, exact nonnegative per-step output, U256
     arithmetic, tie-break semantics, and L11 behavior.
3. **Atom-stream scheduler with bounded jump-ahead.**
   - May preserve fragmentation by defining a sequential schedule.
   - Must avoid U256-proportional work and prove the jump-ahead equivalence.
4. **Another structurally different candidate.**
   - Reduction to online rounding, discrepancy theory, fair queueing, divisor
     apportionment, rotor routing, or another known family is preferred over an
     unsupported novelty claim.

Include a correct brute-force or direct sequential oracle for small
denominators.

## Optimization order

1. Per-asset value conservation and authority closure.
2. Safety under an adaptive or compromised policy operator.
3. Stable-domain continuity and explicit accepted-language semantics.
4. Deterministic Python/Rust arithmetic and bounded resource use.
5. Exact migration and canonical receipt/root binding.
6. Smaller state and proof surface.
7. Tighter fairness or fragmentation bounds.

Lower-ranked improvements cannot compensate for a higher-ranked failure.

## Required evidence

An acceptable selection includes:

- a mathematical proof with explicit assumptions;
- an executable bounded model or exhaustive oracle;
- the existing C1-C7 counterexamples as regression cases;
- adaptive policy sequences chosen from public state;
- account/domain rotation and migration traces;
- `n` at `0`, `1`, `D-1`, `D`, `D+1`, and `2^256-1`;
- zero weights, concentrated weights, all tie surfaces, and destination aliases;
- Python/Rust pseudocode with exact integer semantics;
- state and canonical-encoding inventory;
- complexity and maximum-state bounds;
- explicit nonclaims and tool failures.

Lean, ESSO, SMT, and scripts each establish different evidence. A bounded ESSO
run does not replace a parameterized proof. A Lean arithmetic theorem does not
establish runtime refinement or policy completeness.

## Forbidden outcomes

- Reuse of monetary dust or a future debit claim.
- A state key controlled by the keyholder or ordinary destination rotation.
- A fairness proof assuming policy choices are independent of public state.
- A per-atom loop proportional to a U256 amount.
- Silent V1/V2 acceptance equivalence.
- A provisional credit without replacement replay lineage.
- Shell execution of distribution evidence.
- Cross-asset or cross-domain aggregation.
- Floats, host-width casts, unspecified tie-breaks, or iteration-order
  dependence.
- Claiming a sampled experiment proves an unbounded theorem.
- Editing runtime authority during this review-only checkpoint.

## Terminal condition

This research task is complete when one candidate:

1. satisfies every hard law, with L11 explicitly decided;
2. survives the shared counterexample corpus;
3. has a proof plan and replayable evidence adequate for independent review;
4. specifies policy lifecycle, stable key, state, encoding, migration, and
   Python/Rust semantics;
5. yields an exact amendment delta for the frozen P4B5A packet;

or when all compared candidates are rejected with minimized counterexamples and
the next smaller unresolved question is identified.
