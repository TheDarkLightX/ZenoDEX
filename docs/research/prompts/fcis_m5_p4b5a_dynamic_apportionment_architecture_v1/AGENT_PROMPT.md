# Independent architecture task: break the P4B5A dynamic apportionment blocker

You are an independent architecture and algorithm reviewer for ZenoDEX FCIS.
Work read-only against the source-pinned packet. Do not inspect another agent's
answer before completing your first report.

## Objective

Select the smallest deterministic protocol-fee apportionment architecture that
remains correct under:

- arbitrary U256 fee amounts;
- mixed assets and stable distribution domains;
- an authenticated policy operator that may act strategically after observing
  all public state;
- policy and destination changes;
- account rotation;
- Python/Rust exact replay;
- one atomic FCIS decision and commit.

If no candidate meets the contract, return a minimized no-go result and the
next smallest research question.

## Source-pinned context

Baseline:

```text
c4879d8a570ad0418ccb8778ab9ea401ad0c5aca
```

Read, in order:

1. `docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/PROBLEM_CONTRACT.md`
2. `docs/research/FCIS_M5_P4B5A_PREFLIGHT_20260728.md`
3. `docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_REVIEW_20260728.md`
4. `docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_INDEPENDENT_REVIEW_20260728.md`
5. `docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_20260728.md`
6. `docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md`
7. `docs/research/FCIS_M5_P4B5A_APPORTIONMENT_COUNTEREXAMPLES_20260728.py`
8. `docs/research/FCIS_M5_P4B5A_DYNAMIC_APPORTIONMENT_COUNTEREXAMPLES_20260728.py`
9. `docs/research/FCIS_M5_P4B5A_ADAPTIVE_POLICY_COUNTEREXAMPLE_D4.esso.yaml`
10. the original frozen packet under
    `docs/research/prompts/fcis_m5_p4b5a_fee_dimensions_and_custody_v1/`

Run `check_packet.py` before relying on the context.

## Fixed system boundary

Preserve:

```text
exact settlement replay
  -> controlled provisional protocol-fee values
       with a replacement conservation witness
  -> deterministic apportionment
  -> stable per-domain/per-asset non-monetary state
  -> one net destination-credit balance patch
  -> one decision, receipt, replay update, and atomic commit bundle
```

Distribution records are evidence of already-applied state changes. They are
never executable shell transfers.

The stable state key is based on an authenticated
`fee_distribution_domain_id` plus asset. Ordinary source-account, destination,
or weight changes cannot create fresh state.

## Central theorem or construction

For each role `i`, define:

```text
Q_i(T) = sum[t<T](n_t*w_t,i/D)
A_i(T) = sum[t<T](a_t,i)
```

Either:

1. give a dynamic allocator and prove a finite constant `B_i` such that

   ```text
   abs(A_i(T)-Q_i(T)) <= B_i
   ```

   for every time `T` and every valid adaptive policy sequence; or

2. give a construction that makes adaptive activation unrepresentable and
   prove its fixed-policy interval, activation, and liveness laws.

Every step must produce nonnegative integer allocations summing exactly to the
fresh provisional amount. No monetary carry, future debit, or cross-key value
is permitted.

## Required candidate comparison

Compare at least:

1. cycle-closed fixed-weight mechanical cursor;
2. dynamic cumulative deficit or entitlement vector;
3. bounded jump-ahead atom-stream scheduler;
4. one additional candidate or a justified reduction showing why another
   family adds no value.

Use known online-rounding, discrepancy, apportionment, fair-queueing, or
rotor-routing results where applicable. Cite primary sources. Retrieval informs
the proof plan and carries no authority by itself.

## Mandatory attacks

Your selected candidate must face:

1. the `D=4` adaptive scalar-cursor trace;
2. the production-denominator adaptive trace;
3. fresh-state creation through source or destination rotation;
4. same-batch protocol-recipient spending;
5. missing replacement provisional lineage;
6. role-1 discrepancy `1.9996`;
7. `n=2^256-1` with a nonzero state;
8. concentrated and zero-weight policies;
9. every deterministic tie surface;
10. same-key fragmentation, including:

    ```text
    D=4, w=(1,1,2), state=zero
    whole n=3 versus split n=1 then n=2
    ```

11. destination aliasing and full aliasing;
12. domain split, merge, retirement, and rollback.

Run bounded exhaustive exploration on small denominators. Preserve every
counterexample. State exactly which results were executed, proved, sampled, or
left proposed.

## Required architecture details

Specify:

- exact transition algebra;
- state type and invariant;
- stable domain identity and authority;
- policy lifecycle and activation;
- tie-break and role order;
- U256-safe Python and Rust pseudocode;
- worst-case time, memory, and state bounds;
- canonical fields, tags, and algorithm version;
- V1 zero-dust migration and nonzero-dust rejection;
- V2 same-batch spending semantics;
- replacement provisional lineage witness;
- receipt, patch, state-root, and commit-bundle bindings;
- formal, property, differential, mutation, and stateful tests;
- exact amendment text or decision table for the frozen P4B5A packet.

## Decision rule

Rank lexicographically:

1. value conservation and authority closure;
2. adaptive-policy safety;
3. stable-domain and accepted-language correctness;
4. deterministic bounded Python/Rust execution;
5. migration and canonical binding;
6. state and proof simplicity;
7. fairness and fragmentation strength.

Reject any candidate that fails a higher-ranked item, regardless of gains below
it.

## Evidence discipline

Claim labels:

- `PROVED_UNDER_STATED_ASSUMPTIONS`
- `BOUNDED_EXHAUSTIVE`
- `EMPIRICALLY_SUPPORTED`
- `PLAUSIBLE_HYPOTHESIS`
- `FALSIFIED`
- `UNKNOWN`

Solver `UNKNOWN`, unavailable tooling, timeout, disagreement, or missing replay
is `UNKNOWN`. A passing bounded model cannot promote an unbounded claim.

## Deliverable

Return one Markdown report using `RESPONSE_TEMPLATE.md`. Include:

- exact baseline and files inspected;
- one-sentence verdict;
- candidate table;
- selected algebra or no-go counterexample;
- proof obligations and evidence;
- all required architecture details;
- exact packet-amendment proposal;
- explicit nonclaims and residual risks;
- replay commands.

Do not modify runtime source, commit, push, mount, merge, or weaken prior
evidence. The report is advisory until independently reviewed and committed by
the primary reviewer.
