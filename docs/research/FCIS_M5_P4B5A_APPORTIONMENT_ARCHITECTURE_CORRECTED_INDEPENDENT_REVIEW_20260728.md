# FCIS M5-P4B5A corrected apportionment architecture: independent review

**Outcome:** `CORRECTED_REVIEW_NO_GO_DYNAMIC_POLICY`

**Narrow retained result:**
`KEEP_BPRIME_KEEP_MECHANICAL_CURSOR_FOR_FIXED_WEIGHTS_ONLY`

The corrected report repairs all seven findings from the first independent
review. Its provisional-credit composition, non-monetary state, fixed role
order, periodic amount decomposition, and net alias-aware patch are useful
advances. A new P0 counterexample refutes the proposed policy-change rule:
preserving one scalar cursor does not bound cumulative discrepancy when an
authenticated policy authority may choose weights adaptively.

This review authorizes no packet amendment, implementation, mount, migration,
or claim promotion.

## 1. Pinned review surface

```text
committed head:
  c4879d8a570ad0418ccb8778ab9ea401ad0c5aca

tracked git diff HEAD sha256:
  68e0298b987778240080f32bb894f209ed1f14df52ca5318bc8d810b9c29bc27

corrected report sha256:
  193691ddd2412d154d3f06e6d2f0fecca58dc870eafa5c8a5ed3fce6d8de3b2a

counterexample script sha256:
  9fcb8ff5384f61ddffc0d14418cbdc75a9f2029445cef32a658c753af5f153fc

ESSO model file sha256:
  40e28937747fd757395714e2fbacd0bc10fbbe0a1aeedd01937a546ddc40c1c5

ESSO canonical IR hash:
  sha256:e545a99944cda9f89b341f1e3ca59da411f5a34e7b9d77f5e1cdfc20f33b6cce
```

The tracked diff hash matches the corrected report. It does not cover untracked
files. A complete evidence handoff still needs a deterministic manifest for the
corrected report, both prior reviews, prompt, ESSO model, witness script, and any
other untracked artifacts.

The current Python and Rust WIP remains contradictory and unmounted. Python
uses the earlier contiguous block cursor and gross source-balance debit. Rust
uses monetary dust. This review assessed architecture and counterexamples only.

## 2. Finding summary

| Finding | Priority | Verdict |
|---|---:|---|
| ADAPTIVE-POLICY-ROUNDING-008 | P0 | Confirmed reachable counterexample; dynamic-weight cursor claim refuted |
| CURSOR-KEY-ROTATION-009 | P0 | Source-account key permits reset through account rotation |
| ACCEPTED-LANGUAGE-CONTRACTION-010 | P0 | Existing V1 explicitly permits later same-batch spending of a fee credit |
| PROVISIONAL-LINEAGE-011 | P0 | Current proof depends on the balance atom the corrected design removes |
| ROLE1-INTERVAL-BOUND-012 | P1 | Claimed `< 1` bound is false; witnessed discrepancy is `1.9996` |
| U256-CURSOR-INTERMEDIATE-013 | P1 | `q + n` can exceed 256 bits; use the decomposed remainder |
| EVIDENCE-MANIFEST-014 | P1 | Tracked diff hash omits untracked evidence files |

## 3. ADAPTIVE-POLICY-ROUNDING-008

### Violated claim

The corrected report states that cursor preservation prevents repeated policy
changes from recreating rounding amplification and limits policy-change
rounding influence to fewer than two atoms per role.

That conclusion holds for fixed weights and for the report's sampled
non-adaptive experiments. It fails when the policy authority selects weights
from the current public cursor position.

### Minimal reachable witness

Use `D = 4`, one fee atom per epoch, and preserve the cursor. Select:

| Cursor | Weights `(w0,w1,w2)` | Role 2 allocation | Role 2 ideal |
|---:|---:|---:|---:|
| 0 | `(3,0,1)` | 1 | 1/4 |
| 1 | `(1,1,2)` | 1 | 1/2 |
| 2 | `(2,0,2)` | 1 | 1/2 |
| 3 | `(4,0,0)` | 0 | 0 |

After four epochs, role 2 receives `3` atoms against ideal `5/4`, an excess of
`7/4`. The fifth epoch returns to cursor zero, allocates another role-2 atom,
and raises cumulative excess to `5/2`. Every four-epoch cycle adds `7/4` excess,
so repetition makes the deviation unbounded.

ESSO modeled the exact reachable prefix. Z3 and cvc5 agreed on the transition:

```text
pre:  steps=4, cursor=0, role2_actual=3, role2_ideal_numerator=5
post: steps=5, cursor=1, role2_actual=4, role2_ideal_numerator=6

discrepancy = (4*4 - 6) / 4 = 5/2 atoms
```

The two deterministic ESSO trials produced fingerprint:

```text
5a59340aa8588fd8a23e6ba92907421c5ce590de6a7ea968260e94187b5618a5
```

At production denominator `D = 10_000`, a 100-epoch deterministic trace gives:

```text
role2 actual = 100
role2 ideal  = 20967 / 5000 = 4.1934
role2 excess = 479033 / 5000 = 95.8066
```

The witness uses a restricted policy family `(10_000-w2, 0, w2)` and chooses
the smallest `w2` that assigns the current atom to role 2. It therefore does not
depend on role-1 complexity.

### Required architecture decision

The packet must choose one of these explicit models before amendment:

1. **Cycle-closed weight activation.** Each accounting key retains its current
   weights until the cursor reaches zero after a complete canonical period.
   Pending policy state, activation ordering, dormant keys, destination changes,
   rollback, and receipts then become part of the protocol.
2. **Dynamic-weight entitlement state.** Replace the phase-only cursor with a
   per-role cumulative error or entitlement machine whose invariant is defined
   against the sum of time-varying fractional quotas. This likely restores the
   error-vector candidate as a leading design.
3. **Another proved dynamic allocator.** It must quantify over adaptive policy
   sequences and retain a bounded cumulative discrepancy theorem.

Governance authentication alone does not close this finding. The repository's
threat model includes a compromised or strategically acting policy operator.

## 4. CURSOR-KEY-ROTATION-009

The current value type keys cursor state by:

```text
(source_account_pubkey, asset)
```

The corrected provisional design says the source account names lineage and no
longer names a debited balance. Rotating the configured protocol fee recipient
therefore creates a fresh key at cursor zero. Repeated account rotation
reintroduces reset amplification without invoking a reset API.

Use a stable semantic key such as:

```text
(fee_distribution_domain_id, asset)
```

The domain identifier must come from authenticated deployment policy, remain
independent of a keyholder account, and have controlled migration and duplicate
rules. If source accounts remain in the key, every source rotation needs an
explicit one-to-one cursor migration that prevents fresh parallel domains.

## 5. ACCEPTED-LANGUAGE-CONTRACTION-010

The corrected report says removing the ordinary recipient balance credit adds
no accepted-language contraction. The current V1 behavior has a dedicated
regression proving the opposite:

```text
test_strong_validator_exact_out_protocol_fee_credit_feeds_later_replay
```

The protocol recipient starts with zero asset-in balance. An earlier swap
credits a protocol fee of 15, and a later intent from that recipient spends 10
in the same batch. The later fill succeeds and strong replay accepts it.

Making the fee credit non-spendable causes the later settlement replay to
reject before the apportionment phase. The new design removes a fee-phase reject
while moving the rejection earlier. The accepted language still contracts.

The architecture must choose and version one semantic rule:

- preserve the V1 profile and introduce an explicitly different V2 accepted
  language where provisional fees cannot fund later intents; or
- define how same-batch spending consumes provisional value and how the
  remaining distributable amount is derived without double allocation.

The first option is smaller and easier to verify. It requires retiring the
claim that V2 is acceptance-equivalent to V1.

## 6. PROVISIONAL-LINEAGE-011

The current strong validator constructs each `ProtocolFeeCreditV2` beside a
protocol-recipient balance atom and stores them together in
`_ProtocolFeeReplayAtomV2`. The corrected design removes that balance atom.
Consequently, it cannot retain "the same lineage proof as today."

The new controlled provisional witness must bind at least:

```text
settlement occurrence and intent identity
asset and pool identity
authenticated quote and protocol-fee policy
sender debit atom
pool reserve credit atom
provisional protocol-fee credit
```

It must recompute the per-swap conservation relation:

```text
sender_input_debit
  = pool_input_reserve_credit + provisional_protocol_fee_credit
```

The global candidate must consume each witness exactly once. Omitting this
replacement proof can turn a typed provisional credit into unbacked value.

## 7. ROLE1-INTERVAL-BOUND-012

The report's sampled `< 1` role-1 interval bound is false. At:

```text
D = 10_000
weights = (1, 9_998, 1)
q = 1
n = 9_998
```

role 1 receives `9_998` atoms against ideal `24990001/2500`, producing excess
`4999/2500 = 1.9996` atoms.

The safe interval-discrepancy statement derived from the prefix bounds is:

```text
abs(role0 interval discrepancy) < 1
abs(role1 interval discrepancy) < 2
abs(role2 interval discrepancy) < 2
```

Any tighter role-1 claim needs a separate proof and exhaustive boundary search.

## 8. U256-CURSOR-INTERMEDIATE-013

Periodic decomposition is the right repair for U256-sized fee amounts. One
formula remains inconsistent with its no-wide-intermediate claim:

```text
q' = (q + n) mod D
```

For `n = 2^256-1` and `q > 0`, `q+n` requires 257 bits. Python and Rust
`BigUint` can evaluate it, although a strict checked-U256 implementation cannot.
The decomposed formula is exact and bounded:

```text
r = n mod D
q' = (q + r) mod D
```

Python, Rust, generated references, and proof models should use that form.

## 9. EVIDENCE-MANIFEST-014

The corrected report's tracked patch hash is accurate. `git diff HEAD` excludes
untracked reports, prompts, models, and witness files. Before review handoff,
generate a deterministic manifest containing every evidence path, size, and
SHA-256, plus the committed head and tracked diff hash. Export any Research
Kernel evidence used by the packet because atom identifiers are not portable
between the two observed kernel instances.

## 10. Retained architecture

The following direction survives this review:

```text
exact settlement replay
  -> controlled provisional protocol-fee values with replacement lineage proof
  -> deterministic apportionment under an explicit policy-lifecycle rule
  -> stable per-domain/per-asset apportionment state
  -> one net canonical balance patch
  -> one candidate, receipt, replay update, and atomic commit bundle
```

The hierarchical mechanical-word allocator remains a strong fixed-policy
candidate. Conservation, per-period exactness, and same-policy split/merge
telescoping remain intact. Its scalar minimality does not extend to arbitrary
time-varying weights.

## 11. Evidence executed

```text
python3 docs/research/FCIS_M5_P4B5A_APPORTIONMENT_COUNTEREXAMPLES_20260728.py
  PASS

ESSO validate FCIS_M5_P4B5A_ADAPTIVE_POLICY_COUNTEREXAMPLE_D4.esso.yaml
  PASS
  IR sha256:e545a99944cda9f89b341f1e3ca59da411f5a34e7b9d77f5e1cdfc20f33b6cce

ESSO verify-multi <model> --solvers z3,cvc5 --determinism-trials 2
  EXPECTED FAIL: one reachable counterexample
  solvers agreed: yes
  inconclusive: 0

ruff check counterexample script
  PASS

ruff format --check counterexample script
  PASS

corrected report appendix witness script
  PASS
```

Research Kernel recorded the adaptive-policy witness as
`atom_f07e57a110ed4474` with ESSO evidence
`evidence_6735a448216a4b81`.

TheoremSearch returned adjacent online-discrepancy material and no direct Lean
declaration for the required periodic floor identity. It supplied retrieval-only
prior art and did not influence the counterexample verdict.

## 12. Commands not run and nonclaims

- No Lean theorem was attempted because the dynamic-policy claim is false.
  Lean remains appropriate for the surviving fixed-policy conservation,
  periodicity, telescoping, and prefix-bound lemmas after the policy lifecycle
  is frozen.
- No Python or Rust runtime implementation was changed or tested.
- No canonical encoder, decoder, golden vector, receipt, state-root, migration,
  commit-bundle, or mount claim was promoted.
- No global optimality claim is made for the mechanical-word or error-vector
  families.
- No production policy-authority compromise bound is assumed.

## 13. Next safest checkpoint

Run a review-only dynamic-policy design comparison before amending P4B5A:

1. fixed-weight cycle-closed activation with stable domain keys;
2. dynamic-weight cumulative error/entitlement state;
3. any smaller candidate that survives the ESSO adaptive sequence.

The comparison must include the existing D=4 and D=10,000 counterexamples,
source-account rotation, same-batch fee-recipient spending, replacement
provisional-credit lineage, U256 decomposition, Python/Rust byte semantics, and
policy migration. Freeze the packet only after one design has a bounded
adaptive-policy theorem or explicitly forbids adaptive activation by
construction.
