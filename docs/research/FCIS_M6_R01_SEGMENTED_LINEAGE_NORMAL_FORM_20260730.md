# FCIS M6-R01 Segmented Lineage Normal Form

**Date:** 2026-07-30  
**Status:** `RESEARCH_ONLY_EXECUTABLE_LEAN_UNMOUNTED`  
**Base:** PR #496 head `557cfaaca79318a1757124fd61625433de82b105`  
**Targets:** M6-R01 canonical fee-occurrence semantics; first identity pair for M6-R04

## 1. Frozen decision

A **witness occurrence** is one exact fill-bound fee witness at one canonical
position in one accepted settlement transition.

An **allocator occurrence** is one key coordinate of the transition-local fee
amount vector:

```text
(fee_distribution_domain_id, asset) -> aggregate U256 amount
```

An **allocator occurrence stream is nested, not flat**:

```text
accepted transition 0:
  key-ordered allocator occurrences
accepted transition 1:
  key-ordered allocator occurrences
...
```

For semantic key set `K`, its carrier is

$$
\mathcal O_K = \left(\mathbb N^{(K)}\right)^*.
$$

The inner finite-support amount vector is commutative: same-key witnesses inside
one accepted transition can be permuted and summed. The outer word is ordered:
accepted-transition segments compose only by concatenation. The exact ordered
witness tuple remains available as provenance and is never replaced by the
grouped amounts.

This resolves the four candidate interpretations:

```text
raw fill
  source from which a fee witness may be derived

settlement witness
  exact provenance occurrence

same-key group inside one accepted transition
  one allocator occurrence

whole-transition aggregate
  a finite-support vector of allocator occurrences, not one scalar
```

## 2. Segmented Lineage Normal Form

For transition `t`, let `W_t` be its exact ordered witness tuple. Define

$$
G_t(k)=\sum_{w\in W_t,\;key(w)=k} amount(w).
$$

The semantic history is

$$
N(W_0,\ldots,W_{m-1})=[G_0,\ldots,G_{m-1}],
$$

not the global sum `sum_t G_t`.

The exact witness decomposition is a provenance point above the semantic word:

$$
\pi:\mathcal L_K\rightarrow\left(\mathbb N^{(K)}\right)^*.
$$

`pi` deliberately forgets contributor identities and decomposition. It is
non-injective. The implementation therefore derives two independent identities:

```text
semantic root
  exact arithmetic occurrence vector and transition word

lineage root
  exact ordered witness decomposition over that semantic point
```

One witness of `867` and two same-segment witnesses `493,374` may have the same
semantic root but must have different witness-tuple and lineage roots.

## 3. Why the outer word is necessary

The current allocator groups all contributions by `FeeApportionmentKeyV2`
inside one call, orders the keys by `protocol_order_key`, and evaluates one
state transition per grouped key. That behavior is sound only when the call
boundary equals one accepted-transition boundary.

For one stateful entitlement key, in general

$$
A_s(a+b)\ne A_{A_s(a).state}(b).
$$

The first accepted occurrence changes the persistent deficit used by the next.
Therefore no caller may combine witnesses from multiple accepted transitions
into one allocator invocation without a separate equivalence proof.

## 4. Stronger boundary counterexample

The prior checkpoint retained:

```text
D = 10
weights = (5,2,3)
whole 867       -> (434,173,260)
split 493 + 374 -> (433,174,260)
```

This checkpoint adds a smaller zero-history counterexample at the production
denominator:

```text
D = 10,000
weights = (2,500,2,500,5,000)
pre-deficit = (0,0,0)
```

One accepted occurrence of `3`:

```text
fractions    = (7,500,7,500,5,000)
bonuses      = (1,1,0)
allocation   = (1,1,1)
post-deficit = (-2,500,-2,500,5,000)
```

Accepted occurrences `1` then `2`:

```text
amount 1:
  bonuses      = (0,0,1)
  allocation   = (0,0,1)
  post-deficit = (2,500,2,500,-5,000)

amount 2 from that state:
  bonuses      = (1,0,0)
  allocation   = (1,0,1)
  post-deficit = (-2,500,7,500,-5,000)

total allocation = (1,0,2)
```

Thus one occurrence of `3` differs in both allocation and persistent state from
accepted occurrences `1` then `2`.

A complete residue-domain search over every exact three-role weight vector and
every amount pair for denominators below four found no zero-history
counterexample. At `D=4`, weights `(1,1,2)` and split `1+2` are the first
witness. Scaling by `2500` yields the production-denominator example.

## 5. New immutable values

The unmounted module is:

```text
src/core/fcis_fee_occurrence_normal_form.py
```

It defines:

```text
FeeWitnessOccurrenceClaimV1
FeeAllocatorOccurrenceV1
CanonicalFeeOccurrenceSegmentV1
CanonicalFeeOccurrenceHistoryV1
FeeOccurrenceNormalizationRejectV1
```

A source witness claim carries:

```text
canonical position
FeeApportionmentKeyV2
U256 amount
source_witness_root
```

A canonical segment carries:

```text
boundary_root
policy_root
algorithm_version
fixed role order
ordered witness tuple
key-ordered allocator occurrences
witness_tuple_root
semantic_stream_root
lineage_stream_root
```

A canonical history carries an exact tuple of segments and derives:

```text
semantic_word_root
lineage_word_root
```

Its only allocator projection is nested:

```text
tuple[tuple[FeeAmountCandidateV2, ...], ...]
```

There is deliberately no boundary-erasing flat-history API.

`boundary_root`, `policy_root`, and `source_witness_root` are externally supplied
equality targets. Shape validation does not make them authoritative.

## 6. Exact root language

All roots use SHA-256 with:

- an explicit ASCII domain;
- a field count;
- an eight-byte length before each field;
- fixed 32-byte big-endian U256 encoding;
- exact UTF-8 identifier bytes;
- decoded 32-byte digest inputs.

The semantic occurrence root binds:

```text
normal-form version
SRGD algorithm profile
fixed role order buyback < treasury < rewards
boundary root
policy root
fee distribution domain
asset
aggregate amount
```

The lineage occurrence root additionally binds the ordered normalized witness
roots contributing to the semantic occurrence.

The semantic root supports arithmetic replay. The lineage root prevents a
correct grouped amount from being attached to the wrong witness history.

## 7. Exact invariants

For every accepted segment:

```text
positions = 0..witness_count-1
source witness roots are unique
occurrence keys are strictly protocol ordered
sum contributor amounts = occurrence amount
all contributors of an occurrence have its key
contributors retain settlement order
all contributors reconstruct the global ordered witness tuple
sum witness mass = sum allocator-occurrence mass
all same-key aggregates fit U256
all roots rederive from exact fields
zero-amount witnesses remain explicit
```

For every accepted history:

```text
segment order is preserved
boundary roots are unique
semantic word root rederives
lineage word root rederives
projection remains nested by accepted transition
```

## 8. Executable evidence

The new test file is:

```text
tests/core/test_fcis_fee_occurrence_normal_form.py
```

It covers:

1. Same-segment `867` and `493+374`: same semantic root, different lineage root.
2. All raw permutations with fixed canonical positions normalize identically.
3. Distinct keys use the existing protocol order.
4. Per-key contributor fibers reconstruct the global witness tuple.
5. Zero-amount witnesses remain represented.
6. Position gaps and duplicate witness roots reject.
7. Same-key U256 aggregate overflow rejects.
8. Boundary and policy substitution change semantic identity.
9. One segment and two segments with equal total produce different words.
10. The production allocator exhibits `3` versus `1,2` divergence.
11. Exhaustive residue search establishes `D=4` as the smallest zero-history
    denominator under the frozen finite manifest.

The small permutation campaign executes 384 normalized cases in addition to the
adversarial examples.

## 9. Lean surface

The proof module is:

```text
lean-mathlib/Proofs/FCISFeeOccurrenceSemantics.lean
```

It proves:

```text
witness_projection_noninjective
  Grouped amount cannot reconstruct the exact witness decomposition.

global_mass_forgets_transition_boundaries
  Equal global mass does not imply an equal segmented history.

distinct_key_updates_commute
  Different-key product-state updates commute at every observation point.

occurrence_fold_conjugacy
  A one-step interpretation square lifts through the complete ordered fold.

production_whole_bonus
production_first_split_bonus
production_second_split_bonus
  The exact SRGD selector relations used by the production counterexample.

production_split_merge_boundary_counterexample
  Amount 3 and accepted occurrences 1 then 2 differ in allocation and state.
```

The Lean library declares the new module as an explicit root, so the normal
proof build must compile it. The fold theorem is the recursive connective lemma
needed to lift the existing one-step SRGD/AGQE sign dual over an exact occurrence
word. Instantiating it with the complete executable transition remains a later
refinement gate.

## 10. Relation to R02 and R03

R02 fairness theorems must quantify over the exact ordered allocator-occurrence
word, not a global amount sum.

R03 separates persistent state identity from occurrence context:

```text
state identity
  distribution domain
  asset
  semantic algorithm profile
  fixed role order

occurrence context
  active policy root
  accepted boundary root
  exact witness lineage
```

Destination rotation and ordinary policy rotation may change occurrence context
but must not reset the persistent entitlement state.

## 11. First concrete R04 lineage

SLNF supplies the first concrete identity pair for the LineageCube:

```text
semantic_stream_root
lineage_stream_root
```

The next allocator candidate must bind at least:

```text
source settlement root
accepted boundary root
active policy root
current fee-state root
witness tuple root
semantic stream root
lineage stream root
allocator pre-state
allocator post-state
allocations
```

The receipt must recompute those identities from independent sources. Values
copied from a candidate or bundle are equality targets, never authority.

A crossed-lineage mutant must fail even when grouped arithmetic is identical:

```text
candidate arithmetic from witness tuple W1
receipt provenance from witness tuple W2
semantic_root(W1) = semantic_root(W2)
W1 != W2
```

## 12. ATDD contract

```text
R01-1 Same-transition quotient
  Same-key witnesses in one authenticated boundary normalize to one allocator
  occurrence containing their exact U256 sum.

R01-2 Provenance lift
  Equal same-boundary semantic vectors may have different lineage roots.

R01-3 Boundary preservation
  Equal total mass in one segment or two segments yields different words.

R01-4 Canonical input order
  Raw tuple permutation cannot change output when positions are fixed.

R01-5 Distinct-key order
  Occurrences follow FeeApportionmentKeyV2.protocol_order_key.

R01-6 Zero amount
  An exact zero witness remains an explicit occurrence.

R01-7 Overflow
  A same-key aggregate above U256 rejects before allocator evaluation.

R01-8 Minimal stateful falsifier
  Under weights 2500/2500/5000, amount 3 differs from occurrences 1 then 2.

R01-9 No flat history API
  History projection returns one candidate tuple per accepted transition.
```

## 13. Evidence ledger

| Claim | Status | Evidence |
| --- | --- | --- |
| Occurrence carrier is a word of local vectors | `DEFINED` | algebra and immutable values |
| Same-segment grouping is deterministic | `TESTED` | permutation and grouping campaigns |
| Witness projection is non-injective | `PROVED` | Lean theorem |
| Global sum forgets boundaries | `PROVED` | Lean theorem |
| Different-key updates commute | `PROVED_POINTWISE` | axiom-free Lean theorem |
| One-step relation lifts through a fold | `PROVED_CONDITIONALLY` | generic Lean induction |
| Production split/merge is unsound | `PROVED_AND_TESTED` | Lean relations and Python allocator |
| `D=4` is bounded-search minimal | `TESTED` | exhaustive frozen manifest |
| Settlement replay derives witnesses | `GAP` | no source-bound extractor |
| Boundary and policy roots are authenticated | `GAP` | external equality targets only |
| Python/Rust root parity | `GAP` | no Rust codec or golden vectors |
| Candidate and receipt bind both roots | `GAP` | next R04 face |
| Runtime no-bypass | `UNMOUNTED` | R12 later gate |

## 14. Falsifiers

Reject or revise this checkpoint if:

- fixed-position input permutation changes any output field;
- witness mass and grouped mass differ;
- contributor fibers cannot reconstruct the witness tuple;
- a zero witness disappears;
- a same-key aggregate above U256 reaches the allocator;
- policy or boundary substitution leaves semantic identity unchanged;
- witness decomposition substitution leaves lineage identity unchanged;
- a flat history projection enters an authority path;
- the production `3` versus `1,2` result disagrees with the current allocator;
- a denominator below four produces a zero-history residue-domain witness under
  the same manifest;
- a candidate or receipt accepts crossed semantic and lineage roots.

## 15. Nonclaims and next checkpoint

This work does not derive fee witnesses from settlement replay, authenticate any
root, change the existing allocator or committed-state schema, create a decision
or receipt, prove Rust parity, mount a value-moving path, or establish M6
promotion.

The smallest safe next checkpoint is:

1. derive `FeeWitnessOccurrenceClaimV1` from the exact settlement index/replay;
2. independently recompute the accepted boundary and active policy roots;
3. construct an immutable allocator candidate carrying both SLNF roots;
4. prove and test the candidate-to-receipt face of the concrete LineageCube;
5. add crossed-lineage, foreign-policy, and foreign-boundary mutants.
