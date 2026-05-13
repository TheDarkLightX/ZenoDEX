---
title: UPBA Audited-Set Optimality Certificate
type: note
permalink: autonomous-tau-dex-review/docs/upba-optimality-certificate
---

# UPBA Audited-Set Optimality Certificate

This note records the first runtime bridge from the UPBA optimality theorem to a
deterministic checker.

The checker lives in `src/core/uniform_batch_optimality.py`.

## Game Surface

Players and roles:

- solver proposes a UPBA clearing candidate;
- verifier receives a finite audited candidate set;
- verifier checks whether the declared winner is weakly optimal inside that
  audited set.

State:

- candidate id;
- integer matched volume;
- integer surplus.

For a value-moving UPBA settlement candidate, the candidate id is derived from
the UPBA certificate hash:

```text
candidate_id :=
  H(domain = uniform_batch_optimality_winner_binding,
    schema = zenodex/uniform_batch_optimality_winner_binding/v1,
    uniform_batch_certificate_hash)
```

This makes the winner id a commitment to the actual UPBA settlement certificate,
rather than an arbitrary solver label.

Objective:

```text
volume first, surplus second
```

The checker accepts when no audited candidate has greater volume, and no audited
candidate with equal volume has greater surplus.

## Attack Query

The local deviation condition is:

```text
exists candidate in audited_set:
  candidate.volume > winner.volume
  or
  candidate.volume = winner.volume and candidate.surplus > winner.surplus
```

The verifier rejects exactly this condition.

The bound-verifier deviation condition is stronger:

```text
winner_id != candidate_id_for(uniform_batch_certificate_hash)
```

The verifier rejects this before accepting the optimality proof, so an audited
optimality certificate cannot be presented for a different UPBA settlement.

## Certificate Shape

```text
UniformBatchOptimalityCertificateV1 :=
  schema
  objective_id
  candidate_set_hash
  winner_id
  volume_upper
  surplus_upper_at_winner_volume
  candidates
```

The schema is:

```text
zenodex/uniform_batch_optimality_certificate/v1
```

The objective id is:

```text
zenodex/upba/lexicographic_volume_then_surplus/audit_set_v1
```

Candidate sets are committed with:

```text
zenodex/uniform_batch_optimality_candidate_set/v1
```

The candidate-set hash sorts candidate ids before hashing. The certificate body
itself requires candidates to be sorted by `candidate_id`, so its hash remains
canonical.

## Runtime Checks

The verifier enforces:

- closed schemas for certificate and candidates;
- non-empty sorted candidate list;
- unique candidate ids;
- bounded non-negative integer volume and surplus;
- `winner_id` references exactly one candidate;
- `candidate_set_hash` matches the candidate list;
- `winner.volume = volume_upper`;
- `winner.surplus = surplus_upper_at_winner_volume`;
- every candidate volume is `<= volume_upper`;
- every candidate with `volume = volume_upper` has surplus
  `<= surplus_upper_at_winner_volume`.

The bound verifier additionally enforces:

- the supplied UPBA certificate is hash-valid under the UPBA verifier schema;
- direct certificate-hash binding inputs must be canonical `0x`-prefixed
  lowercase SHA-256 hex;
- `winner_id` equals the domain-separated candidate id derived from that UPBA
  certificate hash.

## Formal Boundary

The Lean theorem file is `lean-mathlib/Proofs/UniformBatchOptimality.lean`.

It proves:

- fixed-price aggregate volume upper bound;
- aggregate clearing feasibility;
- fixed-price aggregate volume optimality;
- finite audit-set upper-bound certificates imply weak optimality inside the
  audited candidate list;
- runtime-strengthened audit certificates imply the winner is both present and
  weakly optimal inside the audited candidate list.

The Python checker implements the runtime-strengthened certificate predicate. It
also adds runtime hygiene that the theorem leaves abstract: canonical hashes,
closed schemas, sorted unique ids, and integer domain bounds.

The bound verifier implements the next runtime obligation:

```text
winner_id = candidate_id_for(uniform_batch_certificate_hash)
```

This is a hash-binding obligation, so it is kept in Python rather than modeled
as arithmetic in Lean.

## Non-Claims

This certificate does not prove:

- the audited set is complete;
- the solver searched every admissible price;
- the admission set is fair;
- censorship resistance;
- oracle safety;
- global MEV elimination.

The bound verifier also does not prove that the UPBA settlement certificate is
accepted against live balances and pool state. It proves that the optimality
certificate's winner id is bound to the supplied UPBA certificate hash. The
normal UPBA settlement verifier still has to accept that certificate in its own
runtime context.

The claim is deliberately local:

```text
given this finite audited candidate set,
the declared winner is weakly optimal by volume first and surplus second
```

## Replay

```bash
pytest -q tests/core/test_uniform_batch_optimality.py
```

Adjacent UPBA checks:

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```

Lean:

```bash
cd lean-mathlib
~/.elan/bin/lean Proofs/UniformBatchOptimality.lean
```
