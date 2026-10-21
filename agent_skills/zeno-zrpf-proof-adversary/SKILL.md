---
name: zeno-zrpf-proof-adversary
description: Adversarially test ZRPF and RISC Zero across semantic input, guest execution, journal, receipt image and profile, recursive child coverage, fresh authority, and atomic admission. Use for zk/zrpf_protocol, zk/zrpf_risc0, RISC Zero guest/host/verifier code, proof manifests, journals, profiles, image IDs, recursive roots, and proof-backed ZenoLedger admission.
---

# Zeno ZRPF Proof Adversary

## Core equality chain

Establish the intended chain and name any untested equality:

```text
Intended semantic transition
 = guest input interpretation
 = guest execution result
 = complete canonical journal
 = receipt under exact image and profile
 = exact recursive child manifest and composition
 = host request under current release, policy, and state
 = atomic durable ledger effect
```

A verified receipt authenticates guest execution and committed journal bytes. It
cannot authorize omitted semantics.

## Fault matrix

Start with one valid retained control. Mutate one authority coordinate per row
and record the earliest reject boundary, exact error, and no-effect snapshot.

- Semantic/guest input: omitted or substituted field, null ambiguity, wrong
  domain/epoch/version, caller-supplied identity, overflow/rounding boundary.
- Journal: omitted, duplicate, reordered, unknown, trailing, alternate, or
  oversized row; count/root/inventory disagreement; self-consistent incomplete
  summary.
- Receipt/profile: wrong image, kind, hash suite, control ID, verifier
  parameters, seal, journal, dev mode, stale or revoked release.
- Recursive coverage: missing, duplicate, substituted, aliased, wrong role,
  ordinal, profile or release; permutation, padding, extra child, topology-root
  substitution, or parent statement missing exact child-set binding.
- Fresh context: stale store revision, policy activation, verifier release,
  application/domain/epoch, migration mode, unmounted profile, or manifest.
- Admission: journal/effect split, response loss, duplicate retry, competing
  slot, crash partial state, or restart divergence.

The parent proves exact equality with the required child sequence or multiset.
Verification of every supplied child alone is insufficient.

Use only profile-specified metamorphic relations: canonical re-encoding,
proof-byte irrelevance with journal equality, commutative topology, ordered
permutation rejection, partition/direct composition, and exact replay.

Adapt circuit underconstraint literature to RISC Zero as a cross-representation
consistency search. Find guest computations or inputs that do not influence the
journal or later authority decision.

## Promotion evidence

- source, profile, and image identity;
- positive receipt control and one-coordinate negatives;
- independent semantic recomposition and exact child coverage;
- current authority-context checks;
- admission atomicity when claimed;
- deterministic replay and explicit stale/research/unmounted nonclaims.

A verified receipt alone never grants settlement authority. Parsed descriptors
remain untrusted before exact receipt verification.
