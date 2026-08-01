# FCIS M6 D06 Lineage Rule Manifest Schema V1

TASK_ID: D06

## Purpose

D06 makes the C3 derived-claim closure rules an explicit, typed, validated
manifest. The manifest is held behind the existing private construction
boundary. The public source-bound lineage constructor remains the only public
constructor for concrete lineage certificates.

The manifest establishes:

one writer per derived key
complete derived-key coverage
canonical dependency tuples
acyclic dependencies
canonical topological rule order
bounded fixed-point termination
manifest-root binding

## Closed derived-key registry

The derived keys are exactly the FCISLineageClaimKeyV1 members whose canonical
values begin with derived/.

They are sorted by UTF-8 bytes in the manifest registry. The four writers are:

derive-evaluation-certificate -> derived/evaluation_certificate_root
derive-receipt-certificate    -> derived/receipt_certificate_root
derive-bundle-certificate     -> derived/bundle_certificate_root
derive-outbox-certificate     -> derived/outbox_certificate_root

No caller-provided key or rule ID is admitted into the authoritative manifest.

## Rule shape

Each rule is an object with:

rule_id: exact nonempty string
output: exact closed claim-key enum member
dependencies: exact tuple of closed claim-key enum members

Dependency tuples are unique and sorted by canonical UTF-8 key bytes. A rule may
not depend on its own output.

The manifest validates the output set against the exact derived-key registry.
It uses a deterministic Kahn-style closure check to reject cycles. Each rule is
assigned a depth equal to one plus the maximum depth of its derived
dependencies, with leaf rules at depth one. Canonical manifest order is
ascending (depth, output UTF-8 bytes). Therefore every derived dependency
appears before its consumer.

## Fixed point and rule-order relation

The authoritative closure uses the validated canonical manifest. A private
test seam accepts only permutations of the exact validated rule set. It applies
at most rule_count + 1 rounds and returns only after an unchanged round.
Acyclicity bounds the dependency path by rule_count, so every admissible
permutation reaches the same fixed point on the same seed.

The D06 vector and checker exercise all 4! = 24 rule permutations and compare
the complete canonical claim set, including its root.

## Manifest root

The root is the domain-separated hash of:

manifest_version
ordered_derived_keys
rule_count
max_rounds = rule_count + 1
ordered_rules = [rule_id, output, ordered_dependencies]

All list lengths use U32 frames. Claim-key values and rule IDs use length
frames. The domain separator is supplied by the repository canonical byte
helpers.

## Fail-closed mutations

The typed manifest rejects:

- duplicate derived writers;
- missing derived writers;
- surplus or unknown derived outputs;
- cyclic derived dependencies;
- noncanonical rule order;
- duplicate or noncanonical dependency tuples;
- wrong enum, tuple, or root types;
- a root that does not recompute from the manifest contents;
- a private closure seam containing a rule outside the validated manifest.

## Boundary

D06 is tested unmounted evidence for the C3 manifest and bounded closure model.
It does not prove the production datastore, runtime caller inventory, proof
context, deployment reachability, authority switch, recovery, outbox delivery,
or value movement.
