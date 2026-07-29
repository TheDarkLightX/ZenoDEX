# Independent adversarial review: B1B Revision 3.4 and B1B-1

Work read-only. Do not amend, implement, commit, push, open another pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: e28f5806a05ea621595d86ccc55190acbf324c4c
refuted Revision 3.3: b86763850c1bc309a1cda1b67a6b3205ed22f758
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Return `NO_GO` if a required file is missing, modified, or uninspectable.

## Review question

Does Revision 3.4 ensure that no configuration body becomes migration, state, update, or publication authority until it has passed the existing B1A semantic validator, been defensively re-owned and revalidated, and matched an independently sourced expected root? Does B1B-1 implement only exact untrusted carriers with byte-identical Python/Rust canonical encodings and no authority-bearing output?

## Accepted Revision 3.3 counterexamples

### Root-consistent but semantically invalid content

Revision 3.3 could admit a structurally exact body, recompute its root, match that root to an authenticated update command, and install it without requiring:

```text
algorithm_version = SUPPORT_RESPECTING_GREEDY_DEFICIT_V1
accepted_language_version = PROVISIONAL_FEES_NO_SAME_BATCH_FUNDING_V2
embedded policy_root = hash(policy)
embedded configuration_root = hash(body)
```

A wrong algorithm, wrong language, wrong policy root, or wrong embedded configuration root could therefore become active and make both fee use and ordinary rotation unavailable.

### Candidate/receipt cycle

Revision 3.3 placed a receipt inside `V2TransitionCandidate` while also deriving the receipt from the candidate. The intended graph must instead be:

```text
transition cause
  -> pre-receipt evaluation candidate
  -> candidate root
  -> receipt
  -> decision
  -> bundle
```

## Mandatory falsification pass

### A. Admit versus validate

Trace untrusted configuration bytes through decoding, structural admission, B1A validation, fresh ownership, defensive revalidation, root recomputation, and independent expected-root equality.

Attempt to replace semantic validation with:

```text
successful admission
a type cast
a Boolean validated flag
a copied private token
root equality alone
```

Any such path is blocking.

### B. Wrong algorithm and language

Construct exact claims with valid outer roots but wrong algorithm or accepted-language values. Confirm B1A rejects before any command, state, manifest, candidate, receipt, or successor relation can consume the body.

### C. Nested root substitution

Attempt both:

```text
wrong policy_root + recomputed outer configuration root
wrong embedded claim.configuration_root + command-bound body root
```

Confirm policy-root equality and embedded configuration-root equality precede independent authority-root comparison.

### D. Hostile post-validation mutation

Mutate nested policy, body, and claim fields after the first validation. Confirm field-by-field fresh ownership plus a second semantic validation and point-of-use revalidation reject the mutation.

### E. Active, proposed, and initial content

Confirm the same admit-then-validate relation is mandatory for:

```text
active content read from exact V2 state
proposed content selected by authenticated update command
initial content selected by point-of-use verified migration manifest
```

A semantically invalid initial or active configuration must not be accepted merely because its root matches the manifest or state header.

### F. Rejection precedence

Check that byte, canonical, structural, B1A semantic, independent-root, state-binding, overflow, update-law, candidate-equality, and publication phases are ordered and fail closed. An earlier rejection must leave no successor, patch, effect, replay update, receipt, decision, bundle, proof, outbox, or publication authority.

### G. Exhaustive bounded model

Run the 1,024-case model. Exactly one guard assignment must accept. The retained admit-then-root negative control must accept semantically invalid cases, proving the model can distinguish the refuted construction.

Delete each semantic guard independently and ensure a named test fails.

### H. Dependency DAG

Build the exact cause/candidate/receipt/decision/bundle graph. Confirm:

```text
TransitionCauseV2 contains no downstream hash
V2EvaluationCandidate contains no receipt or decision
receipt binds the already-computed candidate root
decision contains candidate and receipt
bundle contains the decision
```

Adding `receipt -> evaluation_candidate` must create a detected cycle.

### I. Carrier exactness

For all three B1B-1 carriers, test:

```text
exact types
Boolean/integer alias rejection
full U256 bounds
nonempty bounded Unicode scalar identifiers
lowercase Digest32 uniqueness
unknown, missing, duplicate, and trailing-field rejection
full-consumption canonical JSON
noncanonical whitespace and key-order rejection
domain-separated roots
```

An admitted header, anchor claim, or manifest remains untrusted data.

### J. Python/Rust parity

Consume the same shared fixture in both languages. Confirm exact UTF-8 bytes, arbitrary-precision U256 decimal form, Unicode behavior, schema IDs, and audit roots. Check the source-current fixture builder and Rust format/test gates.

### K. Scope isolation

B1B-1 must not implement or export:

```text
update command authority
pinned verifier
verified migration authority
migration candidate
committed V2 state
state-bound configuration
transition cause implementation
successor-producing transition
receipt or decision authority
bundle
proof input
publication
runtime mount
```

Reject bare-header advance/update functions, generic header patch atoms, public anchor-to-pin conversion, forbidden runtime imports, and premature authority types.

### L. Smaller construction

Try to remove fresh ownership, second validation, embedded-root equality, independent expected-root equality, or phase separation while preserving the same guarantees. Report any genuinely smaller construction. Do not count moving a check into a shell or bundle as a reduction.

## Automatic no-go conditions

Return `NO_GO` if:

- structural admission can substitute for B1A semantic validation;
- command/state/manifest root equality can authorize a B1A-invalid body;
- active, proposed, or initial configuration content follows different semantic validation rules;
- a validated value can be mutated and used without fresh ownership/revalidation;
- a candidate contains its receipt or a cause contains a downstream hash;
- a decoded carrier gains verifier, state, transition, publication, or mount authority;
- Python and Rust disagree on canonical bytes or roots;
- a bare header can be advanced or patched as authority;
- the B1B-1 checkpoint widens an existing mount or suppresses an existing checker.

## Required report

Report:

1. exact target, packet digest, ancestry, and files inspected;
2. commands run and anything unavailable;
3. one verdict;
4. findings ordered by severity with minimal witnesses;
5. an A-through-L attack disposition table;
6. whether B1A semantic validation precedes all authority-root comparisons;
7. whether active/proposed/initial content share one relation;
8. whether the dependency graph is acyclic;
9. whether the 1,024-case model has exactly one accept;
10. Python/Rust parity results;
11. exact permitted and forbidden B1B-1 outputs;
12. residual non-claims and the smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_4_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```
