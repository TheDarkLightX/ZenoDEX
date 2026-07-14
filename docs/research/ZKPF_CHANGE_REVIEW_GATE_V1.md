# ZKPF Change Review Gate V1

Date: 2026-07-14

Status: implemented review-intent and change-classification gate; human approval authentication remains external

## Purpose

ZKPF changes are not equally risky. A documentation correction, a verifier
boundary change, an AIR or semantic relation change, a proving optimization,
and a privileged runtime change should not receive the same agent assignment or
review process.

`tools/check_zkpf_change_review.py` classifies the exact Git change set under the
canonical policy in
`config/proof_profiles/zkpf_change_classification_v1.json`. Protected changes
must carry one content-bound packet at:

```text
reviews/zkpf/<change-set-sha256>.json
```

The packet records the invariants, paper or normative anchors, test commands,
negative controls, benchmark evidence, reviewer roles, confidence, and known
paper-to-code divergences that a human reviewer must evaluate.

## Design source

The workflow adopts several practices found in mature recursive proof systems:

- proof and verifier code are assigned explicit soundness ownership;
- mathematical changes require a paper or normative specification anchor;
- proof-system, authority, performance, release, and operations changes are
  separate classes;
- performance changes require reproducible before-and-after evidence rather than
  intuition;
- the verifier and authority boundary receive stricter review than prover
  scaffolding;
- one change may accumulate several review classes and must satisfy the union of
  their requirements.

The packet is not a substitute for human review. It is a fail-closed checklist
and evidence index that makes omissions machine-visible.

## Exact change-set binding

For Git mode, the checker obtains:

```text
git diff --name-status --find-renames=100% -z <base>...<head>
git diff --binary --full-index --no-ext-diff <base>...<head>
```

Review packets under `reviews/zkpf/**` are excluded from both operations. This
prevents the packet from changing the digest that names itself.

The change-set identity is SHA-256 of the complete binary-capable full-index
diff. A rename contributes one deleted path and one added path so moving a
protected implementation does not evade classification.

Explicit changed-path mode is available for local development. It hashes the
exact bytes of each bounded, single-link, non-symlinked regular file and applies
the same review-packet exclusion.

## Review classes

| Class | Typical scope | Required review |
|---|---|---|
| `ordinary` | Tests, isolated tooling, documentation | Normal code review |
| `soundness` | Protocol relations, guest semantics, AIR-like constraints | Crypto specialist and math reviewer |
| `authority` | Verifier, admission, capability, ledger boundary | Security reviewer, often math reviewer |
| `release` | Source closure, evidence, workflow, promotion policy | Release and security reviewers |
| `performance` | Prover, benchmark, recursion scheduling | Performance and math reviewers |
| `operations` | Firecracker, cgroups, namespaces, privileged runners | Operations and security reviewers |

Classification rules are conservative and additive. A file may match more than
one rule. The packet must contain every required reviewer role and meet the
highest confidence floor.

## Review packet

A ready packet binds:

```text
classification-policy digest
exact change-set digest and path count
affected classes and rules
required reviewer roles
confidence in mathematical correctness
invariant identifiers
paper or normative references
exact test commands
named negative controls
benchmark artifacts where required
paper-to-code divergence records
GitHub required-review approval channel
authority flags fixed false
```

`review_state=ready_for_human_review` means the packet is complete enough to
review. It does not mean a human approved the change. Actual reviewer identity,
approval, CODEOWNERS, and branch protection remain GitHub governance controls.

## Agent routing

The intended delegation process is:

```text
exact change set
  -> machine classification
  -> ordinary implementer, crypto specialist, performance specialist,
     release reviewer, or privileged operator
  -> required packet and negative controls
  -> independent human review
  -> required CI
```

Lower-capability agents may work autonomously only on paths that classify as
ordinary and do not alter a protected dependency indirectly. The reproof
planner remains responsible for determining downstream rebuild and evidence
invalidation after a change is accepted.

## Escalation

A reviewer should stop promotion when any of the following holds:

1. a soundness change has no paper or normative anchor;
2. code intentionally diverges from its anchor without a divergence record;
3. the changed path has no negative test for its principal failure mode;
4. confidence in mathematical correctness is below the configured floor;
5. a performance result compares different program, proof, machine, or profile
   identities;
6. an authority boundary relies on unbound metadata or caller verdict fields;
7. a release change refreshes evidence without invalidating the old claim;
8. a privileged runtime claim lacks live execution and teardown evidence.

## Configuration maintenance

New soundness- or authority-bearing modules must be added to the classification
policy in the same PR that introduces them. The gate classifies its own source,
workflow, and policy as authority changes, so weakening the gate requires its
own review packet.

Glob changes need explicit regression tests. Recursive patterns with wildcard
prefixes, for example `zk/**/verifier/**`, must be tested because a literal
prefix optimization must never silently narrow them.

## Explicit nonclaims

The gate does not establish:

- correctness of the classification policy;
- reviewer identity or actual approval;
- correctness of a paper citation or invariant argument;
- proof validity, release provenance, settlement authority, or production
  readiness;
- absence of undeclared indirect dependencies;
- that a stated confidence value is honest.

Every accepted report and review packet keeps proof, release, settlement, and
production authority false.
