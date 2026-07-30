# FCIS M5-P4B5A B1B Revision 3.3 ChatGPT review adjudication

**Disposition:** `ACCEPT_BLOCKING_FINDINGS`

**Review target:** `b86763850c1bc309a1cda1b67a6b3205ed22f758`

**Review packet:** `0511d71cca6b45df25e3c230e69bcce11d25d5a4`

**Controlling verdict:**

```text
REVISE_BEFORE_B1B1
```

B1B-1 remains blocked.

## 1. Revision 3.3 corrections retained

The review confirms that Revision 3.3 closes the three findings it was written
to address:

1. The freshly authenticated configuration-update command commits the proposed
   configuration root.
2. Migration and non-migration publication both consume the independently
   pinned deployment verifier through a closed state/bundle-family dispatch.
3. `TransitionCauseV2` no longer contains `decision_hash`.

The exact-pre-state header provenance from Revision 3.2 also remains intact.
Revision 3.4 retains all four corrections.

## 2. Proposed-content semantic-validation gap

Revision 3.3 admits and owns proposed configuration content, recomputes its
canonical root, and compares that root with the freshly authenticated command.
It then reads update-law fields directly from:

```text
proposed_claim.configuration_body
```

That pipeline does not require the admitted claim to pass the already-frozen
B1A semantic validator.

The distinction is normative and implemented:

```text
closed admission
  -> exact structure, scalar domains, bounds, and canonical form

B1A validation
  -> pinned SRGD algorithm
  -> pinned accepted language
  -> policy-root equality
  -> configuration-root equality
  -> controlled ValidatedFeeDistributionConfigurationClaimV2
```

`FeeDistributionConfigurationBodyV2` admits nonempty algorithm and
accepted-language strings. The separate
`validate_fee_distribution_configuration_claim_v2` function rejects a wrong
algorithm, wrong language, wrong policy root, or wrong configuration root.

### 2.1 Minimized witness

An authenticated update command may commit the canonical root of a structurally
valid body containing:

```text
algorithm_version = OTHER_ALGORITHM
```

The body can satisfy the deployment, domain, version, activation, and
command-root equations in Revision 3.3. B1A rejects the same claim with:

```text
ALGORITHM_VERSION_MISMATCH
```

No malformed field or hash collision is required.

### 2.2 Authority impact

Installing such a root can make every later fee-bearing transition reject when
it tries to bind the active configuration. A normal configuration update also
requires the active configuration, so the deployment may be unable to rotate
back through the V2 update language.

This is a blocking architecture defect. There is no mounted exposure because
Revision 3.3 is documentation-only.

### 2.3 Required correction

Revision 3.4 must require:

```text
untrusted canonical content
  -> full-consumption decode
  -> closed B1A admission
  -> B1A semantic validation
  -> exact ValidatedFeeDistributionConfigurationClaimV2
  -> point-of-use revalidation
  -> authoritative expected-root comparison
  -> update or migration laws
```

The update laws must read only from the controlled validated claim. The active,
proposed, and initial-migration configuration paths must use the same semantic
validation boundary.

The authoritative equality is:

```text
validated claim configuration root
  = recomputed canonical body root
  = freshly authenticated command root
```

For migration, the final term is the pinned manifest's expected initial
configuration root.

## 3. Candidate/receipt dependency contradiction

Revision 3.3 defines:

```text
V2TransitionCandidate(
    post_state,
    canonical_patch,
    effects,
    receipt,
    replay_update,
    transition_cause,
)
```

Its declared dependency graph separately says:

```text
transition outputs
  -> complete candidate
  -> receipt and bundle
```

Taken together, the graph contains:

```text
receipt -> candidate -> receipt
```

Removing `decision_hash` from `TransitionCauseV2` closed the cause-local cycle.
It did not make the complete object graph acyclic.

### 3.1 Existing source pattern

The current FCIS V1 source separates these phases:

```text
FCISStepCandidateV1
  -> controlled AcceptV1 containing the receipt
  -> CommitBundleV1 containing one committable decision
```

`FCISStepCandidateV1` contains the successor and canonical patches. It does not
contain a receipt. `AcceptV1` introduces the receipt, and `CommitBundleV1`
retains one nested decision rather than copying its fields.

### 3.2 Required correction

Revision 3.4 must use:

```text
V2EvaluationCandidate(
    post_state,
    canonical_patch,
    effects,
    replay_update,
    transition_cause,
)

V2Decision(
    evaluation_candidate,
    receipt,
)

V2CommitBundle(
    decision,
    outbox_plan,
)
```

The receipt must derive from a projection that cannot include the receipt,
decision, bundle, or any hash downstream of itself.

## 4. Rejection order retained as an obligation

Revision 3.4 must freeze this phase order:

```text
1. byte decoding and full consumption
2. closed structural admission
3. B1A semantic validation
   a. algorithm version
   b. accepted-language version
   c. policy-root equality
   d. configuration-root equality
4. authoritative expected-root comparison
5. deployment/domain/version/activation laws
6. evaluation-candidate derivation
7. receipt and decision derivation
8. bundle equality and publication
```

Any earlier rejection produces no successor, patch, effect, receipt, replay
update, outbox, or publication authority.

## 5. Permanent evidence retained

Revision 3.4 must add these named mutants:

```text
command authenticates a body using OTHER_ALGORITHM
command authenticates a body using another accepted language
body embeds a wrong policy root and recomputes its outer root
claim embeds H_MALLORY while its body recomputes to H_GOOD
update reads proposed body before B1A validation
admitted claim is treated as a validated claim
validator call is deleted while command-root equality remains
validated proposed claim is mutated before update-law evaluation
migration initial content is admitted without B1A validation

evaluation candidate contains a receipt
receipt hash includes a receipt-bearing decision
bundle copies candidate or receipt fields outside its nested decision
```

Every semantic mutant must retain valid field types and recompute unrelated
outer hashes. The B1A validation or dependency-DAG check itself must kill it.

## 6. Scope

This adjudication changes documentation only. It authorizes no B1B-1
implementation, command, pinned verifier, migration, committed V2 state,
configuration update, state binding, transition cause, receipt, decision,
bundle, proof input, publication, or mount.

The B1B-1 carrier field sets remain unchanged. The next action is focused
independent review of Revision 3.4.
