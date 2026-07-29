# FCIS M5-P4B5A B1B Revision 3.2 ChatGPT review adjudication

**Disposition:** `ACCEPT_BLOCKING_FINDINGS`

**Review target:** `27bfde2a5679250e949d397960d6dba09117c6bd`

**Review packet:** `1509786d6bc48bc949fbff5359ed42e73534eb2d`

**Controlling verdict:**

```text
REVISE_BEFORE_B1B1
```

B1B-1 remains blocked.

## 1. Prior counterexample closure

The review confirms that Revision 3.2 closes the Revision 3.1 loose-pre-header
counterexample.

Ordinary accept, committed failure, and configuration update now consume the
exact pre-state and extract:

```text
pre_header = exact_pre_state.authority_header
```

Publication also reloads the store-current exact state and rederives the
complete candidate. A bundle-carried state, pre-header, cause, or transition
result is an equality target and cannot supply authority.

That correction remains valid and is retained in Revision 3.3.

## 2. Proposed configuration authority gap

Revision 3.2 receives both:

```text
validated_proposed_configuration
exact_configuration_update_command
```

It validates the proposed deployment, domain, version, activation sequence, and
successor root. It does not require the authenticated command to commit the
root of the proposed configuration.

Therefore one authenticated command can be paired with either:

```text
P_good
P_mallory
```

when both values satisfy the structural update equations. The decision hash
records the selected result after the choice. It does not prove that the
authenticated command authorized that choice.

The finding is correct. The untrusted content provider would retain semantic
policy-selection authority.

Revision 3.3 must place
`proposed_fee_distribution_configuration_root` inside the canonical
authenticated command and require fresh proposed-content admission and exact
root equality.

## 3. Publication deployment-pin gap

Revision 3.2 includes `pinned_deployment_verifier` in the publication signature
without consuming it in the numbered relation.

This leaves two open branches:

1. V1-to-V2 migration publication does not explicitly rerun the source-bound
   migration derivation with the pin and store-current exact V1 state.
2. Ordinary V2 publication does not compare the store-current header deployment
   ID with the independently pinned local deployment ID.

The finding is correct. Loading exact state proves the store supplied that
state. It does not prove the state belongs to the local deployment.

Revision 3.3 must define a closed state-family and bundle-family dispatch:

```text
current V1 + migration bundle
  -> rerun pinned migration derivation

current V2 + V2 transition bundle
  -> compare current deployment ID with the pin
  -> rederive the complete non-migration transition

every mixed family
  -> reject
```

## 4. Cause-hash dependency ambiguity

Revision 3.2 places `decision_hash` inside the transition cause while the cause
is nested inside the decision lineage.

Without an exact projection this can form:

```text
decision
  -> candidate
    -> cause
      -> hash(decision)
```

The review correctly classifies this as a P2 design ambiguity. Revision 3.3
removes `decision_hash` from the cause. Complete candidate equality at
publication already binds the cause to the decision.

The retained dependency direction is:

```text
pre-state, command, context
  -> cause
  -> complete candidate
  -> decision/candidate hash
  -> receipt and bundle
```

## 5. Evidence retained

Permanent counterexamples and mutants:

```text
same authenticated update command paired with two valid proposed bodies
command commits H_GOOD while supplied content hashes to H_MALLORY
shell or bundle supplies the expected proposed root separately
publication receives a deployment pin but ignores it
local deployment B publishes over store-current V2 state A
migration publication omits the pinned verifier
migration publication uses bundle-carried V1 state
migration publication uses bundle-carried expected manifest root
V1 current state dispatches through the ordinary V2 path
cause hash depends on a decision hash that includes the cause
```

Every mutation test must recompute unrelated outer hashes. The authority-source
comparison itself must reject the specimen.

## 6. Scope

This adjudication changes documentation only. It authorizes no B1B-1
implementation, authenticated update command, pinned verifier, migration,
committed V2 state, configuration update, state binding, receipt, bundle, proof
input, publication, or mount.

The B1B-1 carrier fields remain unchanged. The next action is focused
independent review of Revision 3.3.
