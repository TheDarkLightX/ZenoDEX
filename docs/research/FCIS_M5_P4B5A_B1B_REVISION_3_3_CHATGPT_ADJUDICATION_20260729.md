# FCIS M5-P4B5A B1B Revision 3.3 adjudication

**Outcome:** `REVISE_BEFORE_B1B1`

**Reviewed target:** `b86763850c1bc309a1cda1b67a6b3205ed22f758`

**Review packet:** `0511d71cca6b45df25e3c230e69bcce11d25d5a4`

**Authority mount:** prohibited

## Accepted findings

Revision 3.3 correctly:

- binds the proposed configuration root inside authenticated update-command bytes;
- derives the active root only from the exact pre-state;
- consumes the deployment pin in both migration and V2 publication branches;
- rejects mixed state/bundle families;
- preserves exact-pre-state header provenance;
- removes `decision_hash` from `TransitionCauseV2`.

Two gaps remained.

### 1. Structural admission was treated as configuration validation

The update pipeline constructed an admitted proposed claim, recomputed the body
root, compared it with the command-bound root, and then installed that root.
It did not require the existing B1A semantic validator to accept the claim.

A command could therefore intentionally or accidentally authenticate the root
of a structurally exact body carrying:

```text
wrong algorithm version
wrong accepted-language version
wrong embedded policy root
wrong embedded configuration root
```

Every Revision 3.3 update equation could hold while B1A would reject the same
claim. Once installed, the invalid active root could block both fee-bearing
transitions and normal configuration rotation.

### 2. Candidate and receipt phases were circular

Revision 3.3 placed `receipt` inside `V2TransitionCandidate`, while its declared
dependency graph derived the receipt from the complete candidate. The resulting
object graph had the shape:

```text
receipt -> candidate -> receipt
```

The repair is to separate:

```text
V2EvaluationCandidate
  -> receipt
  -> V2Decision
  -> V2CommitBundle
```

## Required correction

Revision 3.4 must make the content path:

```text
canonical bytes
  -> closed admission
  -> B1A semantic validation
  -> defensive revalidation
  -> root recomputation
  -> embedded-root equality
  -> authenticated-command-root equality
  -> update law
```

and must freeze an acyclic candidate/receipt/decision/bundle dependency graph.

No mounted authority is authorized by this adjudication.
