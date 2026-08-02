# FCIS M6 formal-to-runtime assurance architecture v1

## Decision

The intended guarantee is achievable only as a chain of distinct claims:

```text
small formal state machines
+ adversarial specification mutation
+ abstract composition theorem
+ canonical model/runtime projection
+ executable ATDD/BDD refinement
+ concrete persistence/concurrency refinement
+ deployment-complete no-bypass evidence
= bounded mounted assurance for one exact promotion subject
```

ESSO supplies the small finite and inductive state-machine obligations. ATDD/BDD supplies executable acceptance criteria for the implementation. ATDD/BDD is necessary but is not, by itself, a proof that the runtime implements the formal model: the correspondence and mounted-completeness links remain separate proof or validation obligations.

## Exact formal decomposition

The global property is deliberately split into eight small models. None has more than eleven state variables, and all parameter domains are finite.

| Model | Principal claim | External premise left visible |
| --- | --- | --- |
| `fcis_m6_value_flow_kernel_v1` | Transfers, escrow moves, fees, delivery, mint, and burn preserve exact asset quantity | Every mounted command is correctly classified and projected to one action |
| `fcis_m6_managed_asset_issuance_v1` | Managed debt equals circulating supply plus an explicit outstanding protocol claim; generic mint/burn are impossible | The production zUSD asset ID and generic-token exclusion policy are authentic and complete |
| `fcis_m6_atomic_publication_v1` | State, history, nullifier, receipt, economic certificate, outbox, and authority epoch publish as one logical atom | Concrete host/database transaction refines the abstract atomic action |
| `fcis_m6_reopen_reauthorization_v1` | Canonical reopen does not restore write authority; authorization binds the exact reopened head and current epoch | Signature/quorum verifier and host restart boundary are sound |
| `fcis_m6_outbox_delivery_v1` | External delivery has stable semantic identity, at-most-once semantic effect, and provenance-bound acknowledgment | Each destination adapter really implements its declared idempotency contract |
| `fcis_m6_migration_writer_v1` | Migration follows the seven phases and never has two authoritative writers | The complete writer inventory and deployment quiescence barrier are correct |
| `fcis_m6_no_bypass_v1` | Every value change in the attested mounted inventory traverses the unique commit port | Inventory completeness is externally attested and deployment-bound |
| `fcis_m6_promotion_subject_v1` | PROVED, IMPLEMENTED, MOUNTED, and TESTED evidence composes only at one exact lineage | Subject construction includes every authority-bearing source, build, schema, and deployment identity |

The suite is intentionally not a monolithic model of ZenoDEX. A monolith would either be intractable or hide important assumptions in coarse Boolean variables.

## Formal top-level theorem

Let `P` be one exact `M6PromotionSubjectV1`. Let `Project` be the canonical projection from the mounted runtime state, context, command, result, durable layout, and effect receipt into the formal domains.

The target theorem is:

```text
MountedAccept(P, bytes, durable_pre) = mounted_receipt
-> exists formal_pre formal_command formal_post delta atom,
     Project.pre(P, durable_pre) = formal_pre
  /\ Project.command(P, bytes) = formal_command
  /\ FormalGlobalInvariant(formal_pre)
  /\ FormalStep(formal_pre, formal_command) = Accept(formal_post, delta)
  /\ FormalGlobalInvariant(formal_post)
  /\ Project.post(P, mounted_receipt) = formal_post
  /\ AtomicPublication(atom, formal_pre, formal_post, delta)
  /\ every external effect descends from atom.outbox
```

The companion no-bypass theorem is:

```text
for every entrypoint in CompleteMountedInventory(P),
  ValueChange(entrypoint, input)
  -> exists exactly one verified candidate consumed by UniqueCommitPort(P)
```

The companion rejection theorem is:

```text
FormalStep(pre, command) = Reject(reason)
-> authoritative_post = pre
/\ committed_effects = empty
/\ outbox = empty
```

ESSO verifies the finite state-machine premises. A small Lean or Tau composition theorem should combine the eight premise families without hiding inventory completeness, cryptographic soundness, or concrete durability as axioms.

## Formal-to-runtime refinement relation

For each runtime command family, define total canonical functions:

```text
project_state   : RuntimeState -> FormalState | Reject
project_context : RuntimeContext -> FormalContext | Reject
project_command : RuntimeCommand -> FormalAction | Reject
project_result  : RuntimeResult -> FormalResult | Reject
```

Required laws:

1. **Canonical projection:** accepted runtime values have one byte representation and one formal projection.
2. **Forward simulation:** every runtime accept projects to the same formal successor as the mapped formal action.
3. **Rejection purity:** every runtime reject leaves the authoritative state and effect set unchanged.
4. **No extra behavior:** a runtime accept must map to an enabled formal action; an unmapped accept is a hard failure.
5. **No missing protected behavior:** every mounted value-moving command appears in the command-to-action inventory.
6. **Same-lineage evidence:** model, adapter, executable, database schema, deployment, and test reports bind the same promotion subject root.

Where the runtime domain is finite and small, use exhaustive parity. Where it is large, combine theorem-backed arithmetic, boundary vectors, property-based differential testing, mutation testing, and an explicit coverage manifest. Test success does not replace a refinement proof when a proof is feasible.

## ATDD/BDD role

ATDD/BDD is the executable specification layer. Scenarios must be generated from or mechanically checked against the formal action and invariant registries.

Each formal action needs scenarios for:

- a valid enabling state and exact accepted successor;
- every guard conjunct independently falsified;
- rejection precedence where multiple guards fail;
- minimum, maximum, zero, and overflow-adjacent values;
- crossed command/context/state/receipt identities;
- concurrent or crash interleavings when the action touches authority or persistence;
- the corresponding implementation mutant.

Each formal invariant needs at least one retained mutant that violates it and is killed by the formal checker and the mounted runtime tests. The current bounded campaign has one or more mutants for every invariant in the eight models.

BDD scenarios become promotion evidence only when their step definitions call the actual mounted entrypoint and inspect the complete authoritative post-state, history atom, receipt, nullifier, economic certificate, outbox, and authority epoch. Calling a pure helper or research adapter is not mounted evidence.

## Three runtime assurance grades

### Grade F — formal model

- ESSO `validate` and `verify-multi` pass with pinned Z3 and cvc5.
- Both solvers agree; no `UNKNOWN`, timeout, or unsupported result.
- Independent bounded replay passes.
- Every invariant kills at least one implementation/spec mutant.
- All intended actions are reachable; explicitly forbidden actions are unreachable.

### Grade R — implementation refinement

- Canonical projection functions are implemented and independently reviewed.
- ATDD/BDD action parity passes against Python, Rust, Tau, and/or the selected authority implementation.
- Rejection and complete-successor equality are checked, not merely selected roots.
- Static checks prevent direct authoritative constructors and forbidden effects in the functional core.

### Grade M — mounted refinement

- The production build and deployment select the exact implementation.
- Every deployed value-moving entrypoint is in the anchored inventory.
- The unique commit capability is the only credentialed writer.
- Crash, retry, concurrency, reopen, outbox, and migration tests exercise the actual host and datastore.
- Old and direct paths reject after the authority switch.

The global guarantee requires F + R + M at one promotion subject. A feature file passing at Grade R cannot be relabeled MOUNTED.

## Adversarial specification process

The independent checker performs full finite reachable-state exploration and then applies named mutations such as:

- missing debit or credit;
- generic zUSD mint/burn enabled;
- partial publication row omitted;
- publish without candidate verification;
- restart or epoch switch retaining authority;
- delivery before commit or foreign acknowledgment;
- duplicate semantic effect on redelivery;
- authority switch without quiescence;
- dual writers after switch;
- value change without the unique commit port;
- promotion using crossed evidence subjects.

A specification revision fails if:

- a base model violates an invariant;
- an intended action is unreachable;
- a forbidden action is reachable;
- any named mutant survives;
- any invariant lacks a retained killing mutant.

The checked-in bounded result is reproducible, but it is not an ESSO solver receipt. CI must run ESSO separately.

## Required next implementation order

1. Pin and run ESSO/Z3/cvc5 over all eight models.
2. Add the abstract Lean/Tau composition theorem with visible premises.
3. Freeze `ManagedAssetPolicyV1`, including zUSD exclusion from generic mint, burn, and faucet paths.
4. Freeze the full mounted command/entrypoint inventory, including the Tau application host.
5. Implement canonical runtime-to-formal projections.
6. Make the feature scenarios executable against the selected authority runtime.
7. Mount one atomic publication capability and run concrete crash/concurrency refinement.
8. Bind every receipt to one promotion subject and permit promotion only after the four exact-lineage gates.

## Nonclaims

- These models do not prove cryptographic algorithms, solver soundness, compiler correctness, storage-engine durability, network delivery, or completeness of a caller-supplied inventory.
- The independent replay checker is not ESSO and does not replace the dual-solver gate.
- Bounded integer domains validate the structure of the invariants and transitions; production-width arithmetic still requires Lean/SMT/Kani or equivalent width-specific refinement.
- ATDD/BDD does not create a proof by naming a formal action. Its adapters and mounted reachability must themselves be validated.
