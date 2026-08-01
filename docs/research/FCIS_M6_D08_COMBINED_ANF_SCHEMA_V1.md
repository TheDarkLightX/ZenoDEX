# FCIS M6 D08 Combined ANF Schema V1

TASK_ID: D08

## Purpose

D08 is the composition boundary for the unmounted FCIS M6 research model. It
recomputes source-bound lineage and C3 closure, checks anchored Tree-Chord-Gate
evidence and structural proof context, verifies the durable publication atom
and its PRE/POST history transition, then evaluates the ANF-bound decision and
bundle.

The verifier returns one controlled result carrying one canonical ANF root or a
closed typed rejection. It grants no runtime authority and performs no external
I/O.

## Stage order

The stages are checked in this order:

1. Source extraction and source-bound lineage are recomputed from the supplied
   state source, settlement, intents, context, and transition budget.
2. The source-derived decision, commit bundle, evaluation evidence, occurrence
   segment, and C3 closure must equal the instance's base artifacts.
3. Every ANF field that claims source, evaluation, receipt, bundle, outbox, or
   C3 provenance is compared with the freshly recomputed base artifacts.
4. The supplied TCG certificate is checked against its anchored topology root,
   instance root, source node, source artifact, source lineage, sink artifacts,
   gate tuple, and D05 inventory root.
5. Required proof context is checked structurally against the ANF command,
   execution, state, authority epoch, verifier profile, proof root, and derived
   context root.
6. The pre snapshot must reopen to an authoritative history whose current state
   is the ANF pre-state. The expected DRA publication atom is derived from the
   base bundle and pre-history.
7. The post snapshot must reopen to exactly the PRE history plus that atom. The
   ANF post-history root and the complete canonical POST snapshot must agree.
8. The ANF-bound decision and bundle are freshly evaluated and rebuilt. A caller
   supplied later-stage root, decision, or bundle is rejected.

## Root and cycle rule

D08 uses pre-ANF base artifacts for the TCG sink and the DRA commit atom. The
final ANF-bound decision and bundle are evaluated only after those earlier
stages. This is a deliberate acyclic construction: it prevents TCG and DRA
roots from depending on a later ANF root while preserving explicit binding from
the final ANF root to the checked earlier roots.

The base decision root is:

H(d08/decision, acceptance_receipt_root, commit_plan_root, base_bundle_root)

The DRA commit identity is:

H(d08/commit, base_bundle_root, pre_history_root)

All roots are domain-separated canonical lowercase digests. Root fields are
derived or recomputed; callers do not select a replacement root.

## Controlled result

D08CombinedANFAcceptV1 contains only the verifier-minted ANF root.
D08CombinedANFRejectV1 contains:

- a closed D08CombinedANFCodeV1 value;
- a canonical tuple identifying the failed stage or field.

Direct construction of either result requires a verifier-controlled token.

## Rejection boundary

The verifier rejects wrong exact types, source extraction failures, source/base
lineage mismatches, C3 root mismatches, ANF base binding mismatches, TCG
expectation or certificate failures, proof-context mismatches, malformed or
crossed publication atoms, noncanonical or unreopenable histories, post-history
mismatches, ANF decision failures, later-root substitutions, and bundle failures.

Malformed inputs at the source, TCG, outbox, or history boundaries are converted
to typed rejection rather than escaping as an acceptance or an uncaught
authority-bearing exception.

## Assurance boundary

D08 is tested unmounted evidence for a finite composition language. The proof
context field is a structural binding; it does not verify a cryptographic proof.
The TCG inventory and certificate are supplied research fixtures. The DRA
snapshot model does not refine a production datastore or crash protocol. No
caller, API, worker, destination, deployment, migration, authority switch, or
value-moving path is mounted by this task.

