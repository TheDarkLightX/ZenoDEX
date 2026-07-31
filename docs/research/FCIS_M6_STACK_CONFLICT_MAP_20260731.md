# FCIS M6 Stack Conflict Map

TASK_ID: A01
STATUS: IMPLEMENTED
CLAIM_STATUS: RESEARCH_ONLY_EXECUTABLE_UNMOUNTED
PROMOTION: DO_NOT_PROMOTE_M6
DATE: 2026-07-31

## Scope

This map classifies the exact-head interactions among PRs #496, #497, #498,
#499, and #501 before any stack integration. The reviewed source packet is
anchored at `476ec022e755ff049c39bf9f08c6606ac87532ca`. The map covers:

- same-path content and blob identity;
- exported Lean and Python symbol namespaces;
- schema identifiers, root domains, and hash preimages;
- workflow names and assurance surfaces;
- ancestry and parallel-branch relationships.

The classifications are findings about the reviewed heads. They do not prove
that the proposed interfaces are semantically compatible at runtime.

## Classification vocabulary

| Classification | Meaning | Integration consequence |
| --- | --- | --- |
| `IDENTICAL` | The compared content or identity is byte-identical or has no differing meaning in the checked scope. | Reuse the single value; retain its source hash. |
| `COMPATIBLE_ADDITIVE` | The newer surface adds a distinct declaration, root, workflow, or field without a direct collision in the checked scope. | Compose only after the union is rebuilt and its gates pass. |
| `RENAME_REQUIRED` | Two meanings share an exported name or identifier and must be renamed before composition. | No integration until the owner chooses a canonical name. |
| `SCHEMA_MIGRATION_REQUIRED` | A cross-layer relationship requires a new explicit schema, preimage, version mapping, or migration rule. | Do not infer compatibility from similar field names. |
| `SEMANTIC_CONFLICT` | The same interface or authority surface has incompatible meanings. | Never auto-merge; escalate to a design decision. |
| `UNKNOWN_REQUIRES_REVIEW` | The available source does not establish whether the meanings compose. | Keep both surfaces isolated and add a checked adapter or proof obligation. |

No `RENAME_REQUIRED` or direct `SEMANTIC_CONFLICT` was found in the bounded
collision inventory. Several unresolved schema and authority relationships are
classified conservatively as `SCHEMA_MIGRATION_REQUIRED` or
`UNKNOWN_REQUIRES_REVIEW`.

## Exact source heads

| PR | Head commit | Tree | Parent/base relation | Stack role |
| ---: | --- | --- | --- | --- |
| #496 | `4cad0c4ff203e6926991d33f4b314c4873792810` | `716a7b633dc3036aada1cad73787514c72710197` | base `554758aa1536b01b911ba40b21afa4aec55c1b60` | AGQE/SRGD refinement sibling |
| #497 | `0a51b2dc8729af34d86d717dff214576f7ae58c8` | `f9d93c6dbaba549a447af2e8931a1740b8edfc2e` | child of `557cfaaca79318a1757124fd61625433de82b105` | R01 segmented lineage |
| #498 | `a94a1fa0586107a0a48aebbe4cd18c0d1029d481` | `0504abdf4c4b493a97baf06cfd73d4a3922d4cfb` | child of #497 head | R01/R04 source-bound lineage sibling |
| #499 | `babffa56dcbddc5886487fbb6e62740b15370000` | `eb6771943bc490d1f9664d26ec14622a8849b010` | child of #497 head | R04 Tree–Chord–Gate |
| #501 | `476ec022e755ff049c39bf9f08c6606ac87532ca` | `a1d495eae0b26a369487ceb48cad5472abec74db` | child of #499 head | R05–R11 durable retraction |

The exact implementation target recorded by A00 is
`ecf26f987c3d6393501fec66ddfc3429fb8634c7`, tree
`fdf154ac143a9f9a9e840fbbf49761190d138920`. The packet head is one
documentation/evidence child of that implementation target.

## Ancestry and branch topology

| Relation | Result | Classification | Meaning |
| --- | --- | --- | --- |
| #496 ancestor of #497 | false | `UNKNOWN_REQUIRES_REVIEW` | Sibling work from a common base must be compared explicitly. |
| #497 ancestor of #498 | true | `COMPATIBLE_ADDITIVE` | #498 builds on the segmented-lineage head. |
| #498 ancestor of #499 | false | `UNKNOWN_REQUIRES_REVIEW` | R04 lineage closure and R04 TCG work are parallel branches. |
| #499 ancestor of #501 | true | `COMPATIBLE_ADDITIVE` | The durable-retraction packet is based on TCG. |
| #497 ancestor of #499 | true | `COMPATIBLE_ADDITIVE` | Both R04 branches share the R01 base. |

The parallel #498/#499 relationship is itself an integration boundary. No
merge result is implied by the `mergeable` metadata recorded in A00.

## Direct path and blob collisions

### Shared documentation report

| Paths | Heads | Blob | Classification | Finding |
| --- | --- | --- | --- | --- |
| `docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md` | #496, #497, #498, #499, #501 | `bc401d623f3e0ac84a2a7f48ac5813304c745b80` | `IDENTICAL` | The same historical report content is inherited at every reviewed head. |

### Lean build manifest

`lean-mathlib/lakefile.lean` is the only direct implementation-path collision
whose content changes across the reviewed M6 stack. The values are:

| Head | Blob | Observed change |
| --- | --- | --- |
| #496 | `51bb017b9ab76a9c6e1306e84c60eedd4e2135d2` | Prior manifest baseline. |
| #497/#498 | `fe738dbba06649dbedbae3ba25fdc1e9c45591f2` | Adds `Proofs.FCISFeeOccurrenceSemantics`. |
| #499 | `671d9923d116d87df0e21fd62a875e3c9d38a4eb` | Adds `Proofs.FCISTreeChordGateAuthority` and formats the list. |
| #501 | `51619d79b46a3571d108a5ebfa03048de6c2be78` | Adds `Proofs.FCISDurableRetraction`. |

Classification: `COMPATIBLE_ADDITIVE`. The correct integration operation is a
manifest union followed by a complete Lean build. Last-writer replacement is
unsafe because it can silently omit a theorem root.

### Lean import registry

`lean-mathlib/Proofs.lean` has blob
`6e7e69c2d086506ee4491613e5f9c5704bf891f6` at all five reviewed heads.
Classification: `IDENTICAL`.

The theorem roots are distinct:

| Surface | Declaration root |
| --- | --- |
| #496 | `FCISFeeApportionmentAGQESRGDRefinement` |
| #497 | `FCISFeeOccurrenceSemantics` |
| #499 | `FCISTreeChordGateAuthority` |
| #501 | `FCISDurableRetraction` |

Classification: `COMPATIBLE_ADDITIVE`. No same Lean declaration root with
different content was found.

## Exported symbol audit

The reviewed modules use distinct domain-qualified public namespaces. The
major roots are:

| Head | Public surface |
| --- | --- |
| #496 | `FCISFeeApportionmentAGQESRGDRefinement` and its AGQE/SRGD theorem names |
| #497 | `FeeOccurrenceNormalizationCodeV1`, `FeeWitnessOccurrenceClaimV1`, `CanonicalFeeOccurrenceSegmentV1`, and related SLNF functions |
| #498 | `SourceBoundFeeOccurrenceV1`, source-bound lineage certificates, and `FCISLineageClaimSetV1` |
| #499 | `LineageBindingV1`, `AuthorityGateV1`, `AuthorityNodeV1`, `AuthorityEdgeV1`, `TreeChordGateCertificateV1` |
| #501 | `PublicationAtomV1`, `AuthorizedHistoryV1`, `DurableSnapshotV1`, `CommitResolutionV1`, `DestinationResponseEvidenceV1`, and related DRA types |

No duplicate exported Python symbol or Lean declaration with different
meaning was found in the checked changed modules. Repeated private helper names
such as `_reject_v1` are module-local and are not exported collisions.

Classification of the negative finding: no collision to resolve. This audit
does not establish behavior-level compatibility between the modules.

## Schema, root-domain, and preimage collisions

| ID | Surfaces | Classification | Evidence and required action |
| --- | --- | --- | --- |
| C-01 | SLNF (#497) -> source-bound extractor (#498) | `SCHEMA_MIGRATION_REQUIRED` | #498 imports the canonical SLNF segment but defines `SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1 = "zenodex/fcis/fee-occurrence/source-bound-extractor/v2"`. The v1 constant name and v2 encoded value require an explicit version mapping, field-by-field preimage specification, and migration tests. |
| C-02 | Lineage closure (#498) -> TCG authority graph (#499) | `UNKNOWN_REQUIRES_REVIEW` | #498 emits `FCISLineageClosureCertificateV1` and `FCISLineageClaimSetV1`; #499 consumes `LineageV1`, topology roots, and authority-instance roots. No checked adapter or equality theorem binds the claim set to the TCG certificate. D01/D05/D08 must define that relation. |
| C-03 | TCG (#499) -> durable retraction (#501) | `SCHEMA_MIGRATION_REQUIRED` | TCG authority-instance/topology/lineage roots and DRA authority-state/history/snapshot roots are separate domains. The ANF schema must carry and recompute the required TCG binding rather than treating `authority_instance_root` and `authority_state_root` as interchangeable. |
| C-04 | All reviewed root domains | `COMPATIBLE_ADDITIVE` | No exact literal root-domain collision was found among the SLNF, source-bound, lineage, TCG, and DRA namespaces. Distinct strings reduce accidental hash-domain reuse, while semantic binding remains open. |

The DRA roots observed in #501 include
`zenodex/fcis/dra/publication-atom/v1`,
`zenodex/fcis/dra/authorized-history/v1`,
`zenodex/fcis/dra/durable-snapshot/v1`,
`zenodex/fcis/dra/reopen-authorization/v2`, and
`zenodex/fcis/dra/verified-destination-receipt/v1`. Their distinct names do
not authorize caller construction or production mounting.

## Workflow and assurance-surface audit

| Head | Workflow path | Workflow name | Classification |
| --- | --- | --- | --- |
| #497 | `.github/workflows/fcis-m6-r01-segmented-lineage.yml` | `fcis-m6-r01-segmented-lineage` | `COMPATIBLE_ADDITIVE` |
| #498 | `.github/workflows/fcis-m6-r04-lineage-closure.yml` | `fcis-m6-r04-lineage-closure` | `COMPATIBLE_ADDITIVE` |
| #499 | `.github/workflows/fcis-m6-tree-chord-gate.yml` | `FCIS M6 Tree-Chord-Gate` | `COMPATIBLE_ADDITIVE` |
| #501 | `.github/workflows/fcis-m6-durable-retraction.yml` | `FCIS M6 Durable Retraction` | `COMPATIBLE_ADDITIVE` |

No duplicate workflow name was found. The workflows have different triggers,
job sets, and evidence outputs, so aggregate CI coverage must be reviewed when
the stack is integrated. A workflow passing on one head is not evidence that
the merged stack passes.

## Resolution policy

This A01 task performs classification only. It does not merge branches, edit
the reviewed packet, or resolve semantic relations by choosing a last writer.

The following rules govern later tasks:

1. Reuse `IDENTICAL` content only with its recorded blob identity.
2. Compose `COMPATIBLE_ADDITIVE` surfaces by explicit union and rerun the
   relevant build, checker, and replay gates.
3. Treat every `SCHEMA_MIGRATION_REQUIRED` row as an implementation and proof
   obligation with canonical bytes, version rules, and negative tests.
4. Keep every `UNKNOWN_REQUIRES_REVIEW` row isolated until a checked adapter,
   theorem, or executable relation establishes the intended semantics.
5. Never auto-merge a future `SEMANTIC_CONFLICT` or introduce an implicit
   rename to hide one.

The next dependency-closed tasks are A02 and A03. A04 may integrate only after
those collision inputs are complete. A01 adds no mounted caller, datastore
adapter, authority switch, deployment path, or value-moving path.

## Evidence and nonclaims

The machine-readable classification receipt is
`docs/research/FCIS_M6_TASK_A01_EVIDENCE_20260731.json`. The exact source
identity and workflow evidence remain in the A00 ledgers. The source manifest
records the hashes of these artifacts.

This map does not prove:

- production datastore atomicity or crash recovery;
- production verifier ownership of authority witnesses;
- completeness of the no-bypass audit;
- a valid R02 general theorem or whole-system R13 theorem;
- a mounted runtime transition or value movement;
- M6 promotion or deployment readiness.
