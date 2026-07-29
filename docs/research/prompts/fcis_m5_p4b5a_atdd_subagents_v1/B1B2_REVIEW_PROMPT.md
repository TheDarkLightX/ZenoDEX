# B1B-2 source-bound migration design review prompt

```text
status: compiled candidate
prompt kind: independent design falsification
visibility: repository review packet
compiled from: FCIS M5-P4B5A ATDD execution contract v1
execution authorized: false
local commit authority: false
push or PR authority: false
terminal condition: one closed verdict over one exact design manifest
```

Review only the design document and paths declared in the exact design
manifest. Do not edit implementation, create a pinned capability, derive a
migration successor, or mount any path.

Required planned artifacts:

```text
docs/research/FCIS_M5_P4B5A_B1B2_PINNED_MIGRATION_REFERENCE_DESIGN_20260729.md
docs/research/prompts/fcis_m5_p4b5a_b1b2_pinned_migration_review_v1/
  SOURCE_MANIFEST.sha256
```

Before semantic review, run:

```bash
python3 -m tools.build_fcis_b1b2_pinned_migration_review_packet --check
```

Verify that the packet commit is documentation-only and exactly one child of
the design target, the design target descends from the exact independently
approved B1B-1 packet commit, and the manifest contains the complete committed
byte inventory required by the matrix. The manifest must exclude only itself.
Reject missing, extra, duplicate, uncommitted, stale, or non-descendant entries.

Falsify:

```text
decoded claim selects its own pin
manifest and root mutate together after the pin leaves the relation
bundle-carried V1 state replaces store-current exact V1 state
one retained economic namespace changes
legacy fee dust is nonzero
fixed 0/1/0 or 4-to-5 constants vary
second migration or downgrade is representable
the design claims publication, datastore, proof, or mount authority
```

Return exactly one verdict:

```text
APPROVE_B1B2_SOURCE_BOUND_MIGRATION_DESIGN_UNMOUNTED
REVISE_B1B2_SOURCE_BOUND_MIGRATION_DESIGN
NO_GO_B1B2_SOURCE_BOUND_MIGRATION_DESIGN
```

An approval records design adequacy only; implementation remains unauthorized.
Implementation requires a new committed ATDD contract revision,
the exact B1B-1 implementation approval identity, the exact B1B-2 design
approval identity, and explicit user implementation authority.

The output must identify the exact design manifest, commands run, attacks,
counterexamples, non-claims, and smallest safe next checkpoint.
