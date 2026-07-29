# B1B-2 source-bound migration design prompt

```text
status: compiled candidate
prompt kind: review-only design synthesis
visibility: separate B1B-2 design worktree
compiled from: FCIS M5-P4B5A ATDD execution contract v1
execution authorized: false
local commit authority: documentation-only when the coordinator assigns it
push, PR mutation, publication, and external messaging authority: false
terminal condition: exact design document and review manifest ready, then stop
```

**DESIGN ONLY.**

The phase matrix fixes:

```text
execution_authorized = false
```

Do not write implementation, verifier capability, migration candidate,
committed state, publication code, or runtime mount.

Work in a separate clean documentation-only worktree after the B1B-1 exact-head
review finishes. Do not add the design to the B1B-1 implementation head.

The planned exact artifacts are:

```text
docs/research/FCIS_M5_P4B5A_B1B2_PINNED_MIGRATION_REFERENCE_DESIGN_20260729.md
docs/research/prompts/fcis_m5_p4b5a_b1b2_pinned_migration_review_v1/
  README.md
  REVIEW_PROMPT.md
  SOURCE_MANIFEST.sha256
```

## Exact two-commit packet construction

Let `B` be the exact independently approved B1B-1 implementation packet
commit. Create:

```text
documentation-only design target D descended from B
  -> design document and bounded design evidence

documentation-only review packet Q, exactly one child of D
  -> README, review prompt, and source manifest
```

The deterministic packet builder must inventory every committed path changed
from B through D. It must also include the immutable Revision 3.1 and Revision
3.4 authority sources, the committed ATDD contract and matrix, and the exact
B1B-1 implementation approval sources. It sorts paths by raw
repository-relative UTF-8 text, hashes committed Git bytes, hashes packet
siblings from Q, rejects missing or extra entries, verifies ancestry and the
one-child relation, and excludes the manifest itself from the manifest.

The exact planned builder is:

```bash
python3 -m tools.build_fcis_b1b2_pinned_migration_review_packet --check
```

The builder and packet are design evidence. They cannot change the matrix phase
flag or authorize B1B-2 implementation.

The design agent cannot change `execution_authorized` in the ATDD matrix.

## Goal

Produce the smallest review-only B1B-2 design for:

```text
mechanically pinned deployment-verifier interface
source-bound deterministic V1-to-V2 migration reference relation
explicit retained-namespace projection
permanent falsification and mutation inventory
```

## Required independent sources

The core relation must keep these sources present until the use that needs
them:

```text
pinned deployment verifier
untrusted migration manifest carrier
store-current exact V1 state
B1A-validated initial configuration claim
```

The store-current exact V1 state cannot be replaced by bundle-carried,
historical, or shell-selected state.

## Required laws

Freeze exact equations for:

```text
manifest root = pinned expected manifest root
manifest deployment = pinned deployment
current V1 root = manifest expected V1 root
legacy fee dust = 0
initial sequence/version/activation = 0/1/0
source/target snapshot versions = 4/5
balances, pools, LP balances, nonces, vault, oracle, and perps are identities
V1 fee accumulator is unrepresentable in V2
V2 fee apportionment starts in the canonical empty state
second migration rejects
V2-to-V1 downgrade rejects
```

Do not use a durable verified-migration wrapper that can outlive the independent
pin. If a wrapper is proposed for ergonomics, every use must still receive the
pinned verifier and repeat the provenance comparison.

## Required attacks

Falsify:

```text
decoded anchor claim constructs the pin
manifest and root mutate together
deployment and manifest root mutate together
bundle-carried V1 state replaces store-current state
nonzero legacy dust migrates
one retained namespace changes
initial constants vary
second migration or downgrade becomes representable
future publication refinement fails to rerun this relation with store-current state
```

Record that publication refinement as a future obligation only. B1B-2 does not
freeze or implement datastore, publication, crash-recovery, proof, or mount
behavior.

## Output

Write a review-only document containing:

```text
authority map
exact typed signatures
complete equations and rejection precedence
trust-source continuity table
Given/When/Then scenarios
mutation inventory
formal or bounded model plan
non-claims
smallest implementation checkpoint
```

Stop after the design packet. Do not authorize or begin execution.
