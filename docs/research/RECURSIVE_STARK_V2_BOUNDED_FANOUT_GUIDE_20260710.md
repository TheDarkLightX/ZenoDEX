# Recursive V2 Bounded Fanout Guide

Date: 2026-07-10

Status: source-pinned local computational-integrity evidence; release and production pending

## Purpose

The recursive-v2 lane compresses several verified ZenoDEX transition receipts
into one fixed-height epoch-root receipt. A validator verifies the root receipt
and its authenticated journal once for the complete included transition set.

The current implementation supports this shape:

```text
1..=8 Succinct transition-leaf receipts
                 |
                 v
      one closed-subtree receipt
                 |
                 v
        one epoch-root receipt
```

Current real evidence uses two leaves:

```text
spot transition + zUSD DepositMint
                 |
                 v
closed subtree: 2 immediate children, 2 flat leaves, height 1, 3 nodes
                 |
                 v
epoch root:      1 immediate child, 2 flat leaves, height 2, 4 nodes
```

The aggregate guest runs under RISC0 3.0.5 with image ID:

```text
fe131b0ec697a9bd703218f3733e44b84c8e347eb8ebfc8776be2200958fbe53
```

## New Features

### 1. Bounded multi-leaf input

The host harness accepts from one through eight v1 Succinct transition-leaf
artifacts. The upper bound comes from the recursive-v2 node ABI. Empty inputs
and larger sets reject before proving.

Supported transition-leaf surfaces are currently:

- spot transition leaf v1;
- zUSD transition leaf v1;
- perps non-positive-PnL transition leaf v1.

Each leaf receipt is cryptographically verified against its pinned image ID.
The harness also checks its proof type, profile, receipt kind, metadata, and
authenticated journal.

### 2. Canonical order

Leaves are sorted by authenticated lane ID before the flat statement or node
input is constructed. Reversing command-line input order produces the same
inner and root journals.

Duplicate lane IDs reject. This prevents the same authenticated lane state from
being counted twice under a host-selected ordering.

### 3. Common-scope enforcement

Every included leaf must agree on:

- chain ID;
- epoch ID;
- public policy hash;
- feature-suite hash;
- dependency-lock hash;
- toolchain-lock hash.

A mismatch rejects before proving. These fields define the common aggregation
scope and prevent receipts from unrelated epochs or policies from sharing one
root.

### 4. Canonical verifier and authority sets

Leaf verifier IDs and nonzero authority roots are sorted and deduplicated before
their set roots are computed. Distinct leaves may share one verifier ID. The
authenticated child set still preserves every leaf disclosure and receipt
claim.

### 5. Root-as-child verification

The epoch-root guest verifies the closed-subtree receipt as an in-guest
assumption. Its child descriptor binds:

- aggregate image ID;
- node profile;
- verifier ID;
- verification-claim hash;
- journal hash;
- statement hash.

Running the root without the child assumption produces the typed
`missing_child_assumption_rejected` evidence result.

### 6. Exact flat projection

Both recursive levels authenticate the same flat v1 projection. The host and
guest bind the complete leaf set into:

- pre-state and post-state vector roots;
- transaction root;
- evidence and receipt roots;
- accepted and rejected receipt-set roots;
- asset-delta root;
- cross-shard inbox and outbox roots;
- write-set root;
- child claim, journal, source, and verifier roots.

The host recomputes the flat v1 composition directly and requires byte-for-byte
equality with the projection emitted by the recursive-v2 composition.

### 7. Source-frozen build evidence

The committed v2 rebuild reference now pins the 20-file source closure that
contains the bounded-fanout harness. A target-absent same-host build reproduced
the aggregate program, raw ELF, image ID, dependency-source closure, and
both the one-leaf policy verifier and specialized two-leaf verifier.

The clean source root is:

```text
20e5587e3ed7b8f6c561295a04f2cc2de92b90fd38c070de08a33d55b5f7572a
```

The current source closure retains `anyhow` 1.0.102 for recursive-v2 image
identity and updates `quinn-proto` to 0.11.15. A canonical-path clean rebuild
with those exact inputs reproduced the program, raw ELF, image ID, and both
host verifiers byte-for-byte. `anyhow` 1.0.103 changes the guest identity and
therefore requires a separately governed proof-regeneration migration. The
1.0.102 pin is limited to this experimental evidence lane; release,
settlement, and production authority remain false.

`cargo audit` classifies 1.0.102 under the informational-unsound advisory
`RUSTSEC-2026-0190`, whose affected function is
`anyhow::Error::downcast_mut`. A scan of the exact Rust sources listed by the
clean target's dependency metadata found the method definition and no call to
that affected API. The final guest and verifier symbol tables also contain no
matching affected symbol. This reachability evidence narrows the temporary
exception; it does not prove the dependency safe or authorize a production
exception.

The source-pinned release harness then regenerated the two-leaf inner and root
receipts.

### 8. Cross-run proof comparison

The source-pinned run reproduced both authenticated journal hashes from the
earlier prototype run. Its Succinct receipt hashes differ from the historical
receipt hashes.

This establishes stable computation and journal semantics for these two runs.
It also shows that proof-byte determinism has not been established. Consumers
must bind authenticated claims and journals. Valid proving runs do not need
identical proof bytes.

### 9. Fail-closed live replay checker

The repository checker
`tools/check_risc0_recursive_v2_two_leaf_source_pinned_evidence.py` uses the
committed evidence manifest and rebuild reference as fixed trust inputs. Callers
cannot replace either trust root through CLI arguments.

In live mode it:

1. requires bounded regular artifact and executable files;
2. rejects symlinks and hash or size drift;
3. runs the source-pinned harness dry-run in both leaf orders;
4. requires identical authenticated journal surfaces;
5. runs the repository-pinned specialized two-leaf verifier in both leaf orders;
6. requires the exact leaf and node receipt hashes;
7. requires the specialized verifier to reject a duplicate spot leaf and
   swapped inner/root nodes with exact policy errors;
8. requires the source-pinned one-leaf verifier to reject the two-leaf surface
   with its exact policy error;
9. executes the missing-child-assumption control;
10. emits bounded machine-readable JSON.

The checker is replay and boundary evidence. It does not prove the checker
correct.

## How It Works

### Inner node

For canonical leaves `L_1, ..., L_n`, the host derives a recursive node input:

```text
InnerInput = (
  common scope,
  canonical verifier set,
  canonical authority set,
  exact leaf disclosures,
  exact receipt assumptions,
  derived commitment roots,
  fixed ABI bounds
)
```

The aggregate guest verifies every leaf assumption and recomputes the node
journal. The host verifies the returned Succinct receipt and requires its
authenticated journal bytes to equal the deterministic expected journal.

### Epoch root

The host derives a node-child descriptor from the authenticated inner receipt:

```text
InnerDescriptor = H(
  aggregate image ID,
  inner profile,
  inner verifier ID,
  inner verification claim,
  inner journal,
  inner statement
)
```

The epoch-root guest verifies the inner receipt, checks the descriptor, and
recomputes the same flat leaf projection. The resulting root journal commits to
one immediate inner node and all descendant leaves.

## Build And Test

Read `zk/AGENTS.md` and `docs/RISC0_CIRCUIT_QUALITY_CBC_SPEC.md` before changing
the guest, journal, image ID, receipt profile, or verifier.

Run host-only tests without rebuilding the guest:

```bash
cd zk/recursive_stark_v2_risc0
RISC0_SKIP_BUILD=1 cargo test --locked --all
RISC0_SKIP_BUILD=1 cargo clippy --locked --all-targets -- -D warnings
```

For evidence builds, invoke the Cargo executable pinned by
`config/proof_profiles/risc0_recursive_toolchain_lock.json`. Use an external,
initially absent target directory. Do not place `target/` inside either frozen
source scope.

## Dry-Run Composition

Dry-run mode verifies each leaf and computes both expected journals without
generating recursive receipts:

```bash
<release-harness> \
  <spot-leaf.proof.json> \
  <zusd-leaf.proof.json> \
  --dry-run
```

The JSON output reports:

- aggregate image ID;
- input leaf receipt hashes;
- inner and root statement hashes;
- journal and protocol-journal hashes;
- leaf and node counts;
- tree heights;
- authenticated projection roots;
- exact non-claims.

Reverse the two leaf paths and require the same inner and root journal fields.

## Generate Recursive Receipts

Use the pinned IPC prover and distinct output paths:

```bash
RISC0_PROVER=ipc <release-harness> \
  <spot-leaf.proof.json> \
  <zusd-leaf.proof.json> \
  --inner-out <two-leaf-inner.proof.json> \
  --root-out <two-leaf-root.proof.json>
```

The harness verifies each generated receipt before writing it. It also requires
the authenticated journal bytes to match the deterministic host composition.

## Replay The Source-Pinned Evidence

Run the committed replay checker with the exact artifacts and executables:

```bash
python3 tools/check_risc0_recursive_v2_two_leaf_source_pinned_evidence.py \
  --spot-leaf <spot-leaf.proof.json> \
  --zusd-leaf <zusd-leaf.proof.json> \
  --inner-artifact <two-leaf-inner.proof.json> \
  --root-artifact <two-leaf-root.proof.json> \
  --release-harness <source-pinned-release-harness> \
  --one-leaf-verifier <source-pinned-one-leaf-verifier> \
  --two-leaf-verifier <specialized-two-leaf-verifier> \
  --r0vm <pinned-risc0-3.0.5-r0vm> \
  --json
```

A successful report must retain false values for release, settlement, public
replay, privacy, cross-host reproducibility, general fanout promotion, and
production readiness.

Replay the same-profile pair with the committed staged checker:

```bash
python3 tools/check_risc0_recursive_v2_same_profile_two_spot_evidence.py \
  --baseline-spot-leaf <spot-a.proof.json> \
  --distinct-spot-leaf <spot-b.proof.json> \
  --duplicate-source-alias-leaf <spot-alias.proof.json> \
  --inner-artifact <same-profile-inner.proof.json> \
  --root-artifact <same-profile-root.proof.json> \
  --release-harness <source-pinned-release-harness> \
  --two-leaf-verifier <specialized-two-leaf-verifier> \
  --json
```

This checker stages digest-verified bytes in a private directory before use,
replays both valid leaf orders, and requires the duplicate-lane,
duplicate-source, swapped-node, and seal-mutation controls.

## Evidence Records

- Current clean-build and pinned one-leaf evidence:
  `docs/research/RECURSIVE_STARK_V2_CURRENT_EVIDENCE_20260710.json`
- Historical two-leaf prototype:
  `docs/research/RECURSIVE_STARK_V2_TWO_LEAF_EXPERIMENT_20260710.json`
- Source-pinned two-leaf regeneration:
  `docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json`
- Source-pinned same-profile two-spot evidence:
  `docs/research/RECURSIVE_STARK_V2_SAME_PROFILE_TWO_SPOT_EVIDENCE_20260710.json`
- CBC obligation matrix:
  `docs/research/RECURSIVE_STARK_CBC_MATRIX_20260709.json`

## Current Limits

The following claims remain unsupported:

- arbitrary-depth recursion;
- more than one immediate subtree beneath the epoch root;
- a governed general fanout profile;
- real proof evidence for fanouts other than two;
- nonempty accepted or rejected receipt-ID partitions in a real recursive
  proof;
- verified conflict scheduling, data availability, or carry semantics;
- complete zUSD repay, redeem, burn, liquidation, or stability-pool flows;
- durable atomic ZenoLedger admission;
- cross-host or reproducible-release equality;
- public replay;
- witness privacy or zero knowledge;
- settlement, throughput, release, or production authority.

The next strongest proof target is a source-pinned multi-leaf run with nonempty
receipt partitions. The next authority target is durable atomic ZenoLedger
admission using authenticated, pinned recursive-verifier facts.
