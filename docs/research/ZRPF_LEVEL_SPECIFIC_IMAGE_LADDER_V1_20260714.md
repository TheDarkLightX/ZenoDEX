# ZRPF finite level-specific image ladder

Status: research package, specified but not cryptographically executed.  
Class: non-authority tooling.  
Schema: `zrpf/finite-image-ladder-manifest/v1`.

This package turns the finite-ladder scaling hypothesis into a bounded,
fail-closed plan and validation gate. It deliberately does not make a proof,
soundness, throughput, admission, or production-authority claim.

## Design packet

- **Goal:** plan and structurally validate a full, regular ZRPF aggregation
  tree whose program image is different at every level and whose level `k`
  aggregate pins the exact image of level `k - 1`.
- **Affected modules:** this self-contained `agent_outputs/ladder` research
  package only.
- **Typed statement:** a `FiniteLadderManifestV1` describes one finite full
  tree with fanout `2..8`, depth `1..7`, a leaf-adapter image at level zero,
  and one distinct aggregate image for every higher level.
- **Authority boundary:** none. `authority` must be `false`,
  `admission_eligible` must be `false`, and the validator refuses any other
  value.
- **Invariants:** exact topology arithmetic; contiguous levels; distinct image
  identities; exact child-level and child-image binding; ordered exact child
  count; a single root; fail-closed schemas; explicit non-claims.
- **Disaster states:** self-image reuse, skipped levels, child-image
  substitution, topology-count drift, unknown critical fields, duplicate JSON
  fields, non-finite JSON numbers, and capacity arithmetic presented as
  evidence or authority.
- **Canonical bytes/hashes:** none are defined by this package. JSON is an
  interchange and research-validation format, not a ZRPF authority encoding.
- **Compatibility:** changing field meaning or accepted bounds requires a new
  manifest schema version.
- **Tests:** arithmetic boundaries, the first validation gate, mutation-style
  chain substitutions, strict JSON parsing, unknown-field rejection, and
  non-authority enforcement.
- **Formal obligation:** the ESSO artifact models only the bounded
  fanout-2/depth-3 construction sequence. It is not an unbounded proof and it
  does not model RISC Zero cryptography.
- **Dependencies:** Python standard library only.
- **Resource bounds:** manifest input is capped at 1 MiB; fanout is at most 8;
  depth is at most 7; all arithmetic is exact integer arithmetic.
- **Non-claims:** see the required manifest `non_claims` and the final section
  of this document.

## Why a finite image ladder

RISC Zero composition can repeatedly resolve receipt assumptions, but a ZRPF
aggregate guest must know which child program image it accepts. Reusing one
self-recursive guest would require the guest to approve its own image ID, which
creates a build and governance cycle. A finite ladder avoids that cycle:

1. build and identify the level-0 leaf adapter;
2. build level 1 with the exact level-0 image ID embedded;
3. build level 2 with the exact level-1 image ID embedded;
4. continue bottom-up to the finite root level;
5. bind all source, ELF, image, toolchain, and control provenance in a
   separately governed release artifact before considering authority.

Any change below a level invalidates every image above it. The manifest records
that chain; this validator checks internal consistency but cannot establish
that a RISC Zero image ID was actually derived from the recorded ELF.

## Topology

Only full regular trees are in scope. For fanout `f` and aggregate depth `d`:

```text
leaf_count          = f ** d
level_node_counts   = [f ** d, f ** (d - 1), ..., f, 1]
internal_node_count = sum(level_node_counts[1:])
total_node_count    = sum(level_node_counts)
edge_count          = total_node_count - 1
aggregate_rounds    = d
program_image_count = d + 1
```

The root receipt can remain constant-size while work, storage, and composed
soundness do not. The planner therefore calls every plan non-authoritative.

| Fanout | Depth | Leaves | Internal nodes | Total nodes | Meaning here |
| ---: | ---: | ---: | ---: | ---: | --- |
| 2 | 3 | 8 | 7 | 15 | first structural validation gate |
| 8 | 2 | 64 | 9 | 73 | current documented structural capacity |
| 8 | 7 | 2,097,152 | 299,593 | 2,396,745 | capacity arithmetic only |

The fanout-8/depth-7 row is not a throughput result and not an admissible
security claim. Before increasing authority-bearing capacity, ZRPF needs an
executable end-to-end soundness budget that includes every RISC-V segment,
recursion proof, resolved assumption, hash/collision term, and multi-proof
composition loss.

## Manifest contract

`config/proof_profiles/zrpf_finite_image_ladder_v1.example.json` is the first gate: fanout 2, depth 3, eight leaves,
seven aggregate nodes, and fifteen total nodes. Its digest values are visibly
synthetic test values and `build_provenance_status` says so.

The validator requires:

- exactly the documented fields at every schema object;
- lowercase 32-byte hexadecimal digest fields;
- levels `0..depth` in order;
- role `leaf_adapter` only at level 0 and `aggregate` above it;
- a unique image ID, ELF digest, source digest, and program ID at each level;
- aggregate level `k` binding exactly level `k - 1`, its image ID, the plan
  fanout, and ordered children;
- exact derived node counts and exactly one root;
- `authority: false`, `admission_eligible: false`, and all required
  non-claims.

It does not validate RISC Zero receipts, execute guests, reconstruct image IDs,
or establish build reproducibility.

## Commands

```bash
python3 tools/zrpf_level_ladder.py plan --fanout 2 --depth 3 --pretty
python3 tools/zrpf_level_ladder.py plan --fanout 8 --depth 7 --pretty
python3 tools/zrpf_level_ladder.py validate \
  config/proof_profiles/zrpf_finite_image_ladder_v1.example.json --pretty
python3 -m unittest discover -s tests -v
```

Successful validation prints `VALID_NON_AUTHORITY`. It means only that the
research manifest is internally consistent with this schema.

## First validation gate

The next cryptographic implementation gate is exactly fanout 2, depth 3:

- 8 verified leaf-adapter receipts;
- 4 verified level-1 aggregate receipts;
- 2 verified level-2 aggregate receipts;
- 1 verified level-3 root receipt;
- the sealed host verifier accepts only the exact root image/profile/control
  binding;
- omission, duplication, reordering, level substitution, image substitution,
  unresolved assumption, and profile/control substitution all reject;
- receipt, journal, cycle, wall-time, peak-memory, and storage measurements are
  captured with exact toolchain and backend provenance;
- a soundness ledger reports proved and conjectured estimates separately.

Passing this gate still does not grant settlement or production authority.

## ESSO bounded model

`docs/research/models/ZRPF_FINITE_LADDER_DEPTH3_ESSO_V1.json` follows the private ESSO repository's
`esso-ir/v1` `CandidateIR` schema at revision
`db8a3f8a782a508ada5005a2cf177f25c58f451d`. It models five reachable stages:
the level-0 layer, three level-specific builds, and non-authoritative gate
completion. Its invariants bind the built level to coverage, constructed node
count, last image identity, and `authority = false`.

`docs/research/models/ZRPF_FINITE_LADDER_DEPTH3_ESSO_CAMPAIGN_V1.json` records properties, seeded mutants, exact bounds, required
replay-receipt fields, and non-claims. The model is ready to copy into an ESSO
checkout and verify, for example:

```bash
python3 -m ESSO verify \
  docs/research/models/ZRPF_FINITE_LADDER_DEPTH3_ESSO_V1.json \
  --reference docs/research/models/ZRPF_FINITE_LADDER_DEPTH3_ESSO_V1.json \
  --output runs/zrpf_finite_ladder_depth3
```

No ESSO run result is included. Missing ESSO, solver `UNKNOWN`, timeout, or a
non-replayable result remains a recorded gap, never a pass.

## Required non-claims

The manifest repeats these exact machine-checked statements:

1. This artifact grants no settlement, admission, release, or production authority.
2. Capacity arithmetic is not measured throughput, latency, storage viability, or scalability evidence.
3. Manifest validation does not verify RISC Zero receipts, image derivation, build reproducibility, or cryptographic soundness.
4. The bounded fanout-2 depth-3 ESSO model is not an unbounded correctness proof.
5. A constant-size root receipt does not make child journals, witnesses, or data available.

