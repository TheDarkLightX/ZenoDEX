# ZRPF Spot Settlement V7 Local Evidence CBC Specification

Date: 2026-07-13

Status: authority-neutral evidence tooling implemented; fresh proof artifacts pending

Authority: none

## Purpose

The Spot Settlement V7 guest is intended to close the relation between one
authenticated source-opened V6 settlement, the exact Spot transition, the
typed state-root transition, and the exact Settlement Effect Plan B. A future
release needs one retained artifact set whose byte relationships can be
checked independently before any cryptographic or operational claim is
considered.

This evidence lane records and checks that artifact set. It deliberately
separates static byte binding from receipt verification and runtime provenance.

```text
fresh V7 proof artifacts
  -> bounded stable snapshot
  -> exact static relation checker
  -> canonical authority-neutral evidence record
  -> later cryptographic replay and release gates
```

The current implementation supplies the first three stages. No real V7
receipt is committed by this change.

## Fixed artifact inventory

One bundle contains exactly seven regular single-link files:

| Artifact | Meaning |
| --- | --- |
| `spot-settlement-v7.receipt.json` | Canonical structurally Succinct V7 receipt |
| `spot-settlement-v7.seal-word-1-xor-lsb.receipt.json` | Exact one-bit seal mutation |
| `source-opened-spot-settlement-v6.child.receipt.json` | Canonical structurally Succinct V6 child receipt |
| `spot-settlement-v7.guest-input.bin` | Exact bounded V7 guest envelope |
| `spot-settlement-v7.journal.bin` | Exact V7 journal bytes |
| `spot-settlement-v7.verifier-output.bin` | Exact data-only V7 verifier output |
| `spot-settlement-v7.plan-b.bin` | Exact Settlement Effect Plan B bytes |

Unknown, missing, empty, oversized, symlinked, multiply linked, or unstable
artifacts reject. The aggregate artifact budget is 80 MiB.

## Statically checked relations

The checker independently verifies:

1. Exact canonical JSON and the pinned RISC0 Succinct/Poseidon2 structural
   profile for all three receipt objects.
2. V7 receipt journal bytes equal the retained journal.
3. V6 child receipt journal bytes equal the child-journal component of the V7
   guest input.
4. Receipt-claimed V7 and V6 image IDs equal the corresponding data-only
   verifier-output program IDs.
5. The mutation changes only Succinct seal word 1 and applies XOR mask `1`.
6. The verifier output embeds the retained V7 journal and binds all nineteen
   fixed output fields to the journal.
7. The retained Plan B is byte-identical to the plan inside the journal.
8. The child journal, source replay, and state-root host input are bound to the
   journal through exact SHA-256 values and bounded lengths.
9. The V7 profile ID, required child receipt-profile ID, and V7 program
   manifest root are independently derived using the Rust verifier's framed
   hash contracts.

The checker accepts no `verified=true` input and derives all evidence fields
from the artifact bytes.

## Deliberate DA boundary

The guest input contains the proposed full-blob DA certificate bytes. The
static checker retains those bytes inside the bounded guest-input artifact. It
does not decode the certificate, recompute its certificate root, validate the
replay blob, or establish retrievability.

This boundary is executable. A structure-preserving DA-certificate byte change
can still form a new authority-neutral candidate record, while the record
retains this exact non-claim:

```text
data_availability_certificate_bytes_are_retained_without_static_semantic_decode
```

The cryptographically verified V7 guest and later operational DA policy gate
own those stronger obligations.

## Builder behavior

`tools/build_zrpf_spot_settlement_v7_local_evidence.py`:

- accepts exactly the seven artifact IDs;
- reads each input through a stable descriptor with bounded length and
  before/after identity checks;
- derives the evidence document from the captured bytes;
- writes private staged outputs with `O_EXCL` and `fsync`;
- runs the independent checker against the staged candidate;
- publishes only a self-consistent candidate.

The bundle and evidence file require two filesystem renames. Publication is
therefore explicitly recorded as non-atomic. Release publication must use a
stronger governed container or content-addressed release transaction.

## Commands

After a fresh V7 proving run has produced all seven inputs:

```bash
python3 tools/build_zrpf_spot_settlement_v7_local_evidence.py \
  --recorded-at 2026-07-13 \
  --v7-receipt /absolute/input/spot-settlement-v7.receipt.json \
  --v7-receipt-seal-mutation /absolute/input/spot-settlement-v7.mutation.json \
  --v6-child-receipt /absolute/input/source-opened-v6.child.receipt.json \
  --v7-guest-input /absolute/input/spot-settlement-v7.guest-input.bin \
  --v7-journal /absolute/input/spot-settlement-v7.journal.bin \
  --v7-verifier-output /absolute/input/spot-settlement-v7.verifier-output.bin \
  --v7-plan-b /absolute/input/spot-settlement-v7.plan-b.bin \
  --bundle-directory /absolute/output/spot-settlement-v7-bundle \
  --evidence /absolute/output/spot-settlement-v7-evidence.json \
  --json
```

Independently check the resulting bytes with the exact digest emitted by the
builder:

```bash
python3 tools/check_zrpf_spot_settlement_v7_local_evidence.py \
  --evidence /absolute/output/spot-settlement-v7-evidence.json \
  --artifact-directory /absolute/output/spot-settlement-v7-bundle \
  --expected-evidence-sha256 <64-lowercase-hex> \
  --json
```

Focused tests:

```bash
python3 -m pytest -q tests/test_zrpf_spot_settlement_v7_local_evidence.py
```

## Claim boundary

Successful checking establishes:

- exact bounded artifact identities;
- the listed deterministic cross-artifact relations;
- exact protocol-identity derivations;
- one exact seal-mutation relationship;
- one canonical authority-neutral evidence record.

It does not establish:

- cryptographic validity of either receipt;
- rejection of the seal mutation by RISC0;
- source-to-binary or complete build-input provenance;
- execution inside Firecracker;
- data availability or retrievability;
- finality or durable atomic application-state commit;
- release, settlement, production, privacy, or covert-channel authority.

Those claims require a fresh C0/C1/C2-governed V7 build, real proof generation,
independent cryptographic replay, operational DA/finality checks, and the
combined atomic settlement gate.
