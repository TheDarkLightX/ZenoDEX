# ZRPF Spot settlement V7 guest-input builder CBC specification

Date: 2026-07-14

Status: implemented authority-neutral host tooling

## Purpose

The builder creates one canonical `ProposedSpotSettlementV7EnvelopeV1` from
four separately materialized canonical components. It removes ad hoc framing
from the host handoff to the V7 guest while preserving the guest as the first
authority-bearing interpretation boundary.

```text
canonical V6 settlement-admission journal
+ canonical V6 full-blob DA certificate
+ canonical V6 source-opened replay
+ canonical V7 state-root host input
                |
                v
strict decode and exact canonical re-encode
                |
                v
ProposedSpotSettlementV7EnvelopeV1
                |
                v
create-new exact output artifact
```

## Inputs

The CLI requires exactly one path for each input and one new output path:

| Option | Exact type | Bound |
| --- | --- | ---: |
| `--source-child-journal` | `SettlementAdmissionJournalV1` | `MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1` |
| `--data-availability-certificate` | `FullBlobDataAvailabilityCertificateV1` | `MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1` |
| `--replay` | `ProposedSourceOpenedSpotSettlementReplayV3` | `MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3` |
| `--state-root-host-input` | `BoundedSpotStateRootV7HostInputV1` | `MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1` |
| `--output` | canonical V7 guest envelope bytes | create-new only |

Unknown, duplicate, missing, and valueless options reject with stable typed
error codes.

## Construction invariants

For each proposed component byte string `b` and its exact typed decoder `D`
and canonical encoder `E`, construction requires:

```text
x = D(b)
E(x) = b
```

The builder then applies the same rule to the complete envelope. It never
normalizes a noncanonical proposal into an accepted artifact.

The four inputs are interpreted only as proof-neutral canonical proposals.
Their cross-component semantic relationship is intentionally left to the V7
guest after child-receipt verification.

## File boundary

Input reads require:

- one regular file with one link;
- no symlink following on Unix;
- declared byte ceiling checked from metadata before the read;
- a ceiling-plus-one bounded descriptor read;
- stable device, inode, mode, size, modification time, and change time across
  the descriptor and final path check on Unix.

Output persistence requires:

- `create_new`, so replacement and overwrite reject;
- no symlink following on Unix;
- one regular file with one link;
- mode `0600` on Unix;
- complete write and `sync_all`;
- exact descriptor reread and stable final path identity.

## Authority boundary

The builder's receipt, settlement, and production authority constants are
permanently `false`. Successful construction establishes only:

> The output is the canonical V7 envelope containing the four exact canonical
> component byte strings supplied to this invocation.

It does not establish:

- V6 or V7 receipt validity;
- child program or receipt-profile identity;
- data availability or retrievability;
- replay-to-certificate binding;
- source-transition correctness;
- pre-state or post-state correctness;
- release, finality, settlement, or production authority.

These obligations remain in the V7 guest, sealed host verifier, finality and
DA gates, and future atomic application-state admission path.

## Executable evidence

The package tests cover:

- permanent authority-neutral constants;
- deterministic exact four-component composition;
- strict rejection of malformed and trailing component bytes;
- strict CLI option handling;
- exact binary success behavior with empty stdout and stderr;
- one stable bounded reject line on binary failure;
- create-new output and no-overwrite behavior;
- mode `0600` output on Unix;
- output absence after component rejection;
- symlink-input rejection on Unix;
- hard-linked input rejection on Unix;
- empty and oversized input rejection before decoding or output creation.

The direct `libc = 0.2.186` dependency supplies only the Unix
`O_NOFOLLOW`/`O_CLOEXEC` open flags. It is pinned, already present in the
workspace dependency closure, and licensed under MIT or Apache-2.0. A future
portable standard-library no-follow API can remove it without changing the
builder contract.

The required `zrpf-assurance` Rust lane runs all builder targets and the
workspace Clippy gate. This slice changes no governed V6 or V7 image identity,
receipt profile, or release pin and produces no proof evidence.
