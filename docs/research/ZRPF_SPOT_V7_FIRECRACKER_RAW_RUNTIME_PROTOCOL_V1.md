# ZRPF Spot V7 Firecracker Raw Runtime Protocol V1

Date: 2026-07-14

Status: exact host-side data codec implemented and tested; guest writer,
governed runtime manifest, live execution, and every authority claim remain
unimplemented

## Claim scope

This protocol defines the fixed request and output-device bytes for a future
Spot V7 Firecracker guest. It is independent of the retained structural V3
replay protocol.

The implemented host decoder establishes:

```text
exact request bytes
+ exact profile identity
+ request-bound fixed output image
+ zero unused output bytes
+ final commit marker
+ exact SpotSettlementV7VerifierOutputV1 framing
+ nested V7 journal associations
-> data-only decoded V7 payload
```

The decoder does not establish that a VM, Jailer, proof verifier, or release
authority produced those bytes.

## Profile identity

The canonical descriptor is embedded in
`tools/zrpf_spot_v7_firecracker_runtime_protocol.py`. It binds the magic values,
versions, byte order, field order, output bounds, nested payload codec, zero
region, commit domain, and commit formula.

```text
profile SHA-256:
0ff5876bdf454838ac7d59be61e68156d5eaed351f5ee83f716a526a72705f96

retained V3 profile SHA-256:
e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e
```

The identities intentionally differ. The V3 profile and its
`VerifiedReplayReport` payload cannot be relabeled as Spot V7.

## Request ABI

The request is exactly 192 bytes and uses little-endian integers.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | `ZSV7REQ1` magic |
| 8 | 2 | version `1` |
| 10 | 2 | request bytes `192` |
| 12 | 4 | flags, exactly zero |
| 16 | 32 | fresh run nonce |
| 48 | 32 | canonical V7 runtime-profile SHA-256 |
| 80 | 32 | governed runtime-manifest SHA-256 |
| 112 | 32 | exact input-drive SHA-256 |
| 144 | 8 | output bytes `16,777,216` |
| 152 | 4 | payload cap `65,536` |
| 156 | 32 | exact settlement-intent SHA-256 |
| 188 | 4 | reserved, exactly zero |

All four request digests must be nonzero. The request vector used by the tests
has SHA-256:

```text
05f3d19a3d83c90d40892bde3d2943d56573320c94799a4f2101cfcb07625824
```

## Output ABI

The output block device is exactly 16 MiB. Its 256-byte header uses
little-endian integers.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | `ZSV7OUT1` magic |
| 8 | 2 | version `1` |
| 10 | 2 | header bytes `256` |
| 12 | 4 | accepted status `1` |
| 16 | 4 | payload byte length |
| 20 | 4 | flags, exactly zero |
| 24 | 8 | output bytes `16,777,216` |
| 32 | 32 | request nonce |
| 64 | 32 | exact request SHA-256 |
| 96 | 32 | canonical V7 runtime-profile SHA-256 |
| 128 | 32 | runtime-manifest SHA-256 |
| 160 | 32 | input-drive SHA-256 |
| 192 | 32 | settlement-intent SHA-256 |
| 224 | 32 | payload SHA-256 |

The payload begins at byte 256. Every byte after the payload and before the
final 32-byte commit marker must be zero. This rejects stale bytes from a prior
run. The final marker is:

```text
SHA256(
  commit_domain
  || runtime_profile_sha256
  || request_sha256
  || exact_256_byte_header
  || exact_payload
)
```

The canonical test output image has SHA-256:

```text
24dfeb650061fe938b25d27b3079cd793720fe875c6a46b1b45a2eadd76baf53
```

The marker provides completion and internal binding. It is unkeyed and grants
no authenticity or execution provenance.

## V7 payload

`tools/zrpf_spot_v7_verifier_payload_codec.py` independently validates the
existing `ZSPTV7O1` verifier-output framing and nested `ZSPTV7J1` journal. It
checks:

- exact outer and nested lengths and versions;
- 19 nonzero output identities and commitments;
- 13 nonzero journal identities and commitments;
- exact semantic-journal and effect-binding journal sizes;
- semantic-journal SHA-256;
- effect-binding commitment;
- Plan B commitment association;
- exact Plan B byte SHA-256;
- output-to-journal program, profile, source, DA, state, action, and host-input
  associations.

It does not decode Postcard Plan B semantics. The governed Rust V7 verifier and
future PID-1 guest remain responsible for proving and authenticating those
semantics.

## Evidence

Focused replay:

```bash
python3 -m pytest -q \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py
```

The 38 tests cover canonical vectors, request mutation, wrong widths and zero
digests, all direct header bindings, stale and torn output, output truncation,
nonzero trailing bytes, commit-marker mutation, nested payload and journal
mutation, and one structure-preserving nested mutation that recomputes the
outer payload hash and commit marker before reaching the deeper Plan B reject.
They also require positive and negative parity with the pre-existing V7
candidate payload decoder.

Typing and lint gates:

```bash
python3 -m ruff check \
  tools/zrpf_spot_v7_firecracker_runtime_protocol.py \
  tools/zrpf_spot_v7_verifier_payload_codec.py \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py

python3 -m mypy \
  tools/zrpf_spot_v7_firecracker_runtime_protocol.py \
  tools/zrpf_spot_v7_verifier_payload_codec.py \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py
```

The boundary-concolic-style mutation is offline discovery and regression
evidence. It is not a correctness proof.

## Non-claims and residual risks

The following remain false or unestablished:

```text
PID-1 guest writer implementation
Python/Rust byte-for-byte parity
governed V7 runtime manifest
current V6 or V7 receipt evidence
root-owned staging integration
live Jailer or Firecracker execution
cgroup and network-namespace lifecycle evidence
same-UID mutation resistance
hardware attestation
data availability or finality
settlement or release authority
production readiness
zero-knowledge privacy
covert-channel freedom
hardware side-channel resistance
```

## Next safe step

Implement the static Spot V7 PID-1 guest writer as an independent Rust mirror,
freeze cross-language request/output vectors, and require exact parity before
wiring this profile into root-owned jail staging. The governed runtime manifest
must commit the profile digest and exact guest binary before any live runner can
mint an execution capability.
