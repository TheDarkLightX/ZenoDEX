# ZRPF Spot V7 Firecracker Raw Runtime Protocol V1

Date: 2026-07-14

Status: exact request/output codecs, structural Python/Rust V7 payload decoders,
a protocol-only static PID-1 writer, cross-language vectors, and authority-false
root-owned prepare/finish identity binding are implemented and tested; receipt
verification in the guest, governed release selection, live execution, and
every authority claim remain unimplemented

## Claim scope

This protocol defines the fixed request and output-device bytes for a future
Spot V7 Firecracker guest. It is independent of the retained structural V3
replay protocol.

The Python structural decoder and independent Rust mirror establish:

```text
exact request bytes
+ exact profile identity
+ request-bound fixed output image
+ zero unused output bytes
+ final commit marker
+ structural SpotSettlementV7VerifierOutputV1 framing
+ nested V7 journal associations
-> data-only decoded V7 payload
```

The decoder does not establish that a VM, Jailer, proof verifier, or release
authority produced those bytes. It does not decode Postcard Plan B semantics,
and nonzero committed identities are structurally bounded rather than governed.

The PID-1 binary mounts one bounded read-only SquashFS input, reads a
precomputed `ZSPTV7O1` payload, rechecks the complete input-drive hash, zeroes
the fixed output device, writes the bound header and payload, synchronizes, and
writes the commit marker last. It deliberately has no RISC0 receipt-verification
path. Its output remains data-only.

## Profile identity

The canonical descriptor is embedded independently in
`tools/zrpf_spot_v7_firecracker_runtime_protocol.py` and
`zk/spot_settlement_v7_risc0/firecracker_runtime/src/lib.rs`. It binds the magic
values, versions, byte order, field order, output bounds, nested payload codec,
zero region, commit domain, and commit formula.

```text
profile SHA-256:
c8cf02b22988315b667c8b37675b6c8d8cd56f5638b8aa176357a044a89fcdd6

retained V3 profile SHA-256:
e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e
```

The identities intentionally differ. The V3 profile and its
`VerifiedReplayReport` payload cannot be relabeled as Spot V7.

## Request ABI

The request is exactly 224 bytes and uses little-endian integers. V7 rejects
the legacy 192-byte framing rather than inferring a missing machine-config
identity.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | `ZSV7REQ1` magic |
| 8 | 2 | version `1` |
| 10 | 2 | request bytes `224` |
| 12 | 4 | flags, exactly zero |
| 16 | 32 | fresh run nonce |
| 48 | 32 | canonical V7 runtime-profile SHA-256 |
| 80 | 32 | exact proposed runtime-manifest SHA-256 |
| 112 | 32 | exact proposed canonical machine-config SHA-256 |
| 144 | 32 | exact input-drive SHA-256 |
| 176 | 8 | output bytes `16,777,216` |
| 184 | 4 | payload cap `65,536` |
| 188 | 32 | exact settlement-intent SHA-256 |
| 220 | 4 | reserved, exactly zero |

All five 32-byte request bindings must be nonzero. The request vector used by the tests
has SHA-256:

```text
f5f7ce3112563ca79383d8c7502e36df1db78e2d3bc0f32df7b8d09e38ac2c23
```

## Output ABI

The output block device is exactly 16 MiB. Its 288-byte header uses
little-endian integers. V7 rejects a header declaring the legacy 256-byte
framing.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | `ZSV7OUT1` magic |
| 8 | 2 | version `1` |
| 10 | 2 | header bytes `288` |
| 12 | 4 | data-only committed status `1` |
| 16 | 4 | payload byte length |
| 20 | 4 | flags, exactly zero |
| 24 | 8 | output bytes `16,777,216` |
| 32 | 32 | request nonce |
| 64 | 32 | exact request SHA-256 |
| 96 | 32 | canonical V7 runtime-profile SHA-256 |
| 128 | 32 | runtime-manifest SHA-256 |
| 160 | 32 | canonical machine-config SHA-256 |
| 192 | 32 | input-drive SHA-256 |
| 224 | 32 | settlement-intent SHA-256 |
| 256 | 32 | payload SHA-256 |

The payload begins at byte 288. Every byte after the payload and before the
final 32-byte commit marker must be zero. This rejects stale bytes from a prior
run. The final marker is:

```text
SHA256(
  commit_domain
  || runtime_profile_sha256
  || request_sha256
  || exact_288_byte_header
  || exact_payload
)
```

The canonical synthetic Python fixture output has SHA-256:

```text
62a13ecdd2df03c7d17da2b13c4f7e40401b4ae7236188a4b29822c77be7d467
```

The independently encoded Python/Rust output containing the retained canonical
V7 verifier-output vector has SHA-256:

```text
d5d88a069e65df2776ce440a148695998abe2ad0ee9185cdd4c9c4bd0eccc595
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
a future authority-capable PID-1 profile remain responsible for proving and
authenticating those semantics.

## Evidence

Focused Python replay and cross-language parity:

```bash
python3 -m pytest -q \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py \
  tests/test_zrpf_spot_v7_firecracker_rust_parity.py \
  tests/test_zrpf_spot_v7_firecracker_runtime_binding.py \
  tests/test_zrpf_v3_firecracker_jail_staging.py \
  tests/test_zrpf_v3_firecracker_jailer_launcher.py
```

The focused protocol tests cover canonical vectors, request mutation, wrong widths and zero
digests, all direct header bindings, stale and torn output, output truncation,
nonzero trailing bytes, commit-marker mutation, nested payload and journal
mutation, and one structure-preserving nested mutation that recomputes the
outer payload hash and commit marker before reaching the deeper Plan B reject.
They also require positive and negative parity with the pre-existing V7
candidate payload decoder, exact agreement with a Rust positive vector, and
stable Python/Rust reject-code parity for four transport and nested mutations.
The runtime-binding and lifecycle tests additionally reject config and manifest
substitution, a stale profile, legacy 192/256 framing, and same-byte replacement
of the staged config path after preparation.

Focused Rust gates:

```bash
cd zk/spot_settlement_v7_risc0
cargo fmt --all -- --check
cargo test --locked --offline \
  -p zenodex-zrpf-spot-v7-firecracker-runtime --all-targets
cargo clippy --locked --offline \
  -p zenodex-zrpf-spot-v7-firecracker-runtime --all-targets -- -D warnings
```

Seven Rust tests cover the profile and request vectors, the retained V7 payload,
the fixed committed output, transport mutations, nested payload mutations, and
the PID-1 path/bound/non-authority contract. They also require legacy framing
rejection. A rejected input-drive binding is checked to leave the commit marker
absent.

The static-PIE build and ELF inspection are reproducible with:

```bash
cd zk/spot_settlement_v7_risc0
bash firecracker_runtime/scripts/check_static_pid1_v1.sh
```

The checker builds `x86_64-unknown-linux-gnu` with target-specific
`+crt-static` and rejects `PT_INTERP` or `DT_NEEDED`. This local build is
compile evidence only and is not a governed release binary.

Typing and lint gates:

```bash
python3 -m ruff check \
  tools/zrpf_spot_v7_firecracker_runtime_protocol.py \
  tools/zrpf_spot_v7_firecracker_runtime_binding.py \
  tools/zrpf_spot_v7_firecracker_jailer_lifecycle.py \
  tools/zrpf_spot_v7_firecracker_jail_staging.py \
  tools/zrpf_v3_firecracker_jail_staging.py \
  tools/zrpf_v3_firecracker_jailer_launcher.py \
  tools/zrpf_spot_v7_verifier_payload_codec.py \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py \
  tests/test_zrpf_spot_v7_firecracker_rust_parity.py

python3 -m mypy \
  tools/zrpf_spot_v7_firecracker_runtime_protocol.py \
  tools/zrpf_spot_v7_firecracker_runtime_binding.py \
  tools/zrpf_spot_v7_firecracker_jailer_lifecycle.py \
  tools/zrpf_spot_v7_firecracker_jail_staging.py \
  tools/zrpf_v3_firecracker_jail_staging.py \
  tools/zrpf_v3_firecracker_jailer_launcher.py \
  tools/zrpf_spot_v7_verifier_payload_codec.py \
  tests/test_zrpf_spot_v7_firecracker_runtime_protocol.py \
  tests/test_zrpf_spot_v7_firecracker_rust_parity.py
```

The boundary-concolic-style mutation is offline discovery and regression
evidence. It is not a correctness proof.

## Non-claims and residual risks

The following remain false or unestablished:

```text
RISC0 receipt verification inside the PID-1 guest
authority-capable PID-1 guest profile
governed V7 runtime manifest
current V6 or V7 receipt evidence
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

The runtime binding retains exact canonical config and manifest bytes and
hashes them into prepare/finish evidence. Those bytes remain proposals until a
separately governed release manifest selects the same identities. A caller can
construct an authority-false proposal; it cannot manufacture governance,
release, execution, settlement, or production authority.

The pre/post input-drive hashes do not close an ABA attack by a hostile host:
mutable backing bytes could be substituted while SquashFS reads the payload and
restored before the second whole-drive hash. A future authority profile must
use root-owned immutable backing for the full VM lifetime and test that launcher
property. This protocol-only profile intentionally cannot promote its observed
input binding to execution authority.

## Next safe step

Freeze and govern the V7 release manifest, then bind a separate
authority-capable PID-1 profile to actual V6/V7 receipt verification. The
release must select this profile digest, the exact machine configuration, guest
binary, kernel, rootfs, input contract, and verifier identities before a live
runner can mint an execution capability.
