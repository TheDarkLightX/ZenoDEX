# ZDEX Tokenomics Lane Coordinator RISC0 V1

This workspace is an unmounted RISC0 3.0.6 recursive coordinator candidate for
the `ZDEX_TOKENOMICS` lane. It accepts one exact SHADOW module release and one
of two closed canonical input schemas: hyperdeflationary burn or policy-bound fee
allocation. It recomputes the matching deterministic Rust lane coordinator,
verifies the exact release-selected child journal in the guest, and commits
only the canonical complete lane-composition journal.

The host admits only a cryptographically valid unconditional Succinct child
receipt whose image ID is the content-bound module release image and whose
journal is byte-identical to the recomputed burn or fee-allocation journal. It
inserts that real receipt as the sole assumption, requests a Succinct
coordinator receipt, and verifies the exact coordinator image and journal
before returning it. Historical burn input bytes retain their V1 schema; fee
allocation has a separate closed V1 schema and schema dispatch rejects every
other shape.

## Lightweight checks

```bash
RISC0_SKIP_BUILD=1 cargo test --workspace \
  --exclude zenodex-zdex-tokenomics-lane-coordinator-guest \
  --all-targets --locked
RISC0_SKIP_BUILD=1 cargo check \
  -p zenodex-zdex-tokenomics-lane-coordinator-guest --locked
RISC0_SKIP_BUILD=1 cargo clippy --workspace \
  --exclude zenodex-zdex-tokenomics-lane-coordinator-guest \
  --all-targets --locked -- -D warnings
cargo fmt --all -- --check
```

`RISC0_SKIP_BUILD=1` emits host-only placeholder method constants. Proving and
receipt-verifier APIs reject those placeholders. The ignored real-proof test
requires rebuilt child and coordinator ELFs and is intentionally outside the
lightweight local gate. The guest is compiled during the lightweight gate and
is not executed as a native Linux test binary.

## Nonclaims

- Status is SHADOW.
- This workspace is unmounted.
- It has no settlement, publication, writer, or value-moving authority.
- It does not activate a lane, route, profile, or ZenoLedger commit path.
- A real recursive proof for the fee-allocation coordinator path has not been
  run for this candidate. The earlier burn-only proof does not establish the
  new image or fee path.
- The coordinator checks internal policy/root consistency. Profile-selected
  policy governance and release-bound cycle enforcement remain admission-layer
  obligations.
- Lightweight tests do not establish proof performance, production readiness,
  deployment safety, or whole-economy semantic closure.
