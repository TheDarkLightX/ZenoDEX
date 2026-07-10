# ZRPF V3 Protocol Nucleus

This workspace contains the proof-system-neutral structural protocol candidate
for the Zeno Recursive Proof Fabric used by ZenoDEX.

The crate currently provides:

- nonzero typed identifiers and commitments;
- a shared leaf-and-aggregate `NodeJournalV3` shape;
- application, domain, epoch, policy, dependency, and toolchain scope binding;
- verifier IDs derived from program ID, proof profile, and journal version;
- exact, bounded, canonical Postcard decoding;
- canonical dense child partitions and checked tree counts;
- explicit operation-count units, with mixed-unit aggregation rejected;
- a mandatory provenance commitment for source-proof adapters;
- derived child task, claim, journal, program, profile, verifier, statement,
  manifest, effect, provenance, and data-availability roots;
- a bounded fanout-8, depth-2 profile covering at most 64 leaves.

## Authority Boundary

This crate validates structure. It does not verify a proof receipt or ZenoDEX
effect semantics.

`ProjectedChildDescriptorV3::project_canonical_journal` derives metadata from
exact canonical journal bytes. The resulting descriptor has no proof authority.
A proof-backend adapter must verify the exact receipt claim, governed program,
and exact journal bytes before an authority-bearing aggregate guest uses it.
The additive `zk/zrpf_risc0` profile implements that ordering for the Spot V1
compatibility adapter and the bounded level-one and level-two structural guests.

`NodeCommitmentsV3` makes all ZenoDEX commitment fields mandatory and nonzero.
The compatibility adapter derives its field-specific values from an
authenticated V1 journal, and the structural guests derive roots over those
authenticated child commitments. A separate native leaf and semantic aggregate
profile must derive or verify their ZenoDEX meanings. The current structural
profile does not establish conservation, descendant uniqueness, message
cancellation, scheduling, carry continuity, or data availability.

The full claim boundary and next steps are documented in
`docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md` from the
repository root.

## Verification

Run with the repository-pinned Rust toolchain:

```bash
cargo fmt --all -- --check
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --doc
```

The independent Python hash-vector replay is run from the repository root:

```bash
python3 tools/check_zrpf_v3_hash_vector.py
```
