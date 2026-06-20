# DST crash-consistency: the DexState snapshot commit (resilience gap #3, slice 1)

The highest-value slice of resilience gap #3 (true DST): **torn-write / disk-corruption
injection on the state-commit path**, with seed-reproducible recovery. (gitignored
prototype, 6 tests.)

## Why this slice
Full DST (virtualize clock/network/disk + an Elle/Knossos history-checker) is a large
build. But the single most consequential storage property ZenoLedger owns is:
**a crash or disk fault during a state commit must never leave a silently-corrupt
state that gets loaded as authoritative.** ZenoLedger already has the right primitive
for this — it persists state as a `DexSnapshot` whose `commitment_bytes()` is a
**sha256 cryptographic commitment** over the canonical snapshot bytes
(`src/integration/dex_snapshot.py`). So crash-consistency holds **by construction**:

    recovered snapshot is authoritative IFF
        sha256( domain_sep("dex_snapshot", v) || disk_bytes ) == committed_commitment

This harness injects real faults into the real snapshot bytes and proves the recovery
fail-closes on all of them.

## What's verified (exhaustively)
- **Intact** snapshot recovers and round-trips through `state_from_snapshot`.
- **Every torn write** is rejected — exhaustive over *all* truncation offsets
  `0..len-1`; only the complete payload is accepted.
- **Every single-byte corruption** is rejected — exhaustive over *every* position ×
  *every* other byte value (`len × 255` cases).
- **Valid-JSON corruption is still rejected** — the load-bearing property: a bit-rot
  that keeps the bytes parseable (a *different plausible* state) is caught by the
  commitment, never silently loaded.
- **Deterministic recovery** — same on-disk bytes → same verdict every time.
- **Seeded multi-byte corruption** — 500 random 1–8-byte faults, none accepted.

Net: the snapshot commit is crash-consistent / **fail-closed** under torn writes and
corruption — a node never adopts a partial or corrupt state as authoritative; it
rejects and falls back to replay/halt.

## Honest scope
This is the **storage/commit-path** slice only — the part ZenoLedger owns most
directly (consensus is Tau's). It does **not**:
- virtualize the full **clock/network/disk** (a VOPR/FoundationDB-style deterministic
  hypervisor) — it injects faults at the snapshot-bytes boundary;
- add an **Elle/Knossos** *operation-history* checker over recorded settlement
  histories (the other remaining #3 piece);
- exercise the live persistence I/O (it models the on-disk bytes, which is where a
  torn write/corruption manifests).

It uses the **real** `dex_snapshot` (`snapshot_from_state` / `state_from_snapshot` /
commitment) and the real canonical encoders, so the property is about production code,
not a toy. The remaining #3 pieces (IO virtualization, history-checker) are separate
follow-up slices.
