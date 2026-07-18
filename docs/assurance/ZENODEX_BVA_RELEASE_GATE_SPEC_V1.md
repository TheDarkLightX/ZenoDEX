# ZenoDEX Value-Moving BVA Release Gate v1

## Status

This is a release-blocking assurance contract. It does not claim that ZenoDEX is BVA-complete.

The matrix at `docs/assurance/zenodex_bva_matrix_v1.json` inventories value-moving commands and authoritative fields across spot, perpetuals, zUSD, generic tokens, Oracle economics, keys, ZenoLedger/ZenoProof, proof-mining rewards, FIRE/ZenoCover, and committed-state ownership.

The checker has two deliberately different modes:

- **Critical mode** validates the schema, source-bound inventories, duplicate rejection, exact test selectors, and permanent regressions. It must pass on pull requests.
- **Promotion mode** additionally requires every inventoried command and field to have complete applicable boundary cases, immutable executed evidence, and source-bound authority. It must fail while any obligation is incomplete.

A green critical check therefore means that audit debt is explicit and cannot disappear. It is not production approval.

## Required boundary profiles

For a declared numeric range `L <= x <= U`, the minimum evidence is:

```text
L-1, L, L+1, U-1, U, U+1
```

Every applicable value-moving boundary must also cover:

- Boolean-as-integer rejection;
- absent versus explicit null;
- empty, singleton, maximum-size, and maximum-plus-one collections;
- duplicate identities, canonical aliases, depth limits, and cycles;
- mixed conjunction cases rather than only one guard at a time;
- overflow-adjacent arithmetic;
- nonce, deadline, retry, and replay boundaries;
- terminal drain and lifecycle exits;
- rejected transition is an exact no-op.

Profiles are reusable names in the matrix. Each completed item selects only the profiles that are semantically applicable, but it must cover every case in those selected profiles.

## Inventory contract

An inventory item is either:

1. extracted from a mounted source declaration, such as a Python enum, dataclass, or action registry; or
2. listed manually as acknowledged audit debt.

Source extraction prevents a newly added command or state field from being omitted silently. A new extracted item has no coverage entry and therefore blocks promotion automatically.

Manual items keep known surfaces visible, but a surface containing manual authority inventory is not production-complete. Before promotion, each manual item must be replaced by or bound to an exact mounted source registry.

## Evidence contract

Production evidence entries have the exact shape:

```json
{
  "path": "relative/repository/path",
  "sha256": "64 lowercase hexadecimal characters",
  "commit": "immutable commit identity",
  "toolchain": "pinned toolchain identity",
  "executed": true
}
```

With file verification enabled, the checker recomputes each SHA-256 digest. Promotion rejects missing evidence, unexecuted evidence, hash mismatches, partial status, missing cases, and repository claim status other than `complete`.

## Permanent perps regression

`PERP-V3-ML-BVA-112-ORACLE-USABLE` is a critical sentinel. It preserves the defect exposed by ML-BVA vector 112:

- action: `settle_epoch`;
- `oracle_seen = false`;
- `index_price_e8 = 0`;
- expected model result: `GuardFalse`;
- historical native result: accepted.

Critical mode requires both minimized regressions:

```text
tests/kernels/test_perp_epoch_isolated_v3_ml_bva_cases.py::test_v3_native_settlement_rejects_unusable_oracle_boundaries
tests/core/test_perp_v4_parity.py::test_v4_settlement_oracle_boundaries_match_generated_reference
```

The regression includes unseen Oracle, zero index price, stale-by-one, and rejection-no-op boundaries. Removing or renaming either selector fails the gate.

## Gate commands

Pull-request integrity:

```bash
bash tools/run_zenodex_bva_gate.sh critical
```

Production promotion:

```bash
bash tools/run_zenodex_bva_gate.sh promotion
```

The production command is expected to fail until the matrix is genuinely complete. It must never be bypassed by changing `claim_status` alone because every inventory item, case, and evidence record is checked independently.

## Current nonclaims

The initial matrix is intentionally marked `blocked`. It inventories 85 commands and 228 authoritative fields, but most per-item coverage entries are absent. The initial commit closes the vector 112 regression and establishes governance over the remaining work. It does not retroactively interpret existing edge tests as complete BVA evidence.
