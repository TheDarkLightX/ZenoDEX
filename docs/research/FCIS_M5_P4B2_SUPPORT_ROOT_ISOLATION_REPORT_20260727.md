# FCIS M5-P4B2 Support-Root Isolation Report

## Result

`M5_P4B2_SUPPORT_ROOT_ISOLATION_COMPLETE_UNMOUNTED`

This checkpoint removes the mixed legacy `src/state/support_root.py` module
from the exact FCIS authority graph. It does not mount the FCIS evaluator or
authorize a production state transition.

Reviewed parent:

```text
3f4591b0b5d95efd33b416c25c04491a7999f03a
```

## Changed

- `src/state/support_root_primitives.py` now owns the version constants,
  `BatchStateSupport`, exact committed-balance support encoding, and the shared
  versioned support-section hash.
- `src/state/fcis_route_support_v5.py` owns the single route-pool support
  projection reused by legacy v4 differential evidence and FCIS v5.
- `src/state/committed_spot_roots.py` and
  `src/core/fcis_support_profile_v5.py` import only the extracted modules.
- `src/state/support_root.py` re-exports the historical protocol names and
  retains the mounted v4 implementation without being imported by exact FCIS
  authority modules.
- The structural checker rejects any final-mount authority source that imports
  `support_root.py`, and its inventory includes the two extracted modules.

## Invariant and authority impact

The checkpoint establishes this static reachability rule:

```text
path in FinalMountAuthorityPaths
and imports(path, src.state.support_root)
implies checker rejection
```

The v4 protocol byte language remains pinned. Exact committed readers and the
legacy v4 implementation use the same extracted support values and codecs.
The complete FCIS v5 support profile retains its existing state, context, and
command binding.

The final-mount findings changed as follows:

```text
before: 79
after:  64

src/core/dex.py                         2
src/core/route_settlement.py            9
src/core/settlement_strong_validator.py 26
src/state/legacy_state_snapshots.py     27
```

## Evidence

- Focused semantic and checker suite: `357 passed`.
- `state-substrate` profile: `ok=true`, zero violations.
- `exact-consumers` profile: `ok=true`, zero blocking violations.
- `final-mount` profile: honest fail-closed result with exactly 64 violations.
- Focused mypy: success on five changed exact source modules.
- Ruff check and format: pass on all changed Python files.
- Python compilation: pass.
- Security red-flag scan: no high findings. Two medium broad-exception findings
  remain in the legacy v4 module and were not introduced by this checkpoint.
- v4 legacy vectors, committed balance-root parity, committed spot-root parity,
  v5 support properties, and checker mutations are included in the 357-test
  result.

## Commands not run

- Full repository pytest.
- Broad critical quality gate.
- Production-boundary and permissionless-release gates.
- Rust, Tau, ESSO, Lean, RISC0, or production datastore lanes.
- GitHub Actions.

## Residual risk and nonclaims

- Route fields remain admitted through generic owned JSON inside the current
  intent grammar. `fcis_route_support_v5.py` is a single defensive projection,
  not the closed typed route-binding grammar required for promotion.
- The mixed strong validator, legacy snapshots, and `DexState` facade remain in
  the final-mount inventory.
- Full `dex_engine.apply_ops` ingress, authentication, proof binding,
  settlement-selection, rejection-precedence, and output parity remain open.
- No Python/Rust exact-byte parity is claimed.
- The reference commit port does not prove production datastore linearizability,
  crash recovery, or idempotent external delivery.
- No authority switch occurred.

## Next safest step

Create a closed, typed route-binding grammar and exact-only route replay module.
Migrate only FCIS v5 readers first. Preserve the legacy route parser as a
differential oracle until exact semantic and byte parity are established.
