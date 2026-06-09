# zenodex-governance-gate

Pure verdict kernel for the ZenoDEX governance gates — the Rust leg of a
**3-way differential**: the same Boolean gates exist as Tau specs
(`src/tau_specs/governance/gov_*_v1.tau`, bf-layer verified: compile +
non-vacuity + per-guardrail teeth) and as the Python runtime mirror
(`gov_gate.py`); none of the three is trusted over the others.

## What is in scope

- The six pointwise revision gates (fee / router split / router per-share step /
  collateral pair / whale defense / funding cap) and the universal
  `action_bound_ok`.
- The four trajectory-tier bits (drift budget / cooldown / charter / epoch
  budget) — the autonomy envelope.
- `params_digest`: the canonical params encoder
  (`sha256(json([["k",v],...] sorted, no whitespace))`), byte-compatible with
  `gov_epoch.params_digest`. This is the cross-language golden-vector surface:
  if the two encoders ever drift, every pin built on them breaks, so the shared
  fixture carries digest vectors computed by Python that this crate must
  reproduce exactly.

**Not** in scope (yet): the epoch machine (state, receipts, reject-is-no-op) —
that transition ports later with its own reject-is-no-op Kani harnesses;
`gov_epoch.py` remains the reference machine.

## The domain boundary vs the Python shell

The Python mirror takes unbounded ints and **hard-rejects** out-of-domain
values and hostile types (int/str/dict subclasses, bool-as-int). In Rust that
attack class is *unrepresentable*: the domain is the type (`u16`), flags are
real `bool`s, and there is no subclassing or monkeypatching. Consequently the
shared fixture contains only in-domain cases; Python's out-of-domain rejections
are Python-shell behavior covered by `test_gov_gate.py`. The wrap-safe
subtraction-guard forms (the bv[16] timelock/cooldown/charter wrap bypasses
probed in the Tau teeth) map onto `checked_sub` one-to-one — underflow is not
rejected here, it cannot be expressed.

## Parity fixture (single source of truth)

`tests/tau_specs/governance/fixtures/gov_gate_parity_cases.json` is GENERATED
from `gov_parity_cases.py` (the table the Tau↔Python differential drives) by
`gen_rust_parity_fixture.py`, and `test_gov_parity.py::test_rust_fixture_in_sync`
byte-pins it — the fixture cannot silently drift from the source table, and
this crate's `tests/parity.rs` runs every case plus the digest vectors.

```bash
# regenerate after editing gov_parity_cases.py
python3 src/tau_specs/governance/gen_rust_parity_fixture.py

# run the Rust leg
cd rust-runtime && cargo test -p zenodex-governance-gate
```

## Verification

- `cargo test` — unit teeth + the 39-case shared table + digest golden vectors.
- `cargo clippy` — clean under `#![forbid(unsafe_code)]` and
  `#![deny(clippy::arithmetic_side_effects)]` (checked or provably-widened
  arithmetic only).
- `cargo kani -p zenodex-governance-gate` — `#[cfg(kani)]` harnesses prove, over
  the FULL symbolic input domain (every `u16`/`bool` combination): no panic, and
  accept ⇒ invariant for `action_bound` (approval + timelock + band + step),
  `drift_budget` (`used ≤ budget ∧ |Δ| ≤ budget − used`), `cooldown`, `charter`
  (`¬revoked ∧ 0 < ttl ≤ 4096 ∧ granted ≤ now < granted+ttl`), `epoch_budget`,
  and the collateral pair (floor/ceiling/ordering/both steps). These are
  strictly stronger than the fixture: the fixture proves agreement on the
  boundary table, Kani proves the Rust kernel's verdicts imply the guardrails
  for *all* inputs.

## Authority posture

Reference / shadow tier. Default authority is the Python mirror
(`gov_gate.py`); nothing consults this crate in any live path. Promotion
follows the repo's CBC matrix discipline (running implementation + formal
spec + proof artifact + differentials + invariant checks + sign-off), the same
recipe as the perps E2 Rust shadow.
