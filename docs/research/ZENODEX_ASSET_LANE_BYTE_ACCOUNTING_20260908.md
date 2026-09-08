# Derived canonical byte accounting

Date: 2026-09-08

Status: the scoped Lean source compiles, independent byte comparisons pass,
and independent mathematical review accepts the stated contract.
The retained test harness passes an independent fresh replay.
`formal_core_complete=false`; authority remains `NONE`.

## Proved contract

[AssetLaneFiniteByteAccountingV2.lean](../../lean-mathlib/Proofs/AssetLaneFiniteByteAccountingV2.lean)
extends the [finite row-growth relation](ZENODEX_ASSET_LANE_ROW_GROWTH_20260908.md)
to exact serialized lengths. The encoder accounts for JSON punctuation, quote
and backslash escaping, decimal integer digits, and the empty-array correction.
It preserves the registered supply row when its amount becomes zero.

For a selected account update, define `Wold` and `Wnew` as its old and new
balance-row byte costs including one comma, or zero when the row is absent.
Define `Sold` and `Snew` as the selected supply-row costs, and `Eold` and `Enew`
as the empty-balance-table indicators. With fixed serialized metadata:

```text
Bpost + Wold + Sold + Eold = Bpre + Wnew + Snew + Enew
```

The old and new costs and the new empty-table indicator are computed from the
source rows and signed update. The proof derives the equality from erase, put,
sort, supply update and recomposition; it does not assume a post-state size.
Uniqueness, registered-asset membership, supply order, the accounts domain and
selected managed-asset membership are explicit premises where required.

`recomposition_capacity_iff` combines this equality with the row-count law to
derive an exact source-based criterion for both post-state capacity limits.
`lane_capacity_4096_1048576` instantiates the actual row and byte limits.
Separate token-closure theorems cover the admitted printable ASCII domain.

## Checked evidence

The proof source SHA-256 is
`f328e1ad6c282ba8cd8b17c10d45a47eb752fe33db4591da8e10be479addae97`.
Root verification rebuilt its complete 24-module dependency chain from source
with pinned Lean 4.27.0. An independent runtime comparison then checked 399
amount-row encodings and 117 supply-row encodings against Python: all 516
complete byte arrays agreed. These cases cover every printable ASCII byte in
the three amount-row identifier positions, escaped 160-byte identifiers, zero,
one, the u128 maximum and decimal-width boundaries through 10^38.

Zero-amount encoding controls test the encoder; they do not establish that zero
balance rows are admitted runtime states. These comparisons are finite evidence,
not a universal implementation-refinement theorem. Initial diagnostic output
used Lean's abbreviated list renderer; verification rejected that output. The
consumer was changed to print complete numeric arrays before exact comparison.

Independent Astra review compiled 16 literal byte goldens and 17 additional
consumer theorems. All 57 audited target/consumer/golden declarations use only
standard Lean axioms. The review checked false escape and omitted-zero-supply
statements, duplicate-key and missing-registration controls, and the exact
capacity theorem signatures. Its dependency check verified 23 source/object
pairs; the separate root run rebuilt those dependencies. Neither review nor
the byte-size theorem grants publication authority.

The review retained two tooling limits: a generic cross-language scanner's
question-mark matches in checked Lean dependencies were classified individually,
and an optional negative-integer literal check remained unproved because of an
opaque standard-library string operation. That diagnostic is not counted as a
successful negative control. Nonnegative runtime quantity encodings have the
separate comparisons described above.

The separate [runtime boundary tests](ZENODEX_ASSET_LANE_RESOURCE_OUTCOMES_20260908.md)
exercise real Python and Rust transitions at 1,048,576 bytes and one byte beyond,
including escaped-owner row insertion and decimal growth without row insertion.

The retained harness is
[test_lean_asset_lane_finite_byte_accounting_v2.py](../../tests/formal/test_lean_asset_lane_finite_byte_accounting_v2.py),
SHA-256 `68b3a10c52db2616b32d5baa352417907ac6018d5be860dd3eeb5f0fb86f5508`.

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_lane_finite_byte_accounting_v2.py
python3 -m ruff check tests/formal/test_lean_asset_lane_finite_byte_accounting_v2.py
python3 -m ruff format --check tests/formal/test_lean_asset_lane_finite_byte_accounting_v2.py
```

All eight tests passed in the root replay, including a fresh 24-module source
build, six exact theorem contracts, byte-array comparisons and four deliberately
false byte laws rejected at their semantic goals. The false laws omit escaping,
the empty-array correction, funded decimal growth or retained zero supply rows.
Final formatting preserved the exact parsed Python syntax tree, including every
embedded Lean string. Ruff and formatting checks pass. The claims-registry
gate remains failing on the missing derivatives authorization checker; this
checkpoint does not close that independent blocker.

## Remaining obligations

The metadata byte parameters are fixed inputs to this proof. Their correspondence
to owned runtime policy records needs a separate serializer relation. The size
theorems do not establish quantity bounds, all constructor checks, authentication,
the complete rejection order or effect authority. The resource-aware finite
outcome model and its correspondence to Python and Rust remain open; existing
formal enum/source-pin failures must remain visible until that extension passes.

No full Lake, Kani, ESSO or RISC0 guest/proving build was performed for this
checkpoint. Publication, durability, finality and production promotion remain
outside its proved contract.
