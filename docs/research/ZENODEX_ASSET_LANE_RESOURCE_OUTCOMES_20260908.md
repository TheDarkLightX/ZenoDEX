# Asset-lane resource outcomes and rejection ownership

Date: 2026-09-08

Status: Python and Rust implementations tested on isolated state; independent
reviews accepted the scoped repair. W07/W09 remain open. Authority remains `NONE`, profile
authentication remains `SHADOW`, and no deployed profile is activated.

## Repaired behavior

A valid aggregate can already contain 4,096 account rows while its managed leaf
is empty. Issuing one atom to a dormant managed asset produces a one-row leaf
candidate, but merging it into the aggregate requires a 4,097th row. The original
Python coordinator raised `ValueError` instead of returning a domain outcome.
Direct leaf growth and canonical-byte growth had the same boundary problem.

The shared size checker now distinguishes actual size excess. Transfer,
managed-lifecycle and coordinator post-state admission catch that specific
condition and return their own `STATE_RESOURCE_LIMIT` rejection. The limits
remain 256 assets, 4,096 balance rows and 1,048,576 canonical state bytes.

| Admission stage | Result for size excess |
| --- | --- |
| Malformed or oversized pre-state | Constructor/boundary error; transition admission has not succeeded. |
| Transfer post-state | `TRANSFER / STATE_RESOURCE_LIMIT`, with the transfer enum. |
| Managed post-state | `MANAGED_LIFECYCLE / STATE_RESOURCE_LIMIT`, with the managed enum. |
| Merged aggregate post-state | `COORDINATOR / STATE_RESOURCE_LIMIT`, with the coordinator enum. |

Earlier authorization and arithmetic guards retain precedence. Each domain
rejection has identical pre/post roots and an empty effect plan, including no
replay consumption, lane write or outbox enqueue. Unrelated construction errors
retain their original error path. No rounding, amounts, policy constants or
accepted-state fields change.

## Route-owned wire decoding

The existing wire constructor requires each route to own its exact rejection
enum. The original decoder instead searched enums by code text. A code shared
by two leaves could therefore decode into the wrong enum and fail construction.
Coordinator binding and projection rejections also carried a leaf route, which
the existing wire constructor could never accept.

One pure route-to-enum function now serves the domain constructor, wire
constructor and decoder. The decoder reads the route before its code. All
coordinator-owned rejections use `COORDINATOR`; propagated leaf rejections retain
their leaf route. Mixed route/enum pairs fail construction.

Wire fields and historical valid record bytes remain unchanged. The new resource
code is an added outcome. Previously unencodable coordinator domain values now
have a route matching the existing wire contract. The old negative test that
changed `TRANSFER / UNAUTHORIZED_SUBJECT` to the managed route was incorrect:
both leaves own that code. Its retained mutation now selects `COORDINATOR`,
which has no such code. An exhaustive positive control covers every valid pair.

## Executed Python evidence

The 171-test focused suite passed, covering both leaves, the coordinator,
dormant supply, resource boundaries, wire records and regenerated parity
fixtures. New resource tests use actual 4,096/4,097-row states, direct leaf and
aggregate failure, accepted neighbors, exact retry, authorization/arithmetic
precedence, and a full burn that frees a row for a later issue. Byte-helper
controls use the real one-MiB boundary; the aggregate byte-growth control lowers
the threshold to the exact test pre-state size. It is not a real one-MiB
aggregate transition test.

The subsequent
[`test_asset_lane_canonical_byte_boundary_v2.py`](../../tests/core/test_asset_lane_canonical_byte_boundary_v2.py)
adds four actual aggregate transitions at the unchanged 1,048,576-byte limit.
An independent row-size calculation includes quote/backslash escaping, array
separators and decimal digits; the fixture checks its predicted size against
the canonical encoder before calling the transition. Both a new owner and an
existing balance/supply changing from 9 to 10 accept at the exact limit and
reject one byte above it. The latter changes no row count. Each rejected
aggregate has an accepted managed-leaf candidate, identical pre/post roots and
no effects. All four tests passed. Raising or lowering the checker limit by one
byte in isolated mutation runs was detected by both scenario families.

Every route-owned enum value round-trips with exact enum identity and canonical
bytes. Actual runtime rejections also pass the wire codec, including binding,
projection and aggregate-size failures. Unknown routes/codes, mixed enums,
nonempty effects and authority/profile changes reject.

The broader critical quality gate passed 433 acceptance-boundary tests and 834
critical tests, including its coverage floors. Ruff passed on all changed Python
files. The configured Mypy gate passed its 25 source files. Widening Mypy to the
nine changed source modules reported 82 diagnostics, compared with 83 on their
pre-change versions; no new diagnostic was introduced. That wider check remains
a failing gate. The production-boundary audit passed its declared checks; the
permissionless assurance status still reports unqualified environments and
unmounted paths. None of those counts establishes deployment completeness.

Daybreak's independent review accepted the nine pinned Python sources within
scope after checking route ownership, narrow catch placement, guard order,
historical wire bytes and Python callers. Model review remains advisory.

## Executed Rust evidence

The complete standalone ABI V2 crate suite passed **92 tests**, with no failures
or ignored tests, using Rust 1.87.0, locked offline dependencies and a fresh
dedicated target directory. It includes actual 4,096/4,097-row leaf and aggregate
controls, accepted neighbors, burn/issue recovery, guard precedence, exact
no-effect outcomes and wire round trips. Existing shared Python/Rust golden
vectors still agree on canonical bytes, roots and results. The new resource
boundary histories are separately exercised in both languages; they do not
constitute universal implementation refinement.

The later real-byte controls in
[`asset_lane_resource_rejection.rs`](../../zk/global_settlement_abi_v2/tests/asset_lane_resource_rejection.rs)
add two tests, each with exact-limit and one-byte-over subcases. They exercise
the same escaped-owner insertion and funded 9-to-10 digit growth at the literal
1,048,576-byte limit. The managed leaf accepts before the aggregate either
accepts with the complete expected canonical state or returns a coordinator-owned
no-op rejection. Input occurrence identity and unchanged pre-state bytes/roots
are checked. The entire changed test target passed all ten tests in root's
isolated replay. Independent Daybreak source review accepted the scoped tests.
No Rust production source or fixture changed for this addition; the earlier
92-test full-crate run remains evidence for the preceding checkpoint.

The Rust implementation uses the distinct `AbiErrorV2::StateResourceLimit`
variant only for asset-state count, row and byte ceilings. Consumed-object and
occurrence bounds keep their existing error category. The three POST admission
sites catch only this variant. Other errors propagate. Global refinement treats
this asset-lane error as `INTERNAL_CONTRACT_DRIFT`, including a constructed
instance with a misleading global-field label. Independent Daybreak review
accepted the pinned runtime and reviewed test changes within this scope.

The full suite exposed an inherited invalid positive control: its all-lane
fixture sorted effect writes by Rust enum declaration order, although the wire
contract requires lexical lane names. The failure was reproduced at the
unchanged parent. Separate test-only commit `d688b9a9b` corrects construction and
retains declaration order as an exact `InvalidOrder("lane writes")` negative
control. All ten global-refinement tests passed against unchanged production
sources with that test repair.

```bash
cargo +1.87.0 test --locked --offline \
  --manifest-path zk/global_settlement_abi_v2/Cargo.toml --no-fail-fast
cargo +1.87.0 clippy --locked --offline \
  --manifest-path zk/global_settlement_abi_v2/Cargo.toml --all-targets -- -D warnings
```

The full Clippy gate remains failing: the unchanged
`GlobalEconomicStateEffectRefinementV2::validate_wire_observables` has eight
arguments and triggers `clippy::too_many_arguments`. No lint was suppressed.
Rust formatting and whitespace checks pass on the changed files. Build targets
must stay separate for different source copies: sharing one between the
baseline and candidate produced stale-library compiler diagnostics, so final
qualification used a fresh target dedicated to the integration subject.

## Regeneration and remaining checks

The two changed source-bound fixtures were regenerated with their existing
commands:

```bash
python3 -m tools.render_global_settlement_abi_v2_asset_lane_coordinator_golden \
  --write tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json
python3 -m tools.render_global_settlement_abi_v2_managed_asset_golden \
  --write tests/data/global_settlement_abi_v2_managed_asset_golden.json
```

Only source hashes and rejection-code registries changed. Existing accepted and
rejected vectors were compared with the parent and remained equal. The wire
fixture required no regeneration.

No full Lake, Kani, ESSO or RISC0 guest/proving build was run for this repair.
Changed guest dependencies require source/image
requalification before any new receipt or release claim. The existing
claims-registry failure for the missing derivatives authorization matrix remains
an independent integration blocker.

The [shared-state proof checkpoint](ZENODEX_SHARED_ASSET_LIFECYCLE_20260908.md)
proves an arithmetic slice. Its selected-state models lack finite row counts,
canonical-byte lengths and this resource outcome. The later
[recomposition](ZENODEX_ASSET_LANE_FINITE_RECOMPOSITION_20260908.md) and
[row-growth](ZENODEX_ASSET_LANE_ROW_GROWTH_20260908.md) checkpoints prove those
finite table/count relations, while complete resource-aware outcomes remain open.

Replaying `tests/formal/test_lean_managed_asset_runtime_parity_v2.py` against
the resource repair produced 170 passing tests and two failures: its old scalar
model omits `STATE_RESOURCE_LIMIT` from the enum and scenario table. The source
pin and enum checks in `tests/formal/test_lean_asset_lane_refinement_v2.py` also
fail. These failures remain visible pending a concrete finite-state outcome
extension. Refreshing source hashes or excluding a reachable code would not
establish that extension. Resource-aware mixed traces, full runtime refinement
and publication mediation remain required before formal-core or whole-value-safety
completion.
