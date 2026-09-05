# ZenoDEX critical algorithm optimization review

Research subject: `dfdbc07e924a04053289532c776dd87463fd64fd`.
Reviewed implementation: `be6969dc0439514a8186bb6b40cd198f1c97d01d`.
Researcher: Astra Max. Implementation: Luna Max. Integration and final disposition:
parent agent, with a separate independent review of the implemented change.

## Outcome and scope

The best measured benefit relative to implementation and requalification effort
was an exact-string ASCII shortcut in canonical validation. It is implemented,
reviewed and committed. The final local custody benchmark used 21.62–23.81% less
elapsed time, with identical canonical bytes at every measured size.

The survey covered clearing/order refinement, AMM routing and arithmetic,
accounting/projection/encoding, monetary fee claims, perps matching, JMT queries,
journal recovery, cryptographic/proof preparation and the inspected formal test
workload. Oracle, strategy, farm and auction paths did not yield a measured
optimization recommendation. Deployment workload frequencies remain UNKNOWN.
Global optimality and exhaustiveness of this search remain unproved.

Ranking considers measured cost, expected workload, implementation size and the
cost of preserving arithmetic, authority, rejection and release contracts. A
large synthetic speedup alone does not establish product-wide benefit. All
unimplemented measurements below are exploratory scout results; the encoding
result has a retained reproduction tool and source-bound output.

## Ranked candidates and integrator decisions

| Rank | Candidate and source | Evidence and payoff | Disposition |
|---:|---|---|---|
| 1 | Exact built-in ASCII shortcut, `src/state/canonical.py::_reject_surrogates` | Measured 21.62–23.81% less elapsed time in Python custody composition; original non-ASCII/subclass loop retained. | **IMPLEMENTED / TESTED** at `be6969dc0`. |
| 2 | Reuse stake/debt maps during bulk claims, `src/integration/zusd_monetary_bridge.py::_fee_stake_claimable_e8`, `_require_fee_routes_transport_exact`, `_state_invariant_error` | Two full map copies per claimant create `2*S²` copied entries. One owned snapshot reduces these to `2*S`. Scout guard-only speedup: 4.12x at 256, 43.17x at 4,096 stakeholders. | **NEXT CANDIDATE**. Ownership, lazy access and exact rejection contract must be retained. No code change approved beyond that bounded packet. |
| 3 | Reuse second-hop exact-out quotes, `src/core/routing_exact_out.py::_two_hop_exact_out_quote` | 64-by-64 synthetic CPMM hub: 125.187 to 79.831 ms; 8,192 to 4,160 quote calls; equal route objects. | **CONDITIONAL** on pure quote dependencies and stable pool values. Generic caller-supplied callbacks and mutable `PoolState` prevent a blanket cache rewrite. |
| 4 | First-wins accepted-fill intent index, `src/core/batch_clearing_compute.py::_process_pool_intent_phase` | A linear `next(...)` search per accepted fill gives quadratic lookup work. Indexing can remove that component. Total gain unmeasured. | **BENCHMARK FIRST**. Preserve duplicate-ID winner, missing-ID exception and clearing-callback timing. |
| 5 | Touched-key scratch state across pool clearing, `batch_clearing_compute.py` and `batch_clearing_single_pool.py::clear_batch_single_pool_with_factories` under `src/core/` | Global tables copied into local state and again per pool; possible reduction of `P*N` copying. Unmeasured. | **DEFER** pending cross-pool spending, LP metadata, alias isolation and rejection-purity refinement. |
| 6 | Compute identical roots once within an owned calculation, `src/core/asset_lane_projection_v1.py`, `asset_lane_coordinator_v1.py`, `global_settlement_types_v1.py` | Parent profile recorded 48 global encodings and nine private-port root calls in the custody workload. Incremental payoff after rank 1 unmeasured. | **PROFILE AGAIN BEFORE EDITING**. Keep constructor/verifier validation; no object-identity authority caches. Custody-complete coordinator remains unmounted. |
| 7 | Authenticated history checkpoints, `src/integration/global_economic_epoch_journal_v1.py::_validate_store_v1` | Repeated complete-history decoding/schema/integrity checks scale with retained bytes; cumulative append work can grow quadratically before configured limits. Unmeasured. | **ARCHITECTURE WORK** requiring rollback, corruption, concurrency, recovery and committed-ancestry proofs. Current checks stay intact. |
| 8 | Request-local parsed curve parameters, `src/core/amm_dispatch.py` | Each non-CPMM quote parses parameters. Reuse could remove repeated parsing; curve mix and benefit unknown. | **BENCHMARK FIRST** with owned values, original committed bytes and malformed-parameter rejection preserved. |
| 9 | Exact integer gross-from-net inversion, `_min_gross_for_net` in `src/kernels/python/{cubic_sum,sum_boost,quartic_blend,quintic_blend}_swap_v1.py` | Ceiling expression followed by adjustment loops; possible arithmetic simplification. Loop cost and total gain unmeasured. | **LOW-PRIORITY MATH REVIEW**. Prove minimality, bounds and rounding before changing generated/native counterparts. |
| 10 | Reuse unchanged simulation prefixes, `src/core/batch_clearing_mci_ordering.py` | Insertion and pair-swap searches repeatedly evaluate orders. Prefix snapshots may avoid repeated transitions. Unmeasured. | **R&D** with exact small-permutation oracles, reserve-dependent effects, objective/tie preservation and unchanged search bounds. |
| 11 | Prepared JMT tree for repeated queries, `src/state/jmt.py` and `src/state/app_root.py` | Root and proof functions rebuild normalized trees. Reuse for a fixed entry set may help multi-query workloads. Unmeasured. | **BENCHMARK FIRST**. Require deeply owned entries and identical root/proof bytes; small lane-root trees may offer little gain. |
| 12 | Incremental min-fill rerationing, `src/core/perp_np_matching.py::_apply_min_fill_revocation` | Recomputes largest-remainder allocation until revocations stabilize. Cascades may offer an optimization target. Unmeasured. | **DEFER**. Explicitly experimental and unmounted from consensus; retain simultaneous revocations, canonical ties, net zero and overflow rejection. |
| 13 | Reuse proof/receipt preparation, including `zk/asset_lane_custody_coordinator_risc0/shared/src/lib.rs` | Native custody and route prepared values already retain journals. Remaining duplication needs measurement. | **NO BROAD REWRITE**. No proof-generation savings measured; guest changes require new images and genuine receipts. |

The integrator checked the central source claims: repeated zUSD copies, per-fill
linear lookup, per-pool scratch copies, repeated curve parsing, JMT rebuilding,
order reevaluation, monotone min-fill rerationing, and full-history validation.
These checks establish current code structure. They do not establish the
correctness or performance of the proposed replacements.

## Measurements and qualification

| Workload | Size | Baseline median ms | Candidate median ms | Status |
|---|---:|---:|---:|---|
| Custody transition + coordinator + output encoding | 0 rows | 8.264039 | 6.296242 | Retained parent run, five interleaved samples per variant |
| Same | 256 rows | 88.068837 | 69.031670 | Same |
| Same | 4,096 rows | 1285.651796 | 1004.773228 | Same |
| zUSD whole-transport fee guard | 256 stakeholders | 0.8800 | 0.2134 | Exploratory scout prototype; no full monetary-commit claim |
| Same | 4,096 stakeholders | 143.0179 | 3.3133 | Same |
| Two-hop exact-out CPMM hub | 64 first / 64 second pools | 125.187 | 79.831 | Exploratory scout prototype; stable unique-ID fixture only |

The retained encoding implementation evidence is
[`ZENODEX_CANONICAL_ASCII_IMPLEMENTATION_EVIDENCE_20260905.md`](ZENODEX_CANONICAL_ASCII_IMPLEMENTATION_EVIDENCE_20260905.md).
Its companion
[`ZENODEX_CANONICAL_ASCII_BENCHMARK_20260905.json`](ZENODEX_CANONICAL_ASCII_BENCHMARK_20260905.json)
contains all samples, input/output hashes and an unchanged 138-module repository
Python source closure. Reproduce with:

```bash
python3 tools/benchmark_canonical_surrogate_validation_v1.py --repeats 5
```

The implementation passed 706 selected state, signing, verifier, custody and
ledger checks, including a separately rerun local-socket test; 14 production
boundary checks; Ruff; combined mypy; and unchanged custody golden bytes.
The Unicode differential scan covers all 1,114,112 code points, plus structured
and subclass cases. Two semantic mutants are distinguished. Independent review
confirmed semantic preservation and later verified the benchmark provenance and
CLI-bound repairs. These are scoped tests and review, not formal-core completion.

The full critical quality script stopped because `pytest_cov` is missing. Its
coverage checks remain unrun. Historical recompute-batch source pins were already
stale on the research subject and were preserved. No historical receipt/profile
was repinned and no live migration, authority activation or Runpod work occurred.
The documentation claims-registry check also remains blocked: claim 123 refers
to `tools/check_derivatives_authorization_matrix.py`, which is absent from both
the research baseline tree and the current checkout. The registry was unchanged.

## Bounded follow-up packets

### P2: bulk zUSD claim calculation

Owned production surface: only the private claim helper and its two bulk callers
in `src/integration/zusd_monetary_bridge.py`, with focused tests and a reproducible
guard benchmark. Keep single-account helper behavior available.

Invariant: for positive shares `s`, accumulator `a`, debt `d` and the existing
scale `F`, claim equals `max(0, floor(s*a/F) - d)`; nonpositive shares return zero.
Routed fee integrality, exact claimant/pool equality and all authorization checks
must retain their current ordering. No fee rates, policy constants or rounding
ownership may change.

Map reuse must occur inside the existing owned snapshot boundary. Preserve the
original map-copy/lookup/conversion failure precedence. Empty claimant lists must
not gain eager debt/accumulator access; zero shares must not gain accumulator
conversion. Keep claimant sort order, duplicate/alias behavior and input state
unchanged. Do not generalize an internal optimization to arbitrary stateful
Mappings without a separate contract.

Acceptance: frozen pre-change outcome oracle and independent integer formula;
empty/one/max-fixture populations; zero and positive shares; exact and fractional
E8 fees; debt above accrual; malformed fields; partial/repeated claims, activation
and unstaking histories; exact state/error/no-effect parity. Distinguish mutants
that forgive dust, misattribute debt or access the accumulator eagerly. Require
at least 4x improvement at 4,096 stakeholders and report a representative full
monetary-path measurement separately. The fixture size is a benchmark bound,
not a newly selected product limit.

### P3: stable-request exact-out quote reuse

Resolve purity and snapshot ownership first. Restrict initial changes to the
default proven-pure quote path if the generic dependency contract remains open.
Use lazy request-local entries indexed by pool tuple position, direction and
amount, including failed quotes; preserve iteration order and canonical ties.
Pool IDs and object identity are insufficient keys for generic inputs.

Acceptance must compare complete routes and exact outcomes over small exhaustive
graphs, duplicate IDs, shared middle assets, ties, unavailable paths, all admitted
curves and malformed boundaries. Stateful callback and mutation controls must
demonstrate that unsupported cache assumptions cannot silently change behavior.
No production speedup or permission to remove verification follows from the
scout's synthetic hub result.

## Directions without sufficient payoff evidence

Sparse transfer-table merge competes with near-sorted Python sorting while
encoding dominates the inspected workload. Auction clearing already sorts price
buckets. Oracle, strategy and farm workload distributions need measurements.
BLS batching and sealed-executable reuse affect sensitive verification contracts.
The inspected custody formal test already compiles dependencies by module.
None of these observations justifies a broad rewrite or a reduced safety gate.

Performance work remains subordinate to the V3 accounting, authorization,
publication and recovery contracts. Full formal/runtime refinement, lane
qualification and production promotion remain open.
