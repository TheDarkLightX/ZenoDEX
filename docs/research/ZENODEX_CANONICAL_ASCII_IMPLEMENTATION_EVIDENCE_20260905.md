# Canonical ASCII fast-path implementation evidence

Baseline subject: `dfdbc07e924a04053289532c776dd87463fd64fd`.
Status: implemented and locally tested; no release promotion.

## Change and review

`src/state/canonical.py::_reject_surrogates` returns immediately only when
`type(s) is str and s.isascii()`. Every character in that case is below 128 and
therefore outside the surrogate interval `[0xD800, 0xDFFF]`. The original loop
continues to handle non-ASCII values and subclasses. Validation order, canonical
JSON bytes, error types/messages, domain separation and root construction are
unchanged.

Astra Max identified and measured the candidate. The integrator reviewed its
source and prototype before delegating implementation to Luna Max. Independent
review found no semantic flaw in the two-line production change. It identified
missing benchmark dependency provenance and an unchecked fixture size limit;
both were corrected. Combined mypy checking additionally found a benchmark
callable-signature issue, which was corrected before retaining the final run.

The new differential suite retains the pre-change loop as a regression oracle.
It checks all 1,114,112 single Unicode code points, including exactly 2,048
surrogates, plus nested bytes/errors, seeded longer inputs, error precedence,
non-string inputs, and subclasses with overridden iterators or `isascii`.
Controls distinguish two semantic mutants: skipping validation and dropping the
exact-type guard. The frozen loop is a historical implementation oracle, not an
independently authored Unicode/JSON specification or a machine-checked proof.

## Reproduction and results

The retained benchmark is
[`ZENODEX_CANONICAL_ASCII_BENCHMARK_20260905.json`](ZENODEX_CANONICAL_ASCII_BENCHMARK_20260905.json).
It records interleaved baseline/candidate samples, input and output hashes,
Python version, encoder/oracle hashes and the loaded repository Python source
closure. All requested fixtures and both paths are warmed before freezing that
closure, which must remain unchanged through measurement.

The final five-sample run retained an unchanged 138-module source closure and
identical output bytes in every sample:

| Custody rows | Baseline median ms | Candidate median ms | Less elapsed time |
|---:|---:|---:|---:|
| 0 | 8.264039 | 6.296242 | 23.81% |
| 256 | 88.068837 | 69.031670 | 21.62% |
| 4,096 | 1285.651796 | 1004.773228 | 21.85% |

```bash
python3 tools/benchmark_canonical_surrogate_validation_v1.py --repeats 5 > docs/research/ZENODEX_CANONICAL_ASCII_BENCHMARK_20260905.json
python3 -m ruff check src/state/canonical.py tests/state/test_canonical_surrogate_validation_v1.py tools/benchmark_canonical_surrogate_validation_v1.py
python3 -m mypy src/state/canonical.py tests/state/test_canonical_surrogate_validation_v1.py tools/benchmark_canonical_surrogate_validation_v1.py
python3 tools/render_asset_lane_custody_coordinator_v1_golden.py --check
```

Ruff, combined mypy and unchanged custody golden bytes passed. The broader
consumer command below produced 705 passes and one sandbox failure at local
Unix-socket creation. Repeating that exact multiprocessing test with the socket
restriction lifted passed, for 706 successful checks across the same selection.

```bash
python3 -m pytest -q tests/state tests/core/test_asset_lane_custody_coordinator_golden_v1.py tests/core/test_asset_transfer_lane_module_custody_v1.py tests/core/test_dex_intent_auth_message.py tests/core/test_perp_submission_auth_message.py tests/core/test_sealed_bid_auction.py tests/core/test_settlement_normal_form.py tests/core/test_support_root.py tests/agents/test_intent_signer_signing.py tests/integration/test_intent_signatures.py tests/integration/test_proof_verifier.py tests/integration/test_proof_verifier_unit.py tests/integration/test_proof_verifier_fuzz.py tests/integration/test_recompute_batch_proof_verifier.py tests/integration/test_operations_parsing.py tests/integration/test_risc0_shared_fixture_equivalence.py tests/integration/test_zeno_ledger_determinism_golden.py tests/integration/test_zeno_ledger_chaos_encoding.py tests/integration/test_zeno_ledger_chaos_byteorder.py tests/integration/test_zeno_ledger_chaos_protocol.py tests/integration/test_zeno_ledger_chaos_multiprocess.py
python3 -m pytest -q tests/integration/test_zeno_ledger_chaos_multiprocess.py::TestMultiprocessingStartMethods::test_forkserver_child_produces_same_hash
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
bash tools/run_critical_quality_gate.sh
```

The production-boundary check passed its 14 checks. Permissionless status ran;
its historical assurance snapshot and missing ESSO/Tau environments do not
establish current release readiness. The critical quality script stopped before
its checks because `pytest_cov` is unavailable. Its coverage gate remains unrun.
No tests, manifests or thresholds were weakened to bypass that prerequisite.

## Scope and remaining obligations

These are local Python timings for custody module transition, single-lane
composition and canonical output encoding at 0, 256 and 4,096 custody rows.
They establish no full-system throughput, Rust/guest acceleration, receipt
qualification, publication authority or whole-program safety claim. No Runpod,
new guest build, full Lean build, live migration or activation was performed.

The historical recompute-batch assurance manifest already pins a different
`canonical.py` hash on the baseline subject, and its named checker/gate scripts
are absent there. It remains unchanged and is not used as current evidence.
Historical receipts and profiles retain their original subjects. Full V3 formal
core and production qualification remain open.
