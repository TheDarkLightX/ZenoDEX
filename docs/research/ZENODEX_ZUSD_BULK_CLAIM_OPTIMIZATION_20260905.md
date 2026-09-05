# zUSD bulk claim calculation: reviewed candidate held for source admission

This candidate is scoped to `_require_fee_routes_transport_exact` in
`src/integration/zusd_monetary_bridge.py`, based on integration HEAD
`04f0d32b6b6679aa23da645263ec6575f7872c4e`. It changes the implementation of
claim aggregation, with no fee rounding, allocation, policy or wire change.
The implementation, tests and tool are retained in
`ZENODEX_ZUSD_BULK_CLAIM_CANDIDATE_20260905.patch`. The integration bridge was
restored byte-for-byte after verification. No speedup is active in this subject;
W07/W09 and this W13 integration subtask remain incomplete.

For exact dictionaries with exact string field/account keys, exact integer
amounts, and an exact integer accumulator, the bulk helper copies stake/debt
maps once, then evaluates the existing claim formula. Generic mappings,
subclasses, custom conversions and field-name hooks retain the original
per-claimant path. Nonpositive shares still return zero before debt subtraction;
an unused missing accumulator retains lazy behavior. The singleton helper's
signature and behavior are unchanged. `_state_invariant_error` remains on its
original loop and has no performance claim from this patch.

## Verification and review

Luna's initial implementation and Terra's repairs received repeated independent
Sol and parent review. Confirmed parity defects were retained before repair:
mutating accumulator conversions, map-access exception order, caller-injected
snapshot arguments, nonpositive shares, missing unused accumulator, and custom
outer dictionary keys. Exact fields include the dictionary's own keys; an exact
`dict` alone does not exclude equality hooks.

```bash
# Apply only in an isolated candidate checkout; the source-admission gate below
# deliberately blocks this patch on the currently accepted subject.
git apply --check docs/research/ZENODEX_ZUSD_BULK_CLAIM_CANDIDATE_20260905.patch
git apply docs/research/ZENODEX_ZUSD_BULK_CLAIM_CANDIDATE_20260905.patch
python3 -m pytest -q tests/integration/test_zusd_bulk_fee_claims_v1.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py
python3 -m ruff check src/integration/zusd_monetary_bridge.py tests/integration/test_zusd_bulk_fee_claims_v1.py tools/benchmark_zusd_bulk_fee_claims_v1.py
python3 -m mypy src/integration/zusd_monetary_bridge.py tests/integration/test_zusd_bulk_fee_claims_v1.py tools/benchmark_zusd_bulk_fee_claims_v1.py
python3 tools/benchmark_zusd_bulk_fee_claims_v1.py --repeats 7 --counts 0 1 256 4096 > docs/research/ZENODEX_ZUSD_BULK_CLAIM_BENCHMARK_20260905.json
```

Parent replay: **30 passed, 6 skipped**. The skipped wallet-UI cases remain
unexecuted; they do not qualify a client workflow. Ruff passed. Mypy reports
two existing clock-nullability errors at lines 1470/1477. A `--shadow-file`
comparison using the exact HEAD bridge reproduces the same errors, so mypy is
not reported green. The trust-surface scan and red-flag/design-metric triage ran;
the large inherited bridge remains a review hotspot. No broad refactor was made.

The seven-sample, interleaved benchmark checks identical outcomes against a
frozen pre-change guard before and throughout timing. Independent integer
expectations determine the synthetic fixture's claim pool.

| Claimants | Original median ms | Candidate median ms | Speedup |
| --- | --- | --- | --- |
| 0 | 0.006310 | 0.007140 | 0.88x |
| 1 | 0.008390 | 0.011990 | 0.70x |
| 256 | 0.933143 | 0.226470 | 4.12x |
| 4096 | 178.416825 | 3.325918 | 53.64x |

At 4096 equal-sized maps, logical copied-entry counts fall from `n + 2n²` to
`2n`. The tool labels its 4x threshold inapplicable at other sizes. These are
synthetic guard timings, not complete monetary-transaction throughput or a
production workload. Tiny inputs incur extra classification overhead.

## Exact subject and nonclaims

The following are the tested candidate bytes carried in the patch, rather than
the restored bridge and absent candidate test/tool in the integration tree.

| Artifact | SHA-256 |
| --- | --- |
| `src/integration/zusd_monetary_bridge.py` | `2d02415537acf959471221bba58790db977fdceec540401b498ac5721645a2e2` |
| `tests/integration/test_zusd_bulk_fee_claims_v1.py` | `3622b8104e093f67890dd68c6331a2d2ba5a49dd1d87d9bcae2d1eb2f25f1769` |
| `tools/benchmark_zusd_bulk_fee_claims_v1.py` | `faab1a8fde57c7e9ee2200691447365e1271c333c2e4fd88d7bf15d8e6dc7ad1` |

The benchmark JSON binds these source bytes and the pre-change Git subject.
Review accepted this bounded refactor after the retained negative controls
passed. This is implementation/test evidence, without a universal Python
refinement theorem, concurrent mutable-caller guarantee, lane-completion claim,
publication qualification or production promotion. No guest, full Mathlib,
remote proof or live activation ran.

## Integration hold

`python3 tools/check_production_boundary.py --json` rejected the candidate with
`WORKTREE_SOURCE_DRIFT` for the monetary bridge. Historical O-003B V3 binds its
exact Stage-A source and requires an artifact-only, added-file Stage-B commit.
Replacing hashes in that artifact cannot legitimately admit new source. The
benchmark also introduces a new import of the classified bridge, so resolving
only the byte pin would leave an unclassified discovery edge.

Independent source-admission review found no consumed generic successor API.
An explicit versioned classification and current-source restage is needed;
the active whole-program plan already selects V3 and does not grant source
admission. That larger work is deferred for this optional optimization.
Historical artifacts/checkers remain unchanged. The three-file patch was
reverse-checked, removed from the worktree, and forward-checked successfully.

Patch SHA-256:
`6be58fba17f934791c5729d7701d10bcc8ba612b0b15413471cf36260e3871e4`.

Empty context lines use Git-accepted bare newlines so the stored patch passes
repository whitespace checks. `git apply --check` verifies this representation;
no candidate source byte was changed by the context-only normalization.
