# Zeno Oracle Admitted Median3 Aggregate V1

This document describes the narrow admitted-median3 shell currently accepted
by the local verifier:

```bash
python3 tools/zenodex_oracle_admitted_median3.py verify <aggregate>
```

The admitted-median3 verifier is the first bridge from report admission into
aggregation. It does not replace the plain median3 arithmetic verifier; it
adds the stronger requirement that each aggregate input is the output of an
accepted report-admission bundle.

## Aggregate Shape

```json
{
  "schema": "zenodex.oracle.admitted_median3_aggregate.v1",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "current_epoch": 104,
  "max_staleness_epochs": 10,
  "max_deviation_bps": 200,
  "min_distinct_sources": 3,
  "report_admissions": [
    { "schema": "zenodex.oracle.report_admission.v1" },
    { "schema": "zenodex.oracle.report_admission.v1" },
    { "schema": "zenodex.oracle.report_admission.v1" }
  ],
  "aggregate": {
    "value_e8": 100000000,
    "confidence_e8": 1000000,
    "deviation_bps": 100,
    "observed_epoch": 102,
    "report_count": 3
  }
}
```

Unknown fields reject. Local aggregate files above `2_000_000` bytes are
inconclusive rather than accepted.

## Content Binding

The aggregate ID is content-addressed:

```text
aggregate_id := sha256(canonical_json(aggregate without aggregate_id))
```

Plain English: the aggregate ID commits to the query policy fields, all three
report-admission bundles, and the computed median result. If a nested
admission, policy value, or aggregate output changes, the ID must change too.

## Acceptance Contract

The verifier accepts only when all of these checks hold:

```text
AdmittedMedian3Accepted
  -> Exactly3Admissions
  and EveryAdmissionAccepted
  and OneReportPerAdmission
  and SameQuery
  and SameFreshnessWindow
  and DistinctReporters
  and DistinctReporterKeys
  and DistinctSources
  and ExactMedian
  and ExactConfidence
  and ExactDeviation
  and DeviationWithinPolicy
```

Plain English: median3 can no longer aggregate a loose report object in this
path. Each input must first pass signature, lifecycle, source-diversity, and
freshness checks through report admission, and then the aggregate must compute
the exact median/confidence/deviation from those admitted reports.

### Reporter independence is a property of the signing key

`DistinctReporters` checks the self-chosen `reporter_id` label, which is not a
security boundary on its own: a single party can register several `reporter_id`
labels. `DistinctReporterKeys` is the load-bearing Sybil defence. Each admitted
report carries the BLS `reporter_pubkey` whose signature `report_admission`
already verified over the exact payload, and the verifier rejects the aggregate
with `duplicate_reporter_pubkey` if any two of the three inputs are signed by
the same key — even when their `reporter_id` strings and sources differ.

The comparison is over the **canonical** pubkey encoding (prefix-stripped,
lower-cased). The signed-report verifier accepts the same key with an optional
`0x` prefix and in either hex case, so a raw-string comparison would let one key
masquerade as two reporters by simply re-encoding its pubkey; canonicalizing
before comparison closes that bypass.

This keeps the median_3 quorum honest about its own claim: the median of three
inputs is only meaningful if three *distinct signing keys* attest it. Without
this check, one key could supply two (or all three) of the median inputs under
different labels and fully control the result, which would silently break the
"no single signer can move the price" property that the L2 trust posture
(`docs/ORACLE_TRUST_POSTURE.md`) relies on. This is still trust-MINIMIZED, not
trustless: distinct keys are not proof the operators behind them are
independent — see the unchanged non-claims below.

The V1 shell intentionally requires one admitted report per admission bundle.
That keeps the first verifier small and avoids hidden selection rules inside a
multi-report admission.

## Output Receipt

Successful verification returns:

```json
{
  "schema": "zenodex.oracle.admitted_median3_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "value_e8": 100000000,
  "confidence_e8": 1000000,
  "deviation_bps": 100,
  "observed_epoch": 102,
  "report_count": 3,
  "admission_count": 3,
  "distinct_reporter_count": 3,
  "distinct_reporter_pubkey_count": 3,
  "distinct_source_count": 3,
  "errors": []
}
```

The `not_claimed` list remains part of the receipt. In particular, this shell
does not claim that the market price is true or that reporters and sources are
honest. It only verifies the declared admission and aggregation contract.

## Status Values

| Status | Meaning |
| --- | --- |
| `accepted` | The aggregate parsed and every admission/arithmetic check passed. |
| `rejected` | The aggregate parsed, but at least one admission or aggregate check failed. |
| `inconclusive` | The verifier could not load or parse the aggregate safely. |

## Replay

Generate and verify a minimal accepted admitted median3 aggregate:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_admitted_median3.py sample --output "$tmp/admitted-median3.json"
python3 tools/zenodex_oracle_admitted_median3.py verify "$tmp/admitted-median3.json"
```

Run deterministic admitted-median3 chaos replay:

```bash
python3 tools/zenodex_oracle_admitted_median3_chaos.py
```

The current admitted-median3 chaos lane covers `22` named aggregate-hash,
median, confidence, deviation, observed-epoch, admission-count,
admission-rejection, duplicate-admission, duplicate-reporter,
duplicate-reporter-pubkey (one signing key masquerading as two reporters, both
in the same and a re-encoded hex form), duplicate-source, query mismatch,
freshness-window mismatch, multi-report admission, deviation policy,
evidence-floor, hidden-field, and schema-downgrade disaster shapes. Every case
rejects.

## Non-Claims

This V1 shell does not yet claim:

- the production Oracle network is live;
- reporter registration is decentralized;
- source independence is true in the real world beyond the declared source
  classification;
- the median is the true market price;
- every future aggregate cardinality is supported.
