# Zeno Oracle Report Admission V1

Status: first public local verifier format for admitting signed reports into the
Oracle aggregation pipeline.

This document describes the narrow report-admission shell currently accepted
by:

```text
python3 tools/zenodex_oracle_report_admission.py verify <admission>
```

The admission verifier is a bridge. It does not replace the signed-report,
reporter-lifecycle, or source-diversity verifiers. It requires all three to
pass, then checks that their facts agree before a report can be treated as
eligible for aggregation.

## Admission Shape

```json
{
  "schema": "zenodex.oracle.report_admission.v1",
  "admission_id": "sha256:...",
  "current_epoch": 104,
  "max_staleness_epochs": 10,
  "signed_submission": {},
  "reporter_lifecycle": {},
  "source_diversity": {}
}
```

Allowed top-level fields are exactly:

- `schema`
- `admission_id`
- `current_epoch`
- `max_staleness_epochs`
- `signed_submission`
- `reporter_lifecycle`
- `source_diversity`

Unknown fields reject. Local admission files above `1_000_000` bytes are
treated as `inconclusive` before JSON parsing.

The admission ID is content-addressed:

```text
admission_id := sha256(canonical_json(admission without admission_id))
```

Plain English: the admission ID commits to the signed submission, lifecycle
trace, source-diversity receipt, freshness policy, and current epoch.

## Bridge Rule

Acceptance requires:

```text
SignedSubmissionAccepted
and ReporterLifecycleAccepted
and SourceDiversityAccepted
and reporter_id_signed = reporter_id_lifecycle
and report_id_signed = report_id_submitted
and query_id_signed = query_id_submitted = query_id_source_diversity
and payload_hash_signed = value_hash_submitted
and source_id_signed in source_diversity_sources
```

Plain English: a report is admitted only when the signature receipt, lifecycle
trace, and source policy all describe the same reporter, same report IDs, same
query, same signed payload hash, and allowed source.

## Freshness Rule

For every admitted report:

```text
observed_epoch <= current_epoch
current_epoch - observed_epoch <= max_staleness_epochs
```

Plain English: the bridge also rejects future reports and stale reports before
they can be promoted into an aggregate.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.report_admission_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "admission_id": "sha256:...",
  "reporter_id": "reporter.sample",
  "query_id": "sha256:...",
  "admitted_report_count": 2,
  "current_epoch": 104,
  "max_staleness_epochs": 10,
  "admitted_reports": [
    {
      "report_id": "sha256:...",
      "reporter_id": "reporter.sample",
      "reporter_pubkey": "0x...",
      "query_id": "sha256:...",
      "source_id": "source.dex.pool.local",
      "source_set_id": "sha256:...",
      "payload_hash": "sha256:...",
      "value_e8": 100000000,
      "observed_epoch": 100
    }
  ],
  "errors": []
}
```

Each admitted report carries the signature-verified `reporter_pubkey`. Downstream
aggregation (`zenodex.oracle.admitted_median3`) uses it to require three distinct
*signing keys*, so one key cannot supply two median inputs under different
`reporter_id` labels.

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | Signed submission, lifecycle, source diversity, and cross-receipt bindings replayed cleanly. |
| `rejected` | The admission parsed, but at least one bridge or subreceipt check failed. |
| `inconclusive` | The verifier could not load or parse the admission safely. |

## Replay Commands

Generate and verify a minimal accepted report admission:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_report_admission.py sample --output "$tmp/report-admission.json"
python3 tools/zenodex_oracle_report_admission.py verify "$tmp/report-admission.json"
rm -rf "$tmp"
```

Run deterministic report-admission chaos replay:

```bash
python3 tools/zenodex_oracle_report_admission_chaos.py
```

The current report-admission chaos lane covers `18` named admission-hash,
signed-payload, reporter mismatch, missing submit, lifecycle query/value
mismatch, extra submit, source mismatch, source-policy query mismatch,
future/stale report, lifecycle rejection, source-diversity rejection,
hidden-field, schema, type-confusion, and malformed-subreceipt disaster shapes.
Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- report values are true;
- reporters are honest;
- sources are honest;
- disputes are subjectively correct;
- the production Oracle network is live.

The claim is narrower: a report cannot be promoted toward aggregation unless
the signed payload, reporter lifecycle event, and source-diversity policy bind
to the same report facts and pass freshness checks.
