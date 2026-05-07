# Zeno Oracle Signed Report V1

Status: first public local verifier format for signed Oracle report submissions.

This document describes the narrow signed-report submission shell currently
accepted by:

```text
python3 tools/zenodex_oracle_signed_report.py verify <submission>
```

The format uses the same BLS dependency family already present in the repo for
intent signatures. It is not yet a live reporter registry or network relay. It
is the first replayable object that binds a reporter key to a report payload,
sequence number, previous report ID, and content-addressed submission.

## Submission Shape

```json
{
  "schema": "zenodex.oracle.signed_report_submission.v1",
  "submission_id": "sha256:...",
  "chain_id": "zenodex.oracle.local",
  "reporter_id": "reporter.sample",
  "reporter_pubkey": "0x...",
  "reports": []
}
```

Allowed top-level fields are exactly:

- `schema`
- `submission_id`
- `chain_id`
- `reporter_id`
- `reporter_pubkey`
- `reports`

Unknown fields reject. Local signed-report files above `500_000` bytes are
treated as `inconclusive` before JSON parsing.

The submission ID is content-addressed:

```text
submission_id := sha256(canonical_json(submission without submission_id))
```

Plain English: the submission ID commits to the reporter, chain, public key,
and all included reports.

## Report Shape

Each report object has exactly these fields:

```json
{
  "schema": "zenodex.oracle.signed_report.v1",
  "report_id": "sha256:...",
  "payload_hash": "sha256:...",
  "query_id": "sha256:...",
  "source_id": "source.dex.pool.local",
  "value_e8": 100000000,
  "observed_epoch": 100,
  "sequence": 0,
  "previous_report_id": null,
  "signature": "0x..."
}
```

Every report ID is content-addressed:

```text
report_id := sha256(canonical_json(report without report_id))
```

Plain English: the report ID commits to the report payload hash, value, source,
sequence, previous-link field, and signature.

## Signing Payload

The reporter signs a canonical payload:

```json
{
  "schema": "zenodex.oracle.signed_report_payload.v1",
  "chain_id": "zenodex.oracle.local",
  "reporter_id": "reporter.sample",
  "reporter_pubkey": "0x...",
  "query_id": "sha256:...",
  "source_id": "source.dex.pool.local",
  "value_e8": 100000000,
  "observed_epoch": 100,
  "sequence": 0,
  "previous_report_id": null
}
```

The payload hash is:

```text
payload_hash := sha256(canonical_json(payload))
```

The BLS message is:

```text
message_hash := sha256(domain_sep("oracle_report_sig:" + chain_id) || canonical_json(payload))
```

Plain English: the signature is not over a loose price number. It is over the
chain, reporter identity, reporter public key, query, source, value, observed
epoch, sequence, and previous report link.

## Replay And Sequence Rules

Within one submission, acceptance requires:

```text
reports != []
sequence_i = i
previous_report_id_0 = null
previous_report_id_i = report_id_{i-1} for i > 0
distinct(report_id)
distinct(sequence)
```

Plain English: the submission is a contiguous reporter-local report chain. A
report cannot skip a sequence number, point at the wrong predecessor, duplicate
another report ID, or pretend a first report has a predecessor.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.signed_report_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "submission_id": "sha256:...",
  "reporter_id": "reporter.sample",
  "reporter_pubkey": "0x...",
  "chain_id": "zenodex.oracle.local",
  "report_count": 2,
  "first_sequence": 0,
  "last_sequence": 1,
  "last_report_id": "sha256:...",
  "errors": []
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | Every report payload, signature, content hash, and sequence link replayed cleanly. |
| `rejected` | The submission parsed, but at least one policy check failed. |
| `inconclusive` | The verifier could not load the file or the signature backend is unavailable. |

## Replay Commands

Generate and verify a minimal accepted signed-report submission:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_signed_report.py sample --output "$tmp/signed-report.json"
python3 tools/zenodex_oracle_signed_report.py verify "$tmp/signed-report.json"
rm -rf "$tmp"
```

Run deterministic signed-report chaos replay:

```bash
python3 tools/zenodex_oracle_signed_report_chaos.py
```

The current signed-report chaos lane covers `18` named submission-hash,
payload-hash, signature, report-ID, sequence, previous-link, duplicate,
hidden-field, schema, key-format, type-confusion, and malformed-report disaster
shapes. Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- report values are true;
- the reporter is honest;
- the reporter is registered or bonded;
- the source is correct;
- a production Zeno Oracle network is live.

The claim is narrower: accepted signed-report submissions bind reporter keys to
exact report payloads and reject signature, hash, replay-chain, and schema
mutations before reports can be promoted into aggregate receipts.
