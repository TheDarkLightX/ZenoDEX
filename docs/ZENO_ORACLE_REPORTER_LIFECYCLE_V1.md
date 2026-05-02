# Zeno Oracle Reporter Lifecycle V1

Status: first public local verifier format for reporter lifecycle traces.

The reporter lifecycle shell verifies that a permissionless reporter cannot
skip the basic economic sequence: register, post enough bond, submit reports,
face disputes, be slashed only through an open dispute, resolve disputes, and
withdraw only after becoming inactive and clear of open disputes.

The current local verifier is:

```text
python3 tools/zenodex_oracle_reporter_lifecycle.py verify <trace>
```

## Trace Shape

```json
{
  "schema": "zenodex.oracle.reporter_lifecycle.v1",
  "reporter_id": "reporter.sample",
  "required_bond": 100,
  "events": []
}
```

Allowed top-level fields are exactly:

- `schema`
- `reporter_id`
- `required_bond`
- `events`

The verifier bounds traces to `64` events and local files to `250_000` bytes.

## Event Types

The first shell supports:

| Event | Required Fields |
| --- | --- |
| `register` | `type`, `epoch` |
| `deposit_bond` | `type`, `epoch`, `amount` |
| `submit_report` | `type`, `epoch`, `report_id`, `query_id`, `value_hash` |
| `open_dispute` | `type`, `epoch`, `report_id`, `dispute_id`, `dispute_bond` |
| `slash` | `type`, `epoch`, `dispute_id`, `amount` |
| `resolve_dispute` | `type`, `epoch`, `dispute_id`, `outcome` |
| `unregister` | `type`, `epoch` |
| `withdraw_bond` | `type`, `epoch`, `amount` |

Unknown event fields reject. Event epochs must be monotone nondecreasing.

## Safety Laws

```text
ReportAccepted -> ReporterActive and BondAvailable >= RequiredBond
SlashAccepted -> OpenDispute and SlashAmount <= BondAvailable
WithdrawAccepted -> not ReporterActive and no OpenDispute and Amount <= BondAvailable
```

Plain English: the reporter must be active and sufficiently bonded before
reporting, slashes must come through an open dispute and fit inside the bond,
and withdrawals cannot occur while active or while a dispute remains open.

## Replay Commands

Generate and verify a sample lifecycle:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_reporter_lifecycle.py sample --output "$tmp/lifecycle.json"
python3 tools/zenodex_oracle_reporter_lifecycle.py verify "$tmp/lifecycle.json"
rm -rf "$tmp"
```

Run deterministic lifecycle chaos replay:

```bash
python3 tools/zenodex_oracle_reporter_lifecycle_chaos.py
```

The current lifecycle chaos lane covers `20` named sequence, bond, dispute,
slash, withdrawal, epoch, hidden-field, and event-count disaster shapes. Details
are tracked in [ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- a live reporter registry exists;
- reporter signatures are verified;
- report values are true;
- disputes are subjectively correct;
- governance and appeals are finalized;
- token settlement is wired to runtime balances.

The claim is narrower: this first lifecycle shell rejects reporter traces that
try to report without active bond, slash without dispute, withdraw while active,
withdraw during open disputes, or overdraw the reporter bond.
