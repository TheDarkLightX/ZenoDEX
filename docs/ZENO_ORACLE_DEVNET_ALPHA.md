# Zeno Oracle Devnet Alpha

Status: local devnet service over the hardened Oracle MVP verifier shell.

This is not a production truth network. The devnet alpha adds a real transport,
receipt persistence, replay, and consumer read APIs around the existing local
verifiers. A report, feed, aggregate, read, adapter bridge, or budget event only
becomes visible after the corresponding verifier accepts it.

The academic-style whitepaper is published as
[docs/papers/zeno-oracle-whitepaper/main.pdf](papers/zeno-oracle-whitepaper/main.pdf),
authored by Dana Edwards. The package branding assets live under
`assets/branding/zeno-oracle/`.

## What Exists

| Surface | Command or Endpoint | Purpose |
| --- | --- | --- |
| Local service | `bin/zenodex-oracle serve --store /tmp/zeno-oracle-devnet` | Starts the HTTP devnet node. |
| Replay | `bin/zenodex-oracle replay --store /tmp/zeno-oracle-devnet` | Reconstructs state from `events.jsonl`. |
| Health | `GET /health` | Confirms the local node is reachable. |
| State replay | `GET /state` or `POST /replay` | Returns the replay receipt. |
| Reporter registration | `POST /reporters/register` | Persists registered reporter keys and bond lifecycle receipts. |
| Feed registration | `POST /feeds/register` | Persists accepted feed registries. |
| Signed report submission | `POST /reports/submit` | Verifies signatures, reporter registration, feed binding, and report admission. |
| Aggregate build | `POST /aggregates/build` | Builds admitted median3 aggregate, aggregate read, and adapter bridge. |
| Latest accepted read | `GET /reads/latest?query_id=...` | Returns the latest accepted aggregate-read bridge for a query. |
| Latest adapter bridge | `GET /adapter/latest?query_id=...` | Returns the latest accepted ZenoDEX adapter bridge for a query. |
| Economic event | `POST /economics/event` | Persists reward, bond, dispute, slash, burn, or treasury receipts after budget checks. |

## Local Flow

Start a node:

```bash
bin/zenodex-oracle serve --store /tmp/zeno-oracle-devnet --host 127.0.0.1 --port 8008
```

The service prints a JSON startup receipt with the actual port. Use `--port 0`
for an ephemeral local port in tests.

Replay the store:

```bash
bin/zenodex-oracle replay --store /tmp/zeno-oracle-devnet
```

The replay receipt reports accepted and rejected event counts, event-type
counts, latest artifact IDs by event type, missing artifact references, event
sequence errors, duplicate event IDs/sequences, malformed journal lines, and
artifact byte-hash mismatches.

## Fail-Closed Service Boundary

The service path is intentionally narrow:

```text
HTTP artifact accepted -> existing verifier accepted -> artifact persisted -> event receipt appended
```

Malformed or unverifiable objects are rejected and can still be logged as
rejected devnet events. Critical consumer reads are only exposed through
accepted aggregate-read and aggregate-adapter bridge artifacts.

The current admitted aggregate path requires three distinct admitted reports
for the same registered feed query. Each report must come from a registered
reporter, use a source ID admitted by the feed source-diversity policy, satisfy
the feed freshness window, and pass BLS signature verification.

## Replay Store

The devnet store is file based:

```text
events.jsonl
reporters/
feeds/
signed_reports/
admissions/
aggregates/
reads/
adapter_bridges/
economics/
replay/
```

`events.jsonl` is the append-only receipt stream. Replaying it checks that
referenced artifacts still exist and reconstructs the current receipt index.

## CI Gate

The devnet alpha gate is:

```bash
bash scripts/check_zeno_oracle_devnet_alpha.sh
```

It runs the full local MVP gate, the service-level HTTP integration tests, the
deterministic devnet disaster-state harness, and the devnet alpha audit. The
GitHub workflow builds a devnet alpha RC package after the gate passes.

The promoted disaster harness can also be replayed directly:

```bash
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
```

Current expected receipt:

```text
selected_disaster_state_count = 17
unreachable_count = 17
failed_count = 0
inconclusive_count = 0
```

This is bounded devnet evidence. It does not claim a production oracle network
is live or that all future Oracle disaster states are exhausted.

## RC Package

Build the package:

```bash
bash scripts/package_zeno_oracle_rc.sh zeno-oracle-devnet-alpha-rc1
```

The package includes:

```text
dist/zeno-oracle-devnet-alpha-rc1.tar.gz
dist/zeno-oracle-devnet-alpha-rc1.receipt.json
dist/zeno-oracle-devnet-alpha-rc1.sig
dist/zeno-oracle-devnet-alpha-rc1/ZEN_ORACLE_RC_MANIFEST.json
dist/zeno-oracle-devnet-alpha-rc1/assets/branding/zeno-oracle/
dist/zeno-oracle-devnet-alpha-rc1/docs/papers/zeno-oracle-whitepaper/main.pdf
```

The `.sig` file is a devnet integrity signature derived from the package hash.
It is not production code signing.

## Not Claimed

The devnet alpha does not claim:

- production oracle truth;
- live public reporter economics;
- on-chain feed governance;
- production code signing;
- platform-native installers;
- protection from dishonest real-world sources beyond the declared source and
  reporter verifier rules.
