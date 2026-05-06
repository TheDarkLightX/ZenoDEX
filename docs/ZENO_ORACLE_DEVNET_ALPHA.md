# Zeno Oracle Devnet Alpha

Status: local devnet service over the hardened Oracle MVP verifier shell.

This is not a production truth network. The devnet alpha adds a real transport,
receipt persistence, replay, and consumer read APIs around the existing local
verifiers. A report, feed, aggregate, read, adapter bridge, or budget event only
becomes visible after the corresponding verifier accepts it.

The academic-style whitepaper is published as
[docs/papers/zeno-oracle-whitepaper/ZenoOracleWhitepaper.pdf](papers/zeno-oracle-whitepaper/ZenoOracleWhitepaper.pdf),
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

It runs the full local MVP gate, the focused O3 receipt-flow replay, the
service-level HTTP integration tests, the critical-action map checker, the
reporter economics replay, the live-economics production-candidate policy, the
deterministic devnet disaster-state harness, the disaster corpus/frontier, the
obligation-antichain certificate, the frontier-to-obligation projection, the
ZenoProof production-governance candidate policy, the claims registry, the
blocked-goal audit, and the devnet alpha audit. The GitHub workflow builds a
devnet alpha RC package after the gate passes, then validates the package
manifest/signature receipt and runs the package-local replay gate from inside
the extracted bundle before upload.

The critical-action map can be checked directly:

```bash
python3 tools/check_zeno_oracle_critical_action_map.py
```

Current expected critical-action receipt:

```text
catalog_profile_count = 7
runtime_wired_count = 7
design_only_backlog_count = 0
status = accepted
```

The focused O3 receipt chain can be replayed directly:

```bash
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
```

Current expected O3 receipt:

```text
stage_count = 8
accepted_stage_count = 8
failed_stage_count = 0
status = accepted
```

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

The reporter economics replay can be checked directly:

```bash
python3 tools/zenodex_oracle_reporter_economics_replay.py self-test
```

Current expected economics receipt:

```text
"status": "accepted"
"reporter_count": 3
"report_count": 3
"dispute_count": 1
```

The live-economics production-candidate policy can be checked directly:

```bash
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
```

Current expected policy receipt:

```text
status = accepted
replay_status = accepted
receipt_bundle_status = accepted
error_count = 0
go_live_blocker_count = 6
```

The obligation-antichain certificate is checked directly:

```bash
python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
```

Current expected certificate receipt:

```text
ok: axes=24 quotient=21 antichain=16 selected_guards=10 private_witnesses=10
```

The production disaster frontier can be checked directly:

```bash
python3 tools/check_zeno_oracle_disaster_frontier.py --format text
```

Current expected frontier receipt:

```text
status = accepted
frontier_family_count = 29
closed_family_count = 24
blocked_or_backlog_count = 5
new_obligation_family_count = 0
error_count = 0
```

The frontier-to-obligation projection can be checked directly:

```bash
python3 tools/check_zeno_oracle_frontier_obligation_projection.py --format text
```

Current expected projection receipt:

```text
status = accepted
frontier_family_count = 29
projected_family_count = 29
new_obligation_family_count = 0
error_count = 0
```

The ZenoProof production-governance candidate policy can be checked directly:

```bash
python3 tools/check_zenoproof_production_governance_policy.py --format text
```

Current expected ZenoProof policy receipt:

```text
status = accepted
error_count = 0
receipt_bundle_status = accepted
go_live_blocker_count = 8
production_enabled_verifier_count = 8
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
dist/zeno-oracle-devnet-alpha-rc1/bin/zenodex-oracle
dist/zeno-oracle-devnet-alpha-rc1/scripts/check_zeno_oracle_rc_bundle.sh
dist/zeno-oracle-devnet-alpha-rc1/tools/check_disaster_obligation_certificate.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_claims_registry.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_cross_module_oracle_split_brain_v1.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zeno_oracle_disaster_frontier.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zeno_oracle_frontier_obligation_projection.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zeno_oracle_goal_completion_audit.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zeno_oracle_live_economics_policy.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zeno_oracle_rc_package.py
dist/zeno-oracle-devnet-alpha-rc1/tools/check_zenoproof_production_governance_policy.py
dist/zeno-oracle-devnet-alpha-rc1/tools/zeno_oracle_disaster_class_corpus.py
dist/zeno-oracle-devnet-alpha-rc1/tools/zeno_oracle_disaster_obligation_certificate_manifest.json
dist/zeno-oracle-devnet-alpha-rc1/tools/zeno_oracle_math_witness_sweep.jl
dist/zeno-oracle-devnet-alpha-rc1/tools/zeno_oracle_o3_receipt_flow_replay.py
dist/zeno-oracle-devnet-alpha-rc1/tools/zenodex_oracle_reporter_economics_replay.py
dist/zeno-oracle-devnet-alpha-rc1/docs/claims_registry.yaml
dist/zeno-oracle-devnet-alpha-rc1/src/
dist/zeno-oracle-devnet-alpha-rc1/tests/
dist/zeno-oracle-devnet-alpha-rc1/formal/
dist/zeno-oracle-devnet-alpha-rc1/generated/
dist/zeno-oracle-devnet-alpha-rc1/lean-mathlib/Proofs/
dist/zeno-oracle-devnet-alpha-rc1/lean-mathlib/proof_receipts/
dist/zeno-oracle-devnet-alpha-rc1/assets/branding/zeno-oracle/
dist/zeno-oracle-devnet-alpha-rc1/docs/papers/zeno-oracle-whitepaper/main.pdf
dist/zeno-oracle-devnet-alpha-rc1/docs/papers/zeno-oracle-whitepaper/ZenoOracleWhitepaper.pdf
```

The `.sig` file is a devnet integrity signature derived from the package hash.
It is not production code signing.

Validate a built package:

```bash
python3 tools/check_zeno_oracle_rc_package.py \
  --package-dir dist/zeno-oracle-devnet-alpha-rc1 \
  --receipt dist/zeno-oracle-devnet-alpha-rc1.receipt.json \
  --sig dist/zeno-oracle-devnet-alpha-rc1.sig
```

Replay a built package from inside the extracted bundle:

```bash
cd dist/zeno-oracle-devnet-alpha-rc1
bash scripts/check_zeno_oracle_rc_bundle.sh
```

This package-local gate runs the shipped O3 replay, reporter-economics replay,
live-economics policy, disaster harness, disaster frontier, obligation
certificate/projection, ZenoProof governance policy, claims registry, blocked
goal audit, package manifest check, and Julia witness sweep when Julia is
installed. The package checker rejects missing claims-registry evidence files,
so a shipped bundle cannot validate with only the registry YAML present.

## Not Claimed

The devnet alpha does not claim:

- production oracle truth;
- live public reporter economics;
- on-chain feed governance;
- production code signing;
- production ZenoProof verifier governance;
- generalized math-proof completion;
- platform-native installers;
- protection from dishonest real-world sources beyond the declared source and
  reporter verifier rules.
