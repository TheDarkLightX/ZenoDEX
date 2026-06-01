# ZenoLedger Public Network Completion Audit

This audit maps the current ZenoLedger public-node implementation to the
active objective:

```text
ZenoDEX should be able to run through ZenoLedger nodes, any computer should be
able to bootstrap from a public entrypoint, and operators should be able to use
testnet ZenoDEX tokens plus created fake test tokens for feature testing.
```

## Checklist

| Requirement | Current artifact | Evidence | Status |
| --- | --- | --- | --- |
| Build a public bootstrap bundle | `tools/zeno_ledger_node.py bootstrap`, `tools/zeno_ledger_make_public_testnet_bundle.py` | `tools/zeno_ledger_public_network_smoke.py` builds a source bundle with `source_feature_count=10` | Built and locally tested |
| Run Machine A from one command | `tools/zeno_ledger_machine_a_host.py` | Builds the bundle, starts the mirror and writer API, writes `public_network_config.json`, and prints Machine B's acceptance command | Built |
| Let a remote computer bootstrap from one public entrypoint | `write-network-config`, `join-network`, `sync_public_bundle_from_url_v0` | Integration test joins from `public_network_config.json`; smoke syncs two independent node bundles from HTTP | Built and locally tested |
| Let operators pin the expected bootstrap config | `--expected-network-config-hash` on `join-network` | `tests/integration/test_zeno_ledger_node.py` checks accepted hash and rejects `0x00...00` | Built and locally tested |
| Preflight local and remote setup | `tools/zenoctl.py doctor`, `tools/zeno_ledger_node.py preflight`, `doctor_public_node_v0` | Local doctor/preflight checks exist; integration validates a remote network config with expected hash | Built and locally tested |
| Run a node that serves status | `run --serve`, `serve`, `make_node_http_server_v0` | Integration checks `/health`, `/status`, `/features`, `/tokens`, `/network`, `/live`, `/attestation`, `/testnet-status` | Built and locally tested |
| Append live testnet DEX transactions | `append`, `POST /tx`, `append_dex_transaction_v0` | Integration and smoke append a live swap and live fake-token pool operations | Built and locally tested |
| Pull live blocks from a peer by deterministic replay | `pull-live`, `pull_live_from_peer_v0` | Integration and smoke show Node B moves from `peer_ahead` to `same_height` and common height `13` | Built and locally tested |
| Continuously follow live peers when served | `poll_live_peers_once_v0`, `follow-once`, `GET /follow`, served-node polling loop | Integration writes `peer_follow_state.json` and verifies the nested deterministic pull report | Built and locally tested |
| Forward follower submissions to writer | `--submit-peer-url` on served follower | Integration and smoke forward a faucet request through Node B to Node A | Built and locally tested |
| Support testnet ZenoDEX token fixtures | Public bundle token catalog | `/tokens` reports `tZENO`, `tASSET0`, and `tASSET1` | Built and locally tested |
| Mint fake test assets | `faucet`, `POST /faucet`, `append_testnet_faucet_v0` | Integration and smoke faucet existing fixture and created fake assets | Built and locally tested |
| Exercise fake test tokens | `faucet`, `POST /faucet`, deterministic fixture token catalog | Integration and smoke mint fixture test assets and use a fake asset in pool operations | Built and locally tested |
| Replay fake-token effects across peers | live-block pull plus deterministic replay | Smoke asserts Node B reaches the same common header after fake-token faucet and pool operations | Built and locally tested |
| Produce portable node evidence | `build_node_evidence_report_v0` | Evidence report binds local tip, feature coverage, fixture-token catalog, and peer check | Built and locally tested |
| Verify separate-machine evidence | `tools/zeno_ledger_verify_two_machine_evidence.py` | Integration verifies the evidence report's same-height peer, common header binding, and expected fixture token | Built and locally tested |
| Run the Machine B acceptance path from one command | `tools/zeno_ledger_machine_b_acceptance.py` | Runner joins from config URL, faucets an existing fixture token, follows live peers, and emits evidence | Built and locally tested |
| Provide two-machine operator steps | `docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md` | Runbook includes prerequisites, ports, hash pinning, doctor, join, evidence, tokens, faucet, and peer checks | Documented |

## Latest Local Evidence

The following gates passed on the current main-based worktree:

```bash
python3 -m py_compile tools/zeno_ledger_node.py tests/integration/test_zeno_ledger_node.py
python3 tools/zenoctl.py doctor
pytest tests/integration/test_zeno_ledger_node.py -q
python3 tools/zeno_ledger_public_network_smoke.py --out-dir /tmp/zeno-ledger-public-network-smoke-evidence
```

Observed accepted smoke fields:

```text
ok: true
source_feature_count: 10
sync_a_feature_count: 10
sync_b_feature_count: 10
faucet_new_asset_height: 8
swap_height: 7
create_fake_pool_height: 9
add_fake_pool_liquidity_height: 10
remove_fake_pool_liquidity_height: 11
node_b_follow_peer_count: 1
node_b_total_pulled_count: 8
node_b_latest_height: 13
final_peer_check_ok: true
final_peer_height_relation: same_height
final_common_height: 13
```

## Current Acceptance State

The Machine B path has succeeded through Docker multi-machine rehearsal. That
is useful release evidence for multi-node replay and follower behavior, but it
does not close the public URL bootstrap item. The remaining v0.1.16 blocker is a
clean operator path that joins from a published `public_network_config.json`
URL, plus a phone/browser validation artifact.

Use this gate for the durable v0.1.16 evidence bundle:

```bash
python3 tools/check_public_testnet_v0_1_16_evidence.py \
  /path/to/public-testnet-v0.1.16-evidence.json --pretty
```

The gate separates these claims:

- Docker or LAN multi-machine run: Machine A/B evidence reaches a common header.
- Public URL bootstrap: a clean machine joins only from the config URL, verifies
  bundle hashes, checks the seed peer, and serves status.
- Second follower: another clean machine reaches the same common header.
- Phone/browser: a public UI load or browser checkpoint-bundle verification
  succeeds without exposing backend bearer tokens.

The HTTP/public-config URL flow is still the practical friction point. Do not
claim v0.1.16 public-testnet readiness from Docker success alone.

The release evidence claim is:

```text
Machine B on a clean computer bootstraps from Machine A's published config URL,
verifies the pinned network config hash, joins, forwards or pulls live blocks,
and emits a ZenoLedger evidence report matching Machine A at the common header.
```

The expected command sequence is in `docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md`.
After the MacBook run, the decisive artifact is:

```bash
python3 tools/zeno_ledger_machine_b_acceptance.py \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --expected-network-config-hash <NETWORK_CONFIG_HASH> \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --token-symbol tZENO \
  --out /tmp/zeno-ledger-node-b/machine_b_acceptance_report.json
```

Completion condition:

```text
evidence_report.ok = true
peer_check.ok = true
peer_check.peers[0].height_relation = same_height
created_test_tokens contains the exercised testnet fixture token
local_tip.header_hash equals the peer common header hash at the same height
```

The verification command for that condition is:

```bash
python3 tools/zeno_ledger_verify_two_machine_evidence.py \
  --evidence-report /tmp/zeno-ledger-node-b/evidence_report.json \
  --expected-created-token-symbol tZENO \
  --min-height 13
```

The runner embeds `latest_main_summary` in `machine_b_acceptance_report.json`
so the durable artifact can bind the commit SHA, network config hash,
feature-suite hash, Machine A/B tips, common header hash, exercised test token,
and accepted/rejected submission counts. The v0.1.16 bundle should additionally
bind the public URL and phone/browser evidence through
`tools/check_public_testnet_v0_1_16_evidence.py`.
