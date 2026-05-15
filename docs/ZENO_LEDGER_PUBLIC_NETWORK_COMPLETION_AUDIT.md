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
| Let a remote computer bootstrap from one public entrypoint | `write-network-config`, `join-network`, `sync_public_bundle_from_url_v0` | Integration test joins from `public_network_config.json`; smoke syncs two independent node bundles from HTTP | Built and locally tested |
| Let operators pin the expected bootstrap config | `--expected-network-config-hash` on `join-network` | `tests/integration/test_zeno_ledger_node.py` checks accepted hash and rejects `0x00...00` | Built and locally tested |
| Preflight local and remote setup | `tools/zeno_ledger_node.py doctor` | Local `doctor` returns `ok: true`; integration validates a remote network config with expected hash | Built and locally tested |
| Run a node that serves status | `run --serve`, `serve`, `make_node_http_server_v0` | Integration checks `/health`, `/status`, `/features`, `/tokens`, `/network`, `/live`, `/attestation`, `/testnet-status` | Built and locally tested |
| Append live testnet DEX transactions | `append`, `POST /tx`, `append_dex_transaction_v0` | Integration and smoke append a live swap and live fake-token pool operations | Built and locally tested |
| Pull live blocks from a peer by deterministic replay | `pull-live`, `pull_live_from_peer_v0` | Integration and smoke show Node B moves from `peer_ahead` to `same_height` and common height `13` | Built and locally tested |
| Continuously follow live peers when served | `poll_live_peers_once_v0`, `follow-once`, `GET /follow`, served-node polling loop | Integration writes `peer_follow_state.json` and verifies the nested deterministic pull report | Built and locally tested |
| Forward follower submissions to writer | `--submit-peer-url` on served follower | Integration and smoke forward a faucet request through Node B to Node A | Built and locally tested |
| Support testnet ZenoDEX token fixtures | Public bundle token catalog | `/tokens` reports `tZENO`, `tASSET0`, and `tASSET1` | Built and locally tested |
| Mint fake test assets | `faucet`, `POST /faucet`, `append_testnet_faucet_v0` | Integration and smoke faucet existing fixture and created fake assets | Built and locally tested |
| Create named fake test tokens | `create-token`, `POST /tokens`, `append_testnet_token_create_v0` | Integration and smoke create `tMANGO` and use its derived asset ID | Built and locally tested |
| Replay created token registry across peers | `testnet_token_registry.json`, pull-live token-create handling | Integration asserts Node B registry contains `tMANGO` after pulling live blocks | Built and locally tested |
| Produce portable node evidence | `evidence`, `build_node_evidence_report_v0` | Integration checks local tip `13`, created token count `1`, and peer check `ok: true` | Built and locally tested |
| Verify separate-machine evidence | `tools/zeno_ledger_verify_two_machine_evidence.py` | Integration verifies the evidence report's same-height peer, common header binding, and expected `tMANGO` token | Built and locally tested |
| Run the Machine B acceptance path from one command | `tools/zeno_ledger_machine_b_acceptance.py` | Local command-level smoke accepted with `tACCEPT`, `evidence_report_ok=true`, and `verification_report_ok=true` | Built and locally tested |
| Provide two-machine operator steps | `docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md` | Runbook includes prerequisites, ports, hash pinning, doctor, join, evidence, tokens, faucet, and peer checks | Documented |

## Latest Local Evidence

The following gates passed on the current main-based worktree:

```bash
python3 -m py_compile tools/zeno_ledger_node.py tests/integration/test_zeno_ledger_node.py
python3 tools/zeno_ledger_node.py doctor
pytest tests/integration/test_zeno_ledger_node.py -q
python3 tools/zeno_ledger_public_network_smoke.py --out-dir /tmp/zeno-ledger-public-network-smoke-evidence
```

Observed accepted smoke fields:

```text
ok: true
source_feature_count: 10
sync_a_feature_count: 10
sync_b_feature_count: 10
created_test_token_symbol: tMANGO
token_create_height: 8
swap_height: 7
create_fake_pool_height: 10
add_fake_pool_liquidity_height: 11
remove_fake_pool_liquidity_height: 12
node_b_follow_peer_count: 1
node_b_total_pulled_count: 8
node_b_latest_height: 13
final_peer_check_ok: true
final_peer_height_relation: same_height
final_common_height: 13
```

## Remaining Acceptance Item

This audit does not mark the public-network goal complete because one claim has
not been externally observed from this session:

```text
Machine B on a separate physical computer bootstraps from Machine A's public
URL, verifies the pinned network config hash, joins, forwards or pulls live
blocks, and emits a ZenoLedger evidence report matching Machine A at the common
header.
```

The expected command sequence is in `docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md`.
After the MacBook run, the decisive artifact is:

```bash
python3 tools/zeno_ledger_node.py evidence \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787 \
  --out /tmp/zeno-ledger-node-b/evidence_report.json
```

Completion condition:

```text
evidence_report.ok = true
peer_check.ok = true
peer_check.peers[0].height_relation = same_height
created_test_tokens contains the test token created during the run
local_tip.header_hash equals the peer common header hash at the same height
```

The verification command for that condition is:

```bash
python3 tools/zeno_ledger_verify_two_machine_evidence.py \
  --evidence-report /tmp/zeno-ledger-node-b/evidence_report.json \
  --expected-created-token-symbol tMANGO \
  --min-height 13
```

The one-command Machine B runner that produces those evidence files is:

```bash
python3 tools/zeno_ledger_machine_b_acceptance.py \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --expected-network-config-hash <NETWORK_CONFIG_HASH> \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --token-symbol tMANGO \
  --out /tmp/zeno-ledger-node-b/machine_b_acceptance_report.json
```

Until that separate-machine artifact exists, the implementation is a
public-testnet candidate with strong local two-node evidence, not a completed
public-network goal.
