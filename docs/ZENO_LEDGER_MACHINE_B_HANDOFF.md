# ZenoLedger Machine B Handoff

This note is for the agent operating Machine B in the two-machine ZenoLedger
latest-pushed-commit evidence run.

## Human Input Contract

The human should not need to paste these instructions into Machine B. The
Machine B agent should fetch the repo branch, open this note, and follow it.

The only value Machine B may need from the human is Machine A's reachable
address:

```text
MACHINE_A_CONFIG_URL=http://<MACHINE_A_IP>:8000/public_network_config.json
```

If the human can only paste a private server URL or host/IP, use it only for
that connection value. Do not ask the human to relay command blocks between
machines.

## Target

Machine A and Machine B must run the same latest pushed commit on:

```text
codex/zeno-ledger-public-testnet-20260514
```

Fetch the branch and detach at the remote branch tip after the coordinator has
finished pushing this handoff update:

```bash
git fetch origin codex/zeno-ledger-public-testnet-20260514
git checkout --detach origin/codex/zeno-ledger-public-testnet-20260514
git rev-parse HEAD
```

Set the exact evidence commit from the checked-out commit:

```bash
COMMIT_SHA="$(git rev-parse HEAD)"
printf '%s\n' "$COMMIT_SHA"
```

Machine A and Machine B must print the same `COMMIT_SHA`. Use that value for
every `--commit-sha`, `--latest-pushed-commit-sha`, and `--expected-commit`
argument in this run.

Do not edit, commit, or push during the evidence run.

## Clean-Checkout Blocker

Do not run evidence from either of these older commits:

```text
cb39d0a9031f2529cefe69762e0ae5843693a75c
857507e2...
```

Those commits were missing tracked files needed by a clean checkout. The visible
symptom was:

```text
ModuleNotFoundError: No module named 'src.core.uniform_batch_clearing'
```

The fixed branch tip must contain these tracked paths:

```bash
git ls-files src/core/uniform_batch_clearing.py
git ls-files tools/check_zeno_ledger_two_machine_evidence.py
git ls-files tools/build_zeno_ledger_two_machine_evidence.py
git ls-files tests/tools/test_check_zeno_ledger_two_machine_evidence.py
git ls-files tests/tools/test_build_zeno_ledger_two_machine_evidence.py
```

Run this import smoke before starting:

```bash
python3 - <<'PY'
import src.integration.validation
import src.integration.dex_engine
import tools.build_zeno_ledger_two_machine_evidence
import tools.check_zeno_ledger_two_machine_evidence
print("imports ok")
PY
```

Do not create evidence by adding local untracked shims or test helpers. Evidence
must be produced from tracked files at the shared `COMMIT_SHA`.

## Join Machine A

Set Machine A's connection details. If the human gives only an IP or hostname,
use the first form. If the human gives the full config URL, use the second form.

```bash
export MACHINE_A_HOST="<MACHINE_A_IP_OR_HOSTNAME>"
export MACHINE_A_CONFIG_URL="http://${MACHINE_A_HOST}:8000/public_network_config.json"
export MACHINE_A_PEER_URL="http://${MACHINE_A_HOST}:8787"
```

```bash
export MACHINE_A_CONFIG_URL="<FULL_MACHINE_A_CONFIG_URL>"
export MACHINE_A_HOST="$(python3 - <<'PY'
import os
from urllib.parse import urlparse
url = os.environ["MACHINE_A_CONFIG_URL"]
print(urlparse(url).hostname or "")
PY
)"
export MACHINE_A_PEER_URL="http://${MACHINE_A_HOST}:8787"
```

Join Machine A:

```bash
python3 tools/zeno_ledger_node.py join-network \
  --config-url "$MACHINE_A_CONFIG_URL" \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --serve
```

Confirm Machine B can see Machine A:

```bash
python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url "$MACHINE_A_PEER_URL"
```

Expected result: `ok: true`, matching `network_id`, matching `chain_id`,
matching `feature_suite_hash`, and matching common header hash.

Inspect Machine B mode:

```bash
curl http://127.0.0.1:8788/network
```

If Machine B is forwarding testnet submissions to Machine A,
`capabilities.submission_forwarding_enabled` should be `true`.

## Build Machine B Evidence

After Machine B has caught up to Machine A and the fake-token or forwarded
faucet activity is complete, generate the Machine B evidence files:

```bash
mkdir -p /tmp/zeno-ledger-evidence

python3 tools/build_zeno_ledger_node_evidence_input.py \
  --data-dir /tmp/zeno-ledger-node-b \
  --network-config /tmp/zeno-ledger-node-b/public_network_config.json \
  --machine-out /tmp/zeno-ledger-evidence/machine_b.json \
  --attestation-out /tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json \
  --commit-sha "$COMMIT_SHA" \
  --pretty
```

Send these two files back to the coordinator:

```text
/tmp/zeno-ledger-evidence/machine_b.json
/tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json
```

Also report the output of:

```bash
python3 --version

python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url "$MACHINE_A_PEER_URL"

curl http://127.0.0.1:8788/network
```

Do not send auth tokens. The coordinator only needs evidence JSON, hashes,
counts, and checker output.

## Missing-File Checks

If a file is missing, report the exact path and run:

```bash
pwd
git rev-parse HEAD
git status --short
find /tmp -name public_network_config.json -print
ls -l /tmp/zeno-ledger-node-b || true
ls -l /tmp/zeno-ledger-evidence || true
```

If `/tmp/zeno-ledger-node-b/public_network_config.json` is missing,
`join-network` did not complete or used a different `--data-dir`. If
`$MACHINE_A_CONFIG_URL` is missing, Machine A has not published or served the
public network config yet, or Machine B cannot reach Machine A at the supplied
address.

## Loopback Machine B Fallback

Use this fallback when a second physical laptop cannot reach Machine A because
of hotspot routing, VPN policy, client isolation, or unknown Wi-Fi behavior.
Run it on Machine A from the same checked-out branch:

```bash
python3 tools/zeno_ledger_loopback_machine_b.py
```

The harness starts Machine A on random high ports and runs Machine B inside a
clean `python:3.12-slim` Docker container. The container installs the
hash-locked `requirements-core.lock.txt`, joins through the published
`public_network_config.json`, checks Machine A as a peer, pulls live blocks,
forwards a faucet write back to Machine A, pulls the forwarded block, and
builds:

```text
<out-dir>/evidence/machine_a.json
<out-dir>/evidence/machine_b.json
<out-dir>/evidence/machine_a_watcher_attestation.json
<out-dir>/evidence/machine_b_watcher_attestation.json
<out-dir>/evidence/token_test_result.json
<out-dir>/evidence/two_machine_evidence.json
<out-dir>/loopback_machine_b_report.json
```

This is acceptable protocol-path evidence for a clean Machine B environment.
It proves the join, peer-check, live-pull, write-forwarding, and evidence
archive code paths across an HTTP boundary and a separate network namespace.
It leaves one residual network assumption: a separate physical laptop may still
need router, hotspot, VPN, or firewall changes to reach Machine A.

If Docker cannot resolve `host.docker.internal`, retry with:

```bash
python3 tools/zeno_ledger_loopback_machine_b.py --host-alias 172.17.0.1
```

If Docker Desktop already provides `host.docker.internal` and rejects Docker's
`host-gateway` mapping, retry with:

```bash
python3 tools/zeno_ledger_loopback_machine_b.py --no-add-host-gateway
```

## Full VM Fallback

A full VM can act as Machine B if its network can reach Machine A's host ports.
Use NAT with the VM's host-gateway address, or bridged networking if the local
Wi-Fi driver supports it. Then set:

```bash
export MACHINE_A_CONFIG_URL="http://<VM_HOST_GATEWAY_OR_MACHINE_A_IP>:8000/public_network_config.json"
```

Run the normal Machine B join and evidence commands above. The VM path is closer
to a physical two-machine run than Docker, but Docker is the fastest repeatable
fallback when a hotspot blocks peer-to-peer traffic.
