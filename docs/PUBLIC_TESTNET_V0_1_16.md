# Historical Public Testnet v0.1.16

v0.1.16 is retained historical fake-value testnet evidence. Its release flow
requires the retired stream-8 perps and stream-11 zUSD monetary bridge routes.
The current local profile quarantines those routes, so this document does not
describe a currently eligible release.

This historical target has no production value, moves no mainnet assets, and
has no production consensus claim. The default zero-cost public URL was a Cloudflare
Quick Tunnel, so the URL is session-stable unless a stable named HTTPS domain
is provided.

## Public host

Prerequisites: Docker or Podman and `external/tau-testnet/`. The launcher uses
`cloudflared` on PATH when available; otherwise it runs the official
`cloudflare/cloudflared:latest` container through Docker or Podman. If another
tunnel manager creates the URL, pass `--tunnel-url` in the scripted form.

Operator launcher:

```bash
./bin/zenodex-public-testnet
```

Installed operator-bundle launcher:

```bash
zenodex-public-testnet
```

The launcher uses `~/.zenodex/public-testnet-v0.1.16` and attempts the historical
release smoke before starting a stack or tunnel. That check now returns
`blocked_current_profile` with authority `NONE`. On macOS, the retained
`bin/zenodex-public-testnet.command` path has the same refusal.

Scripted form:

```bash
python3 tools/zenoctl.py testnet local public-up \
  --out-dir /tmp/zen-public-v016 \
  --release-smoke \
  --open
```

This command refuses before the stack, tunnel, manifest, or report is created.
Removing `--release-smoke` does not bypass current-profile admission. The
retained profile creates no public URL and grants no release or value-movement
authority.

## Community follower

The commands in this section describe the historical follower workflow. The
current profile produces no host URL or public network config. A later admitted
profile would require clean-machine verification before any URL could be shared
as evidence.

```bash
./bin/zenodex-public-follower \
  --config-url https://<quick-tunnel-host>/public_network_config.json
```

Installed operator-bundle form:

```bash
zenodex-public-follower \
  --config-url https://<quick-tunnel-host>/public_network_config.json
```

The follower command downloads the hash-pinned bundle, replays the bootstrap
ledger, pulls live blocks through `/live`, checks the common header against the
seed, and writes
`~/.zenodex/public-follower/<node-id>/public_follower_acceptance_report.json`.
Use `--serve` to keep a read-only local follower node running after acceptance:

```bash
zenodex-public-follower \
  --config-url https://<quick-tunnel-host>/public_network_config.json \
  --serve
```

The default follower bind address is `127.0.0.1`, and mutation routes are not
enabled on the follower. A public release evidence bundle needs at least two
clean follower reports, preferably from separate machines or networks.

## Historical release-smoke checklist

```bash
python3 tools/zenoctl.py testnet local release-smoke \
  --out-dir /tmp/zen-public-v016
```

The current command returns a typed `blocked_current_profile` rejection and
writes no report. Historical v0.1.16 artifacts covered this checklist:

- faucet `tAGRS`;
- verify fixture accounts were pre-funded with fake native AGRS plus test assets;
- deposit AGRS collateral in the zUSD vault;
- mint `zUSD`;
- deposit zUSD-denominated perps collateral;
- open one long and one short;
- publish and settle perps oracle/epoch state;
- execute a `tAGRS/tZDEX` spot swap;
- verify token catalog, live height, feature hash, config hash, and header/app
  tip agreement.

## Evidence gate

```bash
python3 tools/check_public_testnet_v0_1_16_evidence.py \
  /path/to/public-testnet-v0.1.16-evidence.json
```

The historical evidence manifest includes:

- Docker/local full-stack smoke report;
- external laptop acceptance report;
- second clean follower report;
- phone/browser validation report;
- release-flow transaction smoke report;
- residual-limits statement.

Set `public_config_url_posture` to `session_stable_quick_tunnel` for a
`trycloudflare.com` URL, or `stable_named_url` only for a stable named HTTPS
URL with `stable_public_config_url: true`.
