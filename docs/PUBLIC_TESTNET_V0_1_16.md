# Public Testnet v0.1.16

v0.1.16 is a public fake-value testnet target for the release-relevant DEX
flows: `tAGRS`, `tZDEX`, collateralized `zUSD`, spot swaps, and basic long/short
perps.

This release target has no production value, no mainnet custody, and no
production consensus claim. The default zero-cost public URL is a Cloudflare
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

The launcher uses `~/.zenodex/public-testnet-v0.1.16`, starts the full stack,
runs the release smoke, opens a Cloudflare Quick Tunnel, and opens the public
UI URL in the default browser. On macOS, double-click
`bin/zenodex-public-testnet.command` for the same path.

Scripted form:

```bash
python3 tools/zenoctl.py testnet local public-up \
  --out-dir /tmp/zen-public-v016 \
  --release-smoke \
  --open
```

Both paths print the public UI URL, `/public_network_config.json`, the config
hash, the admin/write token file location, and read-only tester instructions.
Browser users do not receive bearer tokens. nginx injects local writer/API
tokens server-side for the capped fake-value testnet flow. The launcher
pre-funds the fixture test accounts with fake native AGRS plus `tAGRS`/`tZDEX`,
so the existing zUSD, perps, and spot pages can run without a new GUI surface.

## Community follower

An outside tester should verify the testnet from a clean machine before the
URL is shared as evidence. Give them only the public config URL printed by the
host command:

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

## Release smoke

```bash
python3 tools/zenoctl.py testnet local release-smoke \
  --out-dir /tmp/zen-public-v016
```

The smoke report proves:

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

The evidence manifest must include:

- Docker/local full-stack smoke report;
- external laptop acceptance report;
- second clean follower report;
- phone/browser validation report;
- release-flow transaction smoke report;
- residual-limits statement.

Set `public_config_url_posture` to `session_stable_quick_tunnel` for a
`trycloudflare.com` URL, or `stable_named_url` only for a stable named HTTPS
URL with `stable_public_config_url: true`.
