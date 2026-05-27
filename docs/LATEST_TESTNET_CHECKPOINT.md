# Latest Testnet Checkpoint

Checkpoint: `testnet-20260527T061624Z`

This checkpoint packages the current local-testnet GUI, the executed
ZenoLedger public-testnet bootstrap bundle, and an operator source archive.

Local artifact directory:

```bash
dist/zenodex-testnet-20260527T061624Z
```

Artifacts:

- `zenodex-dex-ui-testnet-20260527T061624Z.tar.gz` contains the static DEX UI
  build. Its checked-in runtime config is local-testnet testing mode with
  browser key generation enabled until the standalone Keys app replaces browser
  signing.
- `zeno-ledger-public-testnet-20260527T061624Z.tar.gz` contains the executed
  public-testnet bootstrap bundle and core feature-suite evidence.
- `operator/zenodex-operator-testnet-20260527T061624Z.tar.gz` contains the
  operator source bundle and deterministic manifest.
- `SHA256SUMS` and `SHIPMENT_MANIFEST.json` bind the local files to hashes and
  replay commands.

Build and verify from a checkout:

```bash
npm run build --prefix tools/dex-ui
python3 tools/zeno_ledger_make_public_testnet_bundle.py \
  --out-dir dist/zenodex-testnet-20260527T061624Z/public-testnet-bundle-v2
python3 tools/build_operator_release_bundle.py build \
  --out-dir dist/zenodex-testnet-20260527T061624Z/operator \
  --version testnet-20260527T061624Z
python3 tools/build_operator_release_bundle.py verify \
  --manifest dist/zenodex-testnet-20260527T061624Z/operator/zenodex-operator-testnet-20260527T061624Z.tar.gz.manifest.json
```

Live local-testnet GUI check:

```bash
npm run dev --prefix tools/dex-ui -- --host 127.0.0.1 --port 5173
curl -fsS http://127.0.0.1:5173/api/confidential/status
```

When a `zenoctl testnet local up` stack is running, the Vite dev server
auto-detects the loopback nginx port and proxies `/api/*` to that live stack.
