# Zeno Oracle CLI V1

Status: first local user-facing CLI wrapper.

The Oracle MVP now has one local entry point:

```bash
python3 tools/zenodex_oracle_cli.py
```

The RC package also includes an executable launcher:

```bash
bin/zenodex-oracle
```

This wrapper does not replace the individual verifiers. It routes to them so a
user can discover, generate, verify, and replay Oracle artifacts without knowing
every script name.

## Discovery

List available verifier surfaces:

```bash
python3 tools/zenodex_oracle_cli.py list
```

Check that the local verifier shell is present:

```bash
python3 tools/zenodex_oracle_cli.py doctor
```

In an unpacked RC package, the equivalent command is:

```bash
bin/zenodex-oracle doctor
```

The doctor command returns a JSON receipt with `ok`, `surface_count`,
`chaos_surface_count`, and any missing scripts.

## Feed Creation

Create a local sample feed registry:

```bash
python3 tools/zenodex_oracle_cli.py sample feed --output /tmp/zeno-oracle-feed-registry.json
```

Verify it:

```bash
python3 tools/zenodex_oracle_cli.py verify feed /tmp/zeno-oracle-feed-registry.json
```

Register it into a local Oracle store:

```bash
python3 tools/zenodex_oracle_cli.py register-feed /tmp/zeno-oracle-feed-registry.json --store /tmp/zeno-oracle-store
```

`feed-registry` is accepted as an alias for `feed`.

## Reporter Signed Reports

Create a local signed-report sample:

```bash
python3 tools/zenodex_oracle_cli.py sample signed-report --output /tmp/zeno-oracle-signed-report.json
```

Verify it:

```bash
python3 tools/zenodex_oracle_cli.py verify signed-report /tmp/zeno-oracle-signed-report.json
```

Submit it into a local Oracle store:

```bash
python3 tools/zenodex_oracle_cli.py submit-report /tmp/zeno-oracle-signed-report.json --store /tmp/zeno-oracle-store
```

The signed-report verifier still performs the same payload-hash, report-ID,
sequence, previous-link, duplicate, key-format, and BLS signature checks as the
underlying `tools/zenodex_oracle_signed_report.py` script.

## Local MVP Dry Run

Run the local happy path from one command:

```bash
bin/zenodex-oracle dry-run --workdir /tmp/zeno-oracle-dry-run
```

The same command through Python is:

```bash
python3 tools/zenodex_oracle_cli.py dry-run --workdir /tmp/zeno-oracle-dry-run
```

The dry run generates and verifies a sample feed registry, signed report,
reporter lifecycle trace, token budget transition, admitted median aggregate,
aggregate read, aggregate adapter, and consumer adapter bundle. It also stores
the accepted feed and signed report under the local Oracle store. This is still
a local replay path, not network broadcast.

## Other Surfaces

The same shape works for the other local surfaces:

```bash
python3 tools/zenodex_oracle_cli.py sample admitted-median3 --output /tmp/aggregate.json
python3 tools/zenodex_oracle_cli.py verify admitted-median3 /tmp/aggregate.json

python3 tools/zenodex_oracle_cli.py sample aggregate-adapter --output /tmp/bridge.json
python3 tools/zenodex_oracle_cli.py verify aggregate-adapter /tmp/bridge.json
```

Some surfaces have custom sample arguments. The wrapper forwards remaining
arguments directly to the underlying tool.

## Chaos Replay

Run a single lane:

```bash
python3 tools/zenodex_oracle_cli.py chaos feed
```

Run all local Oracle chaos lanes and emit a combined JSON summary:

```bash
python3 tools/zenodex_oracle_cli.py chaos all
```

The combined replay returns:

```json
{
  "schema": "zenodex.oracle.cli_chaos_all.v1",
  "ok": true,
  "surface_count": 15,
  "case_count": 283,
  "rejected_case_count": 283,
  "failed_case_count": 0
}
```

## Not Claimed

This CLI does not claim:

- a live Oracle network exists;
- a platform-native binary installer exists;
- on-chain feed governance is live;
- network submission is implemented; local store submission is only a replayable
  dev/test flow;
- production ZenoDEX consumers are wired to Oracle reads.

It is the first local runner for the public-testnet Oracle shell.

## CI Gate

The local release gate is:

```bash
bash scripts/check_zeno_oracle_mvp.sh
```

That script runs `doctor`, `chaos all`, and the full Oracle pytest slice. The
GitHub Actions workflow `.github/workflows/zeno-oracle-mvp.yml` runs the same
gate on pull requests and pushes to `main` or this Oracle MVP branch.

## Release Candidate Package

Build the local RC package:

```bash
bash scripts/package_zeno_oracle_rc.sh
```

The script writes:

```text
dist/zeno-oracle-mvp-rc1.tar.gz
dist/zeno-oracle-mvp-rc1/ZEN_ORACLE_RC_MANIFEST.json
```

The manifest lists every packaged file with `size_bytes` and `sha256`, and sets
`bin/zenodex-oracle` as the package entrypoint. The CI workflow uploads the
tarball and manifest as the `zeno-oracle-mvp-rc1` artifact.
