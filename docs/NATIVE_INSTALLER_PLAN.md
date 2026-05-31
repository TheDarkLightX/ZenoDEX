# Native Installer Plan

This plan turns the current operator bundle into a user-facing install path for
Windows, macOS, and Linux while preserving the existing local-testnet
orchestration as the behavior source of truth.

## Current State

The current release path is:

```text
download operator tarball
-> verify SHA256SUMS
-> extract
-> clone external/tau-testnet
-> run python3 tools/zenoctl.py testnet local up
```

That path is deterministic and operator-friendly, but it is too manual for
ordinary local-testnet testers.

## V1 Target

```text
download native zenodex launcher
-> run zenodex local-testnet up
-> browser opens the local UI
```

The launcher should make the common path one command while keeping failures
explicit:

- missing Docker/Podman reports an actionable prerequisite error;
- missing Python reports an actionable prerequisite error until the orchestrator
  is fully native or bundled;
- missing `external/tau-testnet` is fetched automatically for local testnet
  unless `--no-auto-tau` is set;
- the default local-testnet state directory is `~/.zenodex/local-testnet`;
- all local-testnet lifecycle commands still call the checked `zenoctl.py`
  implementation.

## Shipped Slice

The first native binary is `zenodex`, implemented in
`rust-runtime/crates/zenodex-launcher`.

Supported commands:

```bash
zenodex doctor --engine none --strict
zenodex local-testnet up
zenodex local-testnet status
zenodex local-testnet smoke --browser auto
zenodex local-testnet down
zenodex zenoctl <existing zenoctl args>
```

The launcher is deliberately small. It discovers the operator bundle root,
checks or fetches the Tau local-testnet dependency, supplies a default
`--out-dir`, and delegates to `tools/zenoctl.py`.

## Release Artifacts

The `native-launcher` workflow builds `zenodex` on:

- `ubuntu-latest`;
- `macos-latest`;
- `windows-latest`.

Those binaries are uploadable workflow artifacts. The existing release-publish
workflow also attaches a Linux `zenodex` launcher binary beside the operator
bundle. Windows and macOS release attachment should follow once signing and
notarization are configured.

## Installer Track

Native installers are feasible, but they need platform-specific trust work:

- Windows: MSI or setup EXE, signed before public distribution.
- macOS: `.dmg` or `.pkg`, signed with Developer ID and notarized.
- Linux: `.AppImage` plus `.deb` or `.rpm`.

The installer should install the launcher and optionally place an operator
bundle under the user data directory. It should not install secrets, expose
ports publicly, or bypass the existing deployment-profile checks.

## Deferred Work

- Replace the Python orchestration dependency with a fully native command path,
  or bundle a controlled Python runtime.
- Pin the Tau local-testnet dependency to a manifest with commit hash and
  checksum, then verify after fetch.
- Add release signing and provenance attestations for each native binary.
- Add a Tauri desktop shell once the CLI path is stable. The desktop shell
  should call the native launcher rather than duplicate orchestration logic.
