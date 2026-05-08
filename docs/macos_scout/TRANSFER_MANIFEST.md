# MacOS Scout Transfer Manifest

Transfer these paths to the Mac if you are not using a temporary Git branch:

```text
docs/macos_scout/CODEX_HANDOFF_PROMPT.md
docs/macos_scout/MAC_AGENT_OPERATING_LOOP.md
docs/macos_scout/MACOS_OPTIMIZATION_BRIEF.md
docs/macos_scout/M3_MAX_128GB_CAPABILITY_NOTE.md
docs/macos_scout/MACOS_SCOUT_HARDENING_20260508.md
docs/macos_scout/TRANSFER_MANIFEST.md
tools/macos_scout/README.md
tools/macos_scout/Project.toml
tools/macos_scout/derivatives_scout.jl
tools/macos_scout/check_scout_regression_gate.py
tools/macos_scout/scout_regression_manifest.json
tools/macos_scout/metal_prefilter.jl
tools/macos_scout/metal_smoke.jl
tools/macos_scout/run_macos_scout.sh
tools/macos_scout/summarize_scout_outputs.py
tools/macos_scout/make_transfer_bundle.sh
```

Optional local smoke output from this machine:

```text
internal/macos_scout_runs/20260508_162505_smoke/
```

The smoke output is intentionally under `internal/` and should usually remain
uncommitted. It proves the scripts run, but the Mac should produce its own
authoritative run artifacts.

## Bundle Command

From repo root:

```bash
chmod +x tools/macos_scout/make_transfer_bundle.sh
bash tools/macos_scout/make_transfer_bundle.sh
```

The bundle will be written under:

```text
internal/macos_scout_transfer/
```
