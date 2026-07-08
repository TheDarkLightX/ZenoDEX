# ZenoDEX Research Kernel Frontier Hygiene - 2026-06-28

## Executive Result

Five locally replayed ZenoDEX research artifacts now form an explicit closure map for stale or bounded Research Kernel frontier items.
The map is intentionally narrow: it records which supported local evidence resolves or bounds a surfaced frontier atom, then emits the RK edges that should be added.
Research Kernel edge types use `SUPERSEDES` for stale `UNDER_TEST` frontier items and `SPECIALIZES` for the bounded AB candidate; the local `closure_kind` field preserves the resolves/bounds semantics.

- Closure rows: `5`
- Stale `UNDER_TEST` risks closed or bounded: `3`
- Resolved rows: `2`
- Bounded rows: `2`
- Local supported frontier extension rows: `1`

## Closure Map

| frontier atom | closure kind | local resolver |
| --- | --- | --- |
| `atom_db8d68413cd34328` | `resolves` | `negative_frontier_exact_scheduler_v1` exhaustive scheduler certificate |
| `atom_2d749c2ecd2e4c9a` | `bounds` | route split-window hostile corpus and Tau ablation replay |
| `atom_86d2810ce9ad4b50` | `resolves` | `cpss_bc_research_scope_certificate_v1` scope certificate |
| `atom_28ea53e1ebcc4f97` | `bounds` | `ab_subset_dp_dominance_certificate_v1` scoped dominance boundary |
| `cow_capacity_grouped_frontier_20260628` | `supports` | `cow_capacity_dp_certificate_v1` grouped-capacity CoW exact-DP certificate |

## Why This Matters

Research Kernel was still surfacing old risk atoms whose local evidence had already been improved by later artifacts.
The hygiene receipt makes the compounding path explicit:

1. stale entropy-scheduler refutation risk -> exact bounded scheduler certificate;
2. route split-window ablation risk -> hostile corpus with oracle parity and negative knowledge;
3. CPSS-BC overclaim risk -> scope certificate with Lean/Tau evidence and non-claims;
4. Held-Karp AB candidate -> scoped dominance boundary with exact-out and mixed-direction counterexamples;
5. uncoupled CoW matching frontier -> bounded grouped-capacity DP extension.

## Replay

Fast check over existing generated reports:

```bash
python3 tools/check_research_kernel_frontier_hygiene_20260628.py
```

Rebuild prerequisite reports first:

```bash
python3 tools/check_research_kernel_frontier_hygiene_20260628.py --refresh
```

Focused test:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/tau/test_research_kernel_frontier_hygiene_20260628.py
```

## Non-Claims

- This receipt does not mutate Research Kernel frontier ranking by itself; explicit RK edges are required.
- This receipt does not rerun every underlying proof by default; use `--refresh` to rebuild prerequisite reports.
- This receipt records research-evidence closure only and grants no settlement, governance, state-root, or production authority.
- Generated report JSON files are replay outputs; tracked source artifacts and replay commands are the durable evidence handles.
