# MetaMuse Zenith/Morph Workflow

This repo now carries a thin MetaMuse-style workflow layer instead of a separate research stack.
It reuses the existing supervised runner and `tools/zenodex_autonomous_checks.py` while forcing algorithm ideation through explicit waypoints.

## Stages

1. Problem state
- Record `R, α, Δ, G, Π` for the lane.
- `R`: representation
- `α`: abstraction level
- `Δ`: constraints and invariants
- `G`: optimization or proof goal
- `Π`: obligations that must be discharged before promotion

2. Waypoints
- extract invariants
- enumerate baseline families and failure modes
- choose reformulation axes
- select external stimuli
- synthesize candidate principles
- normalize into hypothesis cards
- define falsification and support recipes

3. External stimuli
- data-structure motifs
- control/quasi-concavity analogies
- adversarial plateau views
- amortization or cache-aware probes
- certificate / tie-break structure

4. Rules-decide evaluation
- falsification first
- support second
- promote only with replayable artifacts
- `UNKNOWN`, `TIMEOUT`, and `ERROR` are inconclusive

5. Archive
- winning ideas
- minimal counterexamples
- failed reformulations
- proof obligations that blocked promotion

## Repo Artifacts

- Lane spec and curated corpus: `tools/metamuse_split_routing_lane.py`
- Workflow runner: `tools/zenodex_metamuse_workflow.py`
- Prompt template: `tools/metamuse/agent_prompt.md`
- Schemas:
  - `tools/metamuse/hypothesis_card.schema.json`
  - `tools/metamuse/epoch_packet.schema.json`

## JSON-RPC Shape

These methods are the intended integration boundary even though the current implementation is file-based.

### `metamuse.epoch.plan`
Input:
```json
{
  "lane": "split_routing_exact_in_dgstr"
}
```
Output:
```json
{
  "lane": {"lane_id": "split_routing_exact_in_dgstr"},
  "waypoints": {},
  "stimuli": [],
  "hypotheses": []
}
```

### `metamuse.epoch.run`
Input:
```json
{
  "lane": "split_routing_exact_in_dgstr",
  "run_checks": true,
  "out_dir": "runs/metamuse/split_routing_exact_in_dgstr"
}
```
Output:
```json
{
  "ok": true,
  "out_dir": "...",
  "summary": {},
  "analysis": {}
}
```

### `metamuse.archive.append`
Input:
```json
{
  "lane": "split_routing_exact_in_dgstr",
  "hypothesis_id": "split_dgstr_v1",
  "status": "supported",
  "artifacts": ["runs/.../summary.json"]
}
```

## First Lane: DGSTR Split Routing

The first integrated lane targets exact-in split routing for two CPMM pools.

Current bounded claims:
- `dgstr_v1` is experimental, not the default profile.
- `adaptive_v7` keeps `adaptive_v6` hard-regime escalations and only routes easy manifolds to `dgstr_v1`.
- Promotion evidence is bounded to the curated corpus and quote-call comparison checks.

## How To Run

Dry run:
```bash
python3 tools/zenodex_metamuse_workflow.py \
  --lane split_routing_exact_in_dgstr \
  --out-dir runs/metamuse/split_routing_exact_in_dgstr
```

With support/refute checks:
```bash
python3 tools/zenodex_metamuse_workflow.py \
  --lane split_routing_exact_in_dgstr \
  --out-dir runs/metamuse/split_routing_exact_in_dgstr \
  --run-checks
```

The runner emits:
- `epoch_packet.json`
- `waypoints.json`
- `stimuli.json`
- `hypotheses.json`
- `curated_corpus.json`
- `result.json`
