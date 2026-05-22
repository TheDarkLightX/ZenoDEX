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

- Lane specs and curated corpora:
  - `tools/metamuse_split_routing_lane.py`
  - `tools/metamuse_batch_ordering_lane.py`
  - `tools/metamuse_burn_receipt_lane.py`
  - `tools/metamuse_exact_out_lane.py`
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

## Current Lanes

### DGSTR Split Routing
- Targets exact-in split routing for two CPMM pools.
- Current bounded claims:
  - `dgstr_v1` is experimental, not the default profile.
  - `adaptive_v7` keeps `adaptive_v6` hard-regime escalations and only routes easy manifolds to `dgstr_v1`.
  - Promotion evidence is bounded to the curated corpus and quote-call comparison checks.

### MCI Batch Ordering
- Targets same-direction exact-in batch ordering.
- Adds `mci_ab_global`, an experimental marginal-contribution insertion seed ahead of the existing global AB refinement.
- Promotion evidence is bounded to a curated witness family checked against `optimal_ab_bounded`.

### Burn Receipt Kernel
- Targets audited buyback/burn accounting rather than routing or execution quality.
- Adds a decomposed burn-receipt rail family: replay guard, amount guard, supply guard, and batch-sum guard.
- Promotion evidence is bounded to curated replay/accounting cases plus Tau production traces.

### Exact-Out Multihop Value
- Targets exact-out routing research.
- Adds a witness lane proving that 2-hop exact-out can strictly beat direct exact-out on a replayable topology.
- Promotion evidence is bounded to dual-checked Python + Z3 witness replay, not a new runtime router.

## How To Run

Dry run:
```bash
python3 tools/zenodex_metamuse_workflow.py \
  --lane batch_ordering_mci_ab \
  --out-dir runs/metamuse/batch_ordering_mci_ab
```

With support/refute checks:
```bash
python3 tools/zenodex_metamuse_workflow.py \
  --lane burn_receipt_kernel_v1 \
  --out-dir runs/metamuse/burn_receipt_kernel_v1 \
  --run-checks
```

The runner emits:
- `epoch_packet.json`
- `waypoints.json`
- `stimuli.json`
- `hypotheses.json`
- `curated_corpus.json`
- `result.json`
