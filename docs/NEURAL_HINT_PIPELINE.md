# Neural-Guided Synthesis for ESSO

## Latest: Batch Automation with Two-Stage Model Selection (2026-01-01)

### Model Comparison Results

| Hole Spec | 7B Result | 80B Result | Winner |
|-----------|-----------|------------|--------|
| fee_accumulator | `(+ accumulated fee_amount)` + guards | `(+ accumulated fee_amount)` | Both OK |
| swap_fee_calculator | Complex nested ite | `(safe_div (* amount_in fee_bps) 10000)` | **80B** |
| lp_mint_optimal | Missing inputs entirely | `(ite (<= (* amount0 lp_supply) (* reserve0 amount1)) ...)` | **80B** |
| cpmm_output_amount | `(safe_div (* reserve_out net_in) ...)` | Same | Both OK |

**Key Finding**: 80B dramatically outperforms 7B on complex formulas requiring:
- Multi-variable comparisons (min formula)
- Cross-multiplication logic
- Correct variable usage from context

### Architecture: Two-Stage Model Selection

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│ Hole Specs      │────▶│ Stage 1: 7B      │────▶│ Valid hint?     │
│ (9 specs)       │     │ (fast, ~10s)     │     │                 │
└─────────────────┘     └──────────────────┘     └────────┬────────┘
                                                          │
                              ┌────────────────┐          │ No
                              │ Stage 2: 80B   │◀─────────┘
                              │ (accurate, ~30s)│
                              └────────┬───────┘
                                       │
                              ┌────────▼────────┐
                              │ ESSO Synthesis  │
                              │ + ICE Verify    │
                              └─────────────────┘
```

### Batch Command Usage

```bash
# Two-stage batch (7B first, 80B fallback)
PYTHONPATH=external/ESSO external/ESSO/.venv/bin/python \
  tools/esso_mlx_hints.py batch src/kernels/dex \
  --samples 3 \
  --two-stage \
  --validate cheap

# Report on results
python tools/esso_mlx_hints.py report runs/ngs/<run_id>
```

### Validation Tiers

1. **none**: No validation, fastest
2. **cheap**: Parse + grammar check via ESSO hint loader (~100ms)
3. **full**: Run ESSO synth in hint-only mode (~5s)
4. **examples**: Batched semantic check vs `*_ref.yaml` (Torch MPS/CUDA when available)

### Aggregation Strategy

When multiple samples generate candidates, the aggregator picks best by:
1. Full validation passed > Cheap validation passed
2. Higher frequency (self-consistency across samples)
3. Lower complexity (shorter expressions preferred)
4. Earlier position (first candidate gets slight boost)

---

## Experiment Results (2026-01-01)

### Success: MLX 80B Model Integration

**Model**: Qwen3-Next-80B-A3B-Instruct (49GB, 11 safetensors shards)
**Backend**: MLX (Apple Silicon optimized)
**Test**: `fee_accumulator_simple_hole.yaml`

**Results**:
- Model loaded successfully on M3 Max
- Generated correct candidate: `(+ accumulated fee_amount)`
- ESSO synthesis verified with hints
- End-to-end pipeline operational

### Pipeline Architecture

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│ Hole Spec       │────▶│ LLM Hint         │────▶│ ESSO Synth      │
│ (YAML + synth)  │     │ Generator        │     │ (verify + ICE)  │
└─────────────────┘     └──────────────────┘     └─────────────────┘
                              │
                              ▼
                        ┌──────────────────┐
                        │ llm_hints.json   │
                        │ - model_hash     │
                        │ - synth_hash     │
                        │ - holes: {...}   │
                        └──────────────────┘
```

### Hint Format (ESSO v1)

```json
{
  "schema": "esso-llm-hints/v1",
  "model_hash": "sha256:...",
  "synth_hash": "sha256:...",
  "holes": {
    "hole_id": {
      "term": "(+ accumulated fee_amount)",
      "source": "mlx:model-name",
      "rank": 0
    }
  }
}
```

**Critical**: `holes` must be an object (not array), with hole IDs as keys.

## Tools Created

| Tool | Backend | Description |
|------|---------|-------------|
| `tools/esso_mlx_hints.py` | MLX (Apple Silicon) | 7B/80B local, batch, two-stage |
| `tools/esso_neural_hints.py` | Transformers | HuggingFace models |
| `tools/llm_hint_generator.py` | Ollama CLI | Local Ollama |
| `tools/llm_hint_generator_openai.py` | OpenAI API | LM Studio/vLLM |
| `tools/esso_gpu_semantic_check.py` | Torch (MPS/CUDA) | Batched semantic checker vs `*_ref.yaml` |

## Commands Reference

```bash
# Single spec with specific model
python tools/esso_mlx_hints.py hints-only \
  src/kernels/dex/hole_spec.yaml \
  src/kernels/dex/hole_spec.synth.json \
  --mlx-model /path/to/model \
  --samples 3 \
  --temp 0.7 \
  --validate cheap

# Batch all specs
python tools/esso_mlx_hints.py batch src/kernels/dex \
  --samples 3 \
  --two-stage \
  --validate cheap \
  --output runs/ngs/my_run

# Batch with example-based validation (requires <prefix>_ref.yaml per hole spec)
python tools/esso_mlx_hints.py batch src/kernels/dex \
  --samples 3 \
  --two-stage \
  --validate examples

# Generate report
python tools/esso_mlx_hints.py report runs/ngs/my_run

# Full synthesis with hints
python tools/esso_mlx_hints.py synth \
  src/kernels/dex/hole_spec.yaml \
  src/kernels/dex/hole_spec.synth.json \
  --output runs/synth_result
```

## Model Configurations

### Available Models

| Model | Path | Size | Speed | Accuracy |
|-------|------|------|-------|----------|
| Qwen3-80B | `/Users/danax/projects/TCEModel/models/Qwen3-Next-80B-A3B-Instruct-qx64-mlx` | 49GB | ~30s | High |
| Qwen2.5-7B | `/Users/danax/projects/TCEModel/models/Qwen2.5-7B-Instruct` | ~5GB | ~10s | Medium |

### When to Use Each

- **80B**: Complex formulas, min/max, cross-multiplication, multi-variable
- **7B**: Simple accumulation, basic arithmetic, fee calculations
- **Two-stage**: Best of both - speed for easy, accuracy for hard

## Improvement Plan

### Phase 1: Completed - Model Comparison
- 80B vs 7B accuracy analysis
- Batch automation implemented
- Two-stage selection working

### Phase 2: In Progress - Validation Integration
- Cheap validation via ESSO hint loader
- Full validation via hint-only synthesis
- Aggregation across samples

### Phase 3: Planned - Grammar-Aware Prompting
- Include grammar productions in prompt
- Train/fine-tune on verified ESSO solutions
- Implement grammar validation before Z3

### Phase 4: Future - Feedback Loop
- Capture failed hints for training data
- Implement RLHF from Z3 verification results
- Build hint quality scoring

## Research Findings (SOTA 2024-2025)

From academic literature:
1. **NGDS (Microsoft)**: 67% speedup with neural guidance
2. **LLM-predicted grammars**: Shrink search space by pruning productions
3. **EcoSearch**: Efficient candidate ranking
4. **FVEL**: Formal verification enhanced learning
5. **Lemur**: Language model unified representations

Key insight: **Quantity beats quality** - generate many candidates, let Z3 verify.

## Known Issues

1. **Weak semantic constraints**: Some specs allow trivial solutions
   - Fix: Tighten constraints to require actual computation

2. **MLX requires GUI context**: Metal GPU access blocked in headless mode
   - Fix: Disable sandbox or run from Terminal
   - Note: Torch MPS (used by `--validate examples`) has the same limitation

3. **Hash computation**: Must use ESSO's internal hash functions
   - Implemented in `compute_esso_hashes()`

4. **7B overfitting to guards**: Smaller models add unnecessary ite guards
   - Fix: Use aggregation to prefer simpler terms
