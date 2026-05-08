# M3 Max 128GB Capability Note

Date checked: 2026-05-08.

## What The Machine Can Do For This Work

The 128GB M3 Max Mac is a strong local research box for ZenoDEX scout campaigns.
It is especially useful for large in-memory datasets, deterministic Julia
simulation, parallel CPU fuzzing, local LLM-assisted review, Lean builds, and
long-running proof or property-test batches.

Based on Apple documentation, the relevant expected ceiling is:

- up to 128GB unified memory on M3 Max with 16-core CPU;
- M3 Max configurable to 16-core CPU and 40-core GPU;
- 400GB/s memory bandwidth for the 16-core CPU, 40-core GPU M3 Max variant;
- Apple Silicon GPU support through Metal, with M3-series listed for Metal 3 and
  Metal 4 feature availability;
- Julia GPU experimentation available through Metal.jl, although it should be
  treated as optional until the local stack is smoke-tested.

## Best Local Jobs

Use the Mac first for:

- CPU-threaded Julia sweeps over derivatives and funding parameters;
- Monte Carlo stress paths with large retained counterexample corpora;
- long Hypothesis/property-test campaigns;
- Lean/lake proof builds and proof-search experiments;
- ESSO/Morph CPU campaigns where many seeds matter more than CUDA;
- local artifact distillation before spending remote GPU money.

## Jobs That Still Prefer Runpod

Use Runpod later for:

- CUDA-specific ZK prover benchmarking;
- massive GPU vector sweeps after the Mac finds promising candidates;
- campaigns that need many independent workers for a short wall-clock window;
- jobs that explicitly require NVIDIA CUDA libraries.

## Recommended Local Strategy

Start CPU-first:

```text
smoke -> scout -> deep -> rerun winners with new seed -> promote tests
```

Only use Metal after a smoke test:

```text
MetalOK := Metal.versioninfo succeeds and a small MtlArray computation roundtrips
```

If Metal is unstable, continue with CPU. The 128GB memory budget is the main
advantage for this phase because it lets the Mac retain larger corpora,
counterexamples, and intermediate search objects than typical laptops.

## Sources

- Apple MacBook Pro tech specs: https://support.apple.com/en-us/117736
- Apple M3 family announcement: https://www.apple.com/newsroom/2023/10/apple-unveils-m3-m3-pro-and-m3-max-the-most-advanced-chips-for-a-personal-computer/
- Apple Metal feature tables: https://developer.apple.com/metal/capabilities/
- Metal.jl home: https://metal.juliagpu.org/stable/
- Metal.jl overview: https://metal.juliagpu.org/stable/usage/overview/
