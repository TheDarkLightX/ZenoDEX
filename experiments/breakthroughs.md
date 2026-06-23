# Math Research Breakthroughs

Mirror of `experiments/math_research_memory/breakthroughs.md`.

## ZenoHypergraph v0 Survivor

The v0 bounded cycle found a useful representation survivor:

```text
orders x price_grid -> canonical typed hypergraph -> row scores -> canonical winner
```

The survivor is exact on the bounded test domain and has a GPU/FHE-shaped
execution plan:

```text
map order-price edges
scan row aggregates
compact canonical winner
```

The negative result is equally important: a naive sequence root changes under
order permutation, so it is a poor representation for UPBA semantics.
