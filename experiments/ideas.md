# Math Research Ideas

Mirror of `experiments/math_research_memory/ideas.md`.

## ZenoHypergraph UPBA IR

Use a typed finite hypergraph as the shared representation for bounded UPBA
candidate evaluation. The first object is an order-price incidence hypergraph:

```text
OrderPrice(order, price_row) -> accepted flag, signed deltas, surplus contribution
```

Why it matters: the same object can target public Python verification, ZK
execution proofs, FHE private batch-clearing experiments, and Tau Tables facts.

Next frontier: padding neutrality, partial fills, exact-out orders, encrypted
mask semantics, and hypergraph-root binding in the settlement envelope.
