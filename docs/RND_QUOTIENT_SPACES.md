# Quotient Spaces for ZenoDEX: Intent Normal Forms + Certified Batch Clearing (R&D)

This memo records research results and concrete next steps for using **equivalence relations / quotient spaces**
to (a) compress the effective state space we reason about, and (b) make batch clearing **proof-/certificate-carrying**.

## 1) Why quotient spaces matter for a DEX

A DEX has a huge state space because:
- many orderings of the “same” batch exist (mempool / block builder permutations),
- many interleavings of independent actions exist (different pools, different accounts),
- many micro-variations are semantically irrelevant for a chosen property (e.g., “same post-state up to dust”).

If we define an **equivalence relation** `~` on states/traces/batches that preserves the properties we care about,
we can work on the smaller quotient space `X/~`:
- fewer cases to test/explore,
- simpler proofs (prove invariants on canonical representatives),
- clearer MEV surface (what *shouldn’t* matter becomes formally unexploitable).

ZenoDEX already has the right scaffolding for this direction:
- an **intent lattice** where “equivalence” is the top assurance layer (`docs/INTENT_LATTICE.md`),
- a kernel workflow that already proves forward/no-extra **equivalence** properties (`docs/KERNEL_VERIFICATION_STATUS.md`),
- a proof verifier interface designed for **proof-carrying settlement** (`src/integration/proof_verifier.py`).

## 2) Design pattern: Normal forms as quotients

Instead of letting *every* representation of a “batch” be admissible, pick a **canonical representative**
(a *normal form*) for each equivalence class and require/verify it:

`batch  ~  batch'    ⇔    normal_form(batch) == normal_form(batch')`

That turns “reason about all permutations/interleavings” into “reason about one normal form”.

### Normal forms via rewriting (Church-Rosser intuition)

If you can express transformations of a batch/trace as rewrite rules (swap commuting steps, reorder by key, etc.),
and the rewrite system is confluent (Church-Rosser), then every object has a unique normal form.

Reference (rewriting modulo equivalence): Ohlebusch et al., 1998
https://doi.org/10.1007/BFb0052358

## 3) Candidate equivalence relations that are high-value for ZenoDEX

### A) Permutation quotient (batch order canonicalization)

**Goal**: treat any permutation of a batch submission as the same economic object.

Concrete: define a canonical order over intents (by pool, by side/price, by intent_id; LP by FIFO index).
This aligns with the “deterministic ordering for MEV resistance” kernel intent (`src/kernels/dex/batch_order.yaml`).

This memo’s implementation bet: add an explicit `intent_normal_form` module and enforce it in proof verification.

### B) Commutativity quotient (partial-order reduction)

If two actions commute (apply in either order yields equivalent post-state w.r.t. tracked observables),
then many interleavings collapse into one.

This is exactly the motivation behind partial-order reduction in model checking.
References:
- Flanagan & Godefroid, 2005 (DPOR) https://doi.org/10.1145/1040305.1040315
- Rodríguez et al., 2015 (unfolding-based POR) https://doi.org/10.4230/LIPIcs.CONCUR.2015.456

For a DEX, commutativity is *conditional* (shared user balances / shared pool reserves break independence),
but there are still useful conservative commuting relations (e.g., disjoint users *and* disjoint pools).

ZenoDEX implementation hook:
- `src/core/intent_access.py` computes conservative read/write access sets and partitions batches into
  independent (non-conflicting) components; this is the starting point for DPOR-style reductions and
  per-component certificates.

### C) Symmetry quotient (renaming / indistinguishable agents)

For many safety properties, user identities don’t matter beyond “same/different”. If so, quotient by renaming.

Reference example in model checking practice: Gibson-Robinson et al., 2019
https://doi.org/10.1007/s10009-019-00516-4

### D) “Dust equivalence” quotient (rounding / fee dust)

If the protocol intentionally allows multiple representations that differ only by bounded rounding/dust,
define an equivalence relation for “same outcome up to dust bounds” and prove invariants on that quotient.

This is especially relevant given ZenoDEX’s deterministic rounding + dust-carry style fee kernels.

### E) Settlement ordering quotient (commitment normal forms)

Many settlement fields are order-insensitive with respect to state transition (delta lists). A useful quotient is:

`settlement ~ settlement'  ⇔  normalize(settlement) == normalize(settlement')`

ZenoDEX implementation:
- `src/core/settlement_normal_form.py` defines a canonical ordering for commitments/comparisons.
- `tools/proof_verifiers/recompute_batch_v4.py` uses this to make batch commitments stable across
  equivalent encoders (deltas reordered, etc.).

## 4) Certified batch clearing as “proof-carrying computation”

The core idea is simple:
1) off-chain compute settlement (potentially via optimization),
2) attach a proof/certificate,
3) validators verify it fail-closed.

Classic reference: Necula, “Proof-carrying code” (1997)
https://doi.org/10.1145/263699.263712

### Practical phase-1: “recompute proof” (fast to ship, not ZK)

For immediate R&D velocity, a verifier can:
- validate the batch is in **intent normal form**,
- recompute settlement from a committed pre-state + committed batch,
- check equality with the settlement committed in the batch commitment.

This is not ZK, but it is a **certificate** in the sense of independently checkable computation,
and it plugs directly into ZenoDEX’s existing proof verifier interface.

### Phase-1b: quotient pre-state commitments (“support roots”)

Recompute proofs still need a pre-state commitment. If that commitment is the *full* state root,
then the witness must carry the *full* snapshot, which is often too large.

Quotient idea: define a projected commitment over the batch’s **support** (read-set). Two global
states are equivalent if they agree on that support; the verifier only needs the projected snapshot.

ZenoDEX implementation:
- `src/state/support_root.py` (support derivation + `state_support_root` hash)
- `tools/proof_verifiers/recompute_batch_v3.py` / `tools/proof_verifiers/recompute_batch_prover_v3.py`

### Phase-2: “compressed certificate”

To go beyond recomputation, emit a smaller witness that is cheaper to validate than recomputing:
- per-pool step certificate (reserves-before/after + swap math checks),
- dual variables / KKT-style certificates if we adopt convex clearing (see below),
- kernel-level certificates stitched together (batch order + swap math + conservation).

## 5) “Convex clearing” direction (optional, deeper R&D)

Constant function market makers can be expressed as convex programs; this gives a path to *optimality certificates*
via KKT conditions (when the program is convex).

References:
- Angeris et al., 2021 https://doi.org/10.48550/arXiv.2107.12484
- Angeris et al., 2023 https://doi.org/10.1145/3670865.3673500

MEV framing:
- Daian et al., 2020 https://doi.org/10.1109/SP40000.2020.00040
- Kulkarni et al., 2022 https://doi.org/10.48550/arXiv.2207.11835

Sequencing-rule framing:
- Ferreira & Parkes, 2022 https://doi.org/10.1145/3564246.3585233
- Budish et al., 2015 (batch auctions) https://doi.org/10.2139/ssrn.2388265

## 6) Actionable bets (what we should implement now)

1) **Intent Normal Forms (batch canonicalization)**
   - Define a canonical ordering and a verifier that enforces it.
   - Treat “non-normal-form batch” as invalid for proof-carrying settlement.

2) **Certified Batch Clearing v0 (recompute-proof)**
   - Implement a reference proof verifier that consumes:
     - committed pre-state (snapshot),
     - committed batch (intents + settlement),
     - and checks settlement correctness by recomputation + conservation validation.
   - This provides an end-to-end “proof-carrying” pipeline today.

3) **Next: certificate compression**
   - Replace recomputation with a per-pool step certificate (or convex/KKT proof).
   - Use quotient ideas (normal forms / commutativity) to shrink witness size.

## 7) Extra security/robustness reference

Adversarial synthesis against AMMs:
- Han et al., 2024 https://doi.org/10.1145/3728872
