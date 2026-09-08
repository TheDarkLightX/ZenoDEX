# Tau Swarm autonomy envelopes: normative contract and human/LLM workflow

Date: 2026-09-07. Status: original
experimental application, bounded local study. **Authority: NONE.** Nothing here
authorizes execution, deployment, money movement, credential use or Tau Net
submission. The commands in section 8 reproduce the bounded study; final
results and their source bindings are recorded in section 9.

## 1. Object of study

A *swarm problem* is a triple `(C, B, anchor)`:

* `C` is a Boolean contract over disjoint coordinate tuples `E` (environment,
  read only) and `X` (controls). Each requirement is an equation `r_i = 0`; the
  contract residual is `R = join_i r_i`, and a valuation is *legal* iff
  `R(v) = 0`.
* `B = (B_1..B_k)`, `1 <= k <= 16`, partitions `X` into named agent blocks.
* `anchor` maps every control to a term over `E` only. It is one
  environment-parametric seed valuation, not a SAT model: it must be legal for
  *every* environment.

An *autonomy envelope* is a tuple of local residuals `d_j` over `E + B_j` whose
zero sets `D_j(e)` are the permitted local choices.

### Normative guarantees (checked natively at compile time)

* **G1 Product safety.** `all E,X . (join_j d_j = 0) -> (R = 0)`. Every element
  of the Cartesian product `D_1(e) x ... x D_k(e)` is legal, for every `e`.
* **G2 Anchor retention.** `all E . join_j d_j[anchor] = 0`; the seed survives,
  so no domain is empty for any environment.
* **G3 Exact final universal cofactor.** For every `j`, `d_j = 0` is equivalent
  (as a formula over `E + B_j`) to
  `all (X \ B_j) . ((join_{i != j} d_i = 0) -> (R = 0))`.
  A local choice is permitted **iff** it is compatible with *every* choice still
  permitted to the others. This is factorwise inclusion-maximality: no single
  `D_j(e)` can be enlarged while keeping G1 with the other factors fixed.
* **G4 Scope.** `d_j` reads only `E + B_j`; no agent's rule mentions another
  agent's coordinate (checked structurally and re-checked on export).
* **G5 Independent recheck.** `check_bundle` re-evaluates every local domain and
  the *original* global contract before returning any bundle. Local permission
  is never accepted as a substitute for the global equation.
* **G6 Binding.** Each `LocalChoice` carries `envelope_id = subject_id`, a
  SHA-256 over the canonical semantic snapshot (contract, blocks, anchor,
  domains, expansion order), excluding runtime counters. Combination requires
  one subject, one shared environment tuple and one choice per block in block
  order.

### Explicitly not guaranteed

* **Not maximum volume.** G3 is a fixed point of factorwise enlargement, not a
  largest product. See section 5.
* No claim about generated code, agent behaviour, performance, admission to any
  network, or legal clearance.

## 2. Units and typing

Every declared coordinate is an **exact host boolean**. There is no arithmetic,
money, quantity, time series or probability in the represented contracts.
Constant terms have the form `{"kind": "constant", "value": true}` or the same
object with `false`. Integers, floats, `NaN`/`Infinity` tokens and strings in
constant position are rejected.
Environment flags are facts the swarm may read; controls are the only fields a
block owner may propose. Temporal liveness, signatures, custody and finality are
out of scope and would require separate contracts.

The JSON wire profile is bounded independently of the in-memory term model.
Encoding rejects a problem that exceeds the decoder's budget or whose terms
would change structurally on decoding. Accepted anchor objects are ordered by
the contract's controls. Nonconstant native projections have a local parser
bound of 64 environment-plus-owned aliases, 4,096 bytes, 256 nodes and depth 64;
other expression and runtime budgets also apply. Optional exhaustive inspection
is limited to ten control bits. Compilation itself does not enumerate the
global Boolean assignment space.

## 3. Neuro-symbolic story: an authorized breaking API change

A person (the developer) decides policy; three model agents propose flags.

1. **The person authorizes.** They set the environment flag
   `allow_breaking = true`. This is a human decision recorded as data, not a
   permission granted to any agent.
2. **Disjoint ownership.** `schema` owns `breaking, additive`; `client` owns
   `upgrade, shim`; `verification` owns `regression, migration`. The partition
   is checked: overlapping or missing controls are rejected before any native
   call.
3. **The person chooses priority and seed.** The expansion order
   (`--order schema,client,verification`) and the anchor are human choices.
4. **Compile once, then choose locally.** The compiler emits one residual per
   agent plus a standalone `.tau` gate. Each agent evaluates only its own gate:
   inputs are streamed in `environment ++ owned controls` order, and the single
   output `o1` is 1 exactly when the local choice is formally compatible.
   Local evaluation needs only that agent's coordinates and the shared
   environment. This prototype does not measure communication savings or
   establish confidentiality of another agent's rules.
5. **Combine.** `combine_choices` requires the same `subject_id` and the same
   environment tuple from all three, then re-checks locally *and* against the
   original global contract (G5).
6. **If the formal contract changes, recompile.** The subject id changes, and
   choices bound to the old id are refused. There is no partial upgrade path.
7. **The actual code is still verified separately.** These are planning flags.
   Nothing here checks that the emitted migration or shim code is correct.

### The 3-versus-12 autonomy tradeoff

With `allow_breaking = true` the schema-first order yields **3** independent
combinations; the verification-first order yields **12**. Both are safe (G1) and
both are factorwise maximal (G3). Schema-first grants the schema block the
freedom to say `breaking`, and that single freedom forces `client = {upgrade}`
and `verification = {regression, migration}` for *everyone*. Verification-first
commits the verification block early, which removes `breaking` from the schema
block's local domain and leaves the other two blocks broader. With
`allow_breaking = false`, both orders yield 12, and `breaking` is unavailable in
both: the human flag, not the agent, decides that.

The globally feasible valuation counts are **15** (`allow_breaking = true`) and
**14** (`false`). In this example, the chosen product admits a strict subset of
the globally feasible plans: 3 or 12 of 15 when breaking changes are permitted.
The inspection report states both numbers side by side so the person can see the
cost of the priority they picked.

## 4. Universal compatibility

A tempting shortcut is to give each agent every choice that participates in
*some* legal global valuation (an existential projection). That is unsound for
independent choosing. In `asymmetric_choices` (`a&(b|c) | b&c = 0`) every value
of `a` and each of `(b,c) in {(0,0),(0,1),(1,0)}` occurs in a legal valuation,
so the existential product admits six combinations, but `(1,0,1)` and `(1,1,0)`
are illegal: the exact joint relation admits four. Our cofactor is therefore
**universal** over the other blocks' *current domains*, which is exactly the
condition `all others . (others admitted -> global legal)`.

Equally, expansions must be **sequential on the current state**: computing every
block's expansion against the same stale snapshot and merging them reproduces
the unsafe six-combination product. Each expansion is committed before the next
cofactor is formed.

## 5. Inclusion maximality is not maximum volume

`triangle_choices` has two two-bit agents and six allowed code pairs
`{(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)}`. From the all-zero anchor, both orders
reach a product of size 3 (`{0,1,2} x {0}` or its mirror). Both are
inclusion-maximal: no factor can be enlarged. Yet the anchor `(1,1)` yields
`{0,1} x {0,1}`, size **4**, which our exhaustive tiny-product oracle confirms is
the maximum. So the seed, not only the order, selects the fixed point, and
**searching every order does not repair it**. We claim maximality, never
maximum volume, and the tools repeat this in `nonclaims`.

## 6. Failure, UNKNOWN and recovery

* Malformed data (bad container, unknown field, duplicate JSON key at any depth,
  non-boolean constant, foreign or missing anchor control, anchor reading a
  control, non-permutation order, oversize input, existing `--out` directory) is
  **invalid input, exit 2**. Incidental `TypeError`, `RecursionError` and
  Unicode errors are normalized to `ValueError` so callers see one class.
* A missing binary path is **invalid input, exit 2**. Native execution failures,
  timeouts, unsupported queries, non-equivalent
  projections and expression growth are **UNKNOWN, exit 3**. UNKNOWN never
  degrades to a permissive answer: no envelope is issued and no artifact is
  written.
* Completed runs are **exit 0**; the benchmark adds **exit 1** for oracle
  disagreement or detected source drift (FAIL), retaining a failed replay
  record. A missing required source is invalid input before execution.
* Recovery: supply an explicit compatible Tau binary, reduce or repair the
  input, pick a different anchor or order, and retry into a *fresh* directory.
  Existing directories are never overwritten.

## 7. Artifacts and ownership

`compile --out DIR` writes `problem.json`, `report.json`, `native_queries.json`,
per-agent `agent_NN.tau` and `agent_NN.contract.json`, and `inspection.json`
when `--environment` is given. Each gate is a generic local stream artifact:
many input streams, one output stream, generator-owned symbol names, no
caller-supplied Tau text, and a header stating `authority: NONE`. Gate SHA-256
hashes and input order are recorded in the report so a reviewer can bind a file
to a report line. The benchmark additionally freezes all dependency source
hashes plus the Tau binary hash, re-checks the hashes after the replay, and
fails if any source changed during the run. These are unsigned observations.
The CLI report identifies the semantic problem and gate bytes; it is not a
complete authenticated manifest of every auxiliary artifact. No report loader
grants authority. File output uses a fresh directory and is not an atomic
publication transaction; an IO failure can leave partial files for inspection.

## 8. Commands

```
python tools/tau_swarm.py describe
python tools/tau_swarm.py example triangle --balanced-anchor
python tools/tau_swarm.py compile --example planning \
    --order schema,client,verification --environment '{"allow_breaking": true}' \
    --tau /path/to/tau --out artifacts/planning
python tools/tau_swarm.py compile --problem my_problem.json --tau /path/to/tau
python tools/benchmark_tau_swarm.py --tau /path/to/tau --out artifacts/bench
python -m pytest tests/test_tau_swarm_codec.py tests/test_tau_swarm_cli.py \
    tests/test_tau_swarm_inspection.py tests/test_tau_swarm.py
```

## 9. Evidence scope

| Layer | What exists | What it does not establish |
| --- | --- | --- |
| Python implementation | Codec, compiler, exporter, inspection, CLI, benchmark in this repository | No proof that Python refines the Lean model |
| Focused combined suite | **190 passed in 33.92s**, with native tests enabled: 68 composition tests and 122 swarm tests. Includes single-agent exactness, 65-coordinate local-projection capacity, malformed input, rejected projection mutants, binding, codec, CLI and gate replay | Bounded regressions and parity checks; no repository-wide acceptance |
| Lean | Conditional theorem in `Proofs/TauSwarmAutonomy.lean` checked under Lean 4.27 in the parent lake environment | Conditional on its hypotheses; not connected to the Python or native code |
| Final experiment | **PASS:** seven cases, nine environment slices, 320 Boolean oracle rows, 84 native gate trace rows, 39 exclusion witnesses, 87 native query/execution records; 30 source hashes match | Fixed relations only; no real LLM productivity or general performance result |
| Existing Tau gates | Supported-runtime subset, Tau spec assurance test, and claims-registry check passed | New generic gates remain outside the mounted network profile |
| Tau Net | Not mounted; `runtime_mounted` is `false` everywhere | No admission, no rule-offer semantics, no settlement |

The final experiment took 10.92 seconds in this local run. The measured choice
counts confirm sections 3 and 5, including the independent finite oracle's
maximum product sizes. This oracle is exhaustive only for the declared tiny
examples. It is not a general maximum-product implementation.

See the [final replay report](tau_swarm_20260907/replay/report.json),
[validation record](tau_swarm_20260907/validation.json),
[core review](tau_swarm_20260907/core_review.md), and
[Opus integration review](tau_swarm_20260907/integration_review.md).
Whole-repository tests and MyPy, a full Lean build, the TLA model fleet, RISC0
checks and Tau Net node integration were not run for this bounded study.

The binary used in the final local run reports `0.7.0-alpha (d80aa50c)`, SHA-256
`b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`. The
source-to-binary build correspondence is **unestablished**. Native agreement plus
a Lean theorem does not prove refinement between the Python code, the compiler
and the native engine.

## 10. Prior art and boundaries

* Ignatov, *On closure operators related to maximal tricliques in tripartite
  hypergraphs*,
  <https://arxiv.org/pdf/1602.07267>, section 4, directly gives the sequential
  polyadic concept expansion we use; our sweep is that construction, applied to
  environment-parametric coordination of disjoint agent choices.
* Rudolph, Sacarea, Troanca, *Conceptual Navigation for Polyadic Formal Concept
  Analysis*, on proper n-concepts as maximal products,
  <https://www.cs.ubbcluj.ro/~dianat/publications/camera_ready_submission1_Rudolph_Sacarea_Troanca.pdf>
  gives the maximal-product characterisation corresponding to G3.
* Rudell, *Multiple-Valued Logic Minimization for PLA Synthesis*, ERL-86-65,
  <https://www2.eecs.berkeley.edu/Pubs/TechRpts/1986/ERL-86-65.pdf>, section
  4.3.6, explains that full-block expansion can miss larger products even when
  all orders are tried. This is prior art for the limitation in section 5.

This is an original application implementation using established mathematics:
environment-parametric local choice gates for a human-directed swarm, with
independent global recheck and explicit UNKNOWN results. Historical novelty of
the application and any advance in Tau's underlying decision procedure are
unestablished.

Custom Tau Lang / Tau Net licenses are separate from this repository. This
application uses a **separately installed** binary. It vendors no Tau Lang or
Tau Net source, binaries or parsing library; the host term parser was written
for this application. Operating that separately installed software remains
subject to its applicable terms. Patent freedom-to-operate is **not
established**. See the [first-cycle source and license study](tau_composition_20260907.md)
for the researched boundaries. No legal or production clearance is claimed.

## 11. Next practical experiment

Evaluate a developer and their swarm on fixed API-change tasks with an
independently checked artifact contract. Compare completed accepted tasks,
human corrections and renegotiations with centralized per-proposal checking.
The present compiler operates on planning flags; connecting flags to actual
code and test evidence is the next missing link. Seed and order selection can
be model-assisted, while native compatibility and the final code checker
remain the acceptance gates.
