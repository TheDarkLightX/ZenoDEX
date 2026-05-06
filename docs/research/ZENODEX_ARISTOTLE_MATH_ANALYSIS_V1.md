# ZenoDEX Aristotle Math Analysis v1

Status: analysis receipt for Aristotle results downloaded on 2026-05-06.

This note analyzes the local Aristotle result corpus under
`experiments/aristotle_results/`. The result directories are intentionally
scratch artifacts. This tracked note records what the proofs mean, which parts
are production-relevant, and which parts still need local promotion.

## Corpus

| Aristotle job | Scope | Direct theorem count | Local status |
| --- | --- | ---: | --- |
| `0570bfa8-e9e4-4951-91ef-9e02e7b715ea` | broad ZenoDEX math completion packet | 164 | downloaded, trust scan clean |
| `d7939dbc-5a1f-4815-b721-fc649be415b1` | disaster-state hardening context packet | 104 | downloaded, trust scan clean |
| `fb6f30df-0453-4b26-9d84-d7a8893b65d2` | exact ZenoProof / ProofMining reward gate packet | 15 | downloaded, trust scan clean, already mirrored in public Lean style |
| `2e59e2eb-3f9a-4732-a910-f18af4aacab4` and `426c46de-3ec2-41a0-b03a-a3046f99aff8` | earlier ZenoOracle math packets | 34 | downloaded, trust scan clean |

The disaster-context summary says 89 proved theorems, while a direct `rg
'^theorem '` count over its Lean files finds 104 theorem declarations. Treat
104 as the audit count until the summary is reconciled. The difference appears
to be a reporting/counting issue, not a trust issue.

The checked token scan over the three current result jobs found no `sorry`,
`admit`, `axiom`, `unsafe`, or `sorryAx` in Lean files. The active local
`lean` and `lake` commands report Lean `v4.28.0`, matching the Aristotle
projects. One nested tracked file, `lean-mathlib/lean-toolchain`, still pins
`v4.27.0`; if proof promotion runs inside that subproject, align or confirm the
pin before treating local replay as final.

## Main Mathematical Shape

The corpus has five recurring proof forms.

1. Guard decomposition. A Boolean or `Prop` gate is defined as a conjunction,
   then proofs show that acceptance projects to every required field and that
   false fields reject.

2. Binding integrity. Commitments, receipts, roots, and consumer actions are
   modeled as structured fields. Full binding implies structural equality, and
   unchecked fields produce counterexamples.

3. Monotone safety. Adding gates or coverage axes shrinks residual risk, wider
   freshness windows admit at least as much as narrower windows, collateral
   increases preserve safety, and fee or reward budgets bound downstream
   components.

4. Conservation and bounded arithmetic. Settlement composition preserves zero
   net deltas, reward payment preserves the pool delta equation, CPMM output is
   bounded by reserves, and insurance payouts are bounded by the pool.

5. Negative knowledge. Several attractive global claims are false without extra
   assumptions: exact LP round-trip, subset route optimality, local safety
   implying global safety, pairwise-distinct crosschecks implying O5
   independence, and debt increase preserving MCR.

The central disaster-reduction formula is:

```text
ReachableBad(withGate(sys, gate), init) -> ReachableBad(sys, init)
```

Adding a gate cannot create a new reachable bad state in the abstract transition
system. This is the right meta-shape for ZenoDEX hardening: each production
gate should map to a concrete runtime check, a replayable test family, and a
Lean theorem with this monotonicity profile.

## Highest-Value Results

The strongest production basis is the small set of load-bearing theorems that
connects verifier admission, binding, runtime guards, and value conservation.

Tier 1 promotion candidates:

- `admission_requires_verifier` and `reward_requires_verifier_acceptance`: proof
  admission and rewards require verifier context.
- `full_binding_iff_match` and `partial_binding_allows_mismatch`: full binding
  is exact commitment equality, and partial binding is strictly weaker.
- `revocation_breaks_admission` and `code_identity_loadbearing`: verifier
  policy activity and code identity are real admission boundaries.
- `weak_verifier_count_rejects`, `root_drift_rejects`, and
  `acyclic_no_self_support`: O5 independence needs verifier separation, root
  equality, and dependency acyclicity.
- `stale_report_rejected`, `mismatched_query_blocks`, and
  `mismatched_value_blocks`: ZenoOracle consumption is bound to freshness,
  query, and value.
- `settlement_composition_conserved`: conserved settlement batches compose.
- `cpmm_output_le_reserve` and `cpmm_product_preserved`: CPMM execution cannot
  overdeliver relative to reserve and weakly preserves the product invariant.
- `duplicate_claim_rejected`, `reward_conservation`, and
  `reward_budget_bounded`: ProofMining cannot replay a nonce and cannot bypass
  pool accounting when the guards hold.
- `safe_liquidatable_disjoint`, `vault_debt_increase_can_violate`, and
  `oracle_drift_rejects_risky`: perps and zUSD safety depends on the current
  oracle and MCR roots.
- `winner_implies_valid`, `winner_is_minimal`, and
  `subset_winner_not_global`: exact-out route certificates must check the full
  candidate domain before claiming global optimality.
- `adding_axis_reduces_risk`, `removing_axis_can_widen`, and
  `full_coverage_iff`: disaster coverage is monotone and deletions can widen
  residual risk.
- `same_public_result_context_ok_eq` and the code/sandbox/determinism rejection
  theorems: backend-independent admission depends on matching public result
  bits plus explicit TCB assumptions.

The small `fb6f30df` packet is the cleanest immediate production proof source.
Its proof-quality scan rated it `S (100/100)`, and the same shape is already
mirrored in `lean-mathlib/Proofs/ZenoDEXProofMiningClaimability.lean`.

First promotion slice: `lean-mathlib/Proofs/ZenoDEXAristotleDisasterBasis.lean`
now carries 22 locally checked theorem declarations from the Tier 1 basis. It
is covered by `tests/formal/test_lean_zenodex_aristotle_disaster_basis.py` and
receipt `lean-mathlib/proof_receipts/zenodex_aristotle_disaster_basis_v1.json`.

## Curation Findings

Several proof families are high-value but need curation before becoming public
assurance claims.

- The broad `0570bfa8` packet is intentionally abstract. Many theorems prove
  facts about fields such as `proofOk`, `bindingOk`, `policyOk`, or
  `dagClosed`. Those are useful only after a binding pass maps each field to a
  runtime implementation, a replay command, and a test witness.

- `Section06_ReceiptBinding.lean` is large and valuable, with 33 theorem
  declarations, but it models O3/O4/O5 receipt fields as abstract `Prop`
  structures. It should be promoted after tying each field to the actual
  receipt format, source registry, runtime state root, query/value/window, and
  consumer action.

- The disaster-context O5 DAG theorem currently uses `dagAcyclicSimple`, which
  rejects self-loops and two-cycles. It is useful negative knowledge, but it is
  weaker than full transitive DAG closure. A follow-up theorem packet should
  define reachability and prove no self-support over transitive closure.

- Backend equivalence currently proves that equal public result records imply
  equal `contextOk` values. It does not prove that Wasm, native, and zkVM
  backends compute the same public result from the same artifact. That stronger
  claim needs a refinement or simulation theorem plus code identity and signing
  assumptions.

- `Module.boundary_mismatch_blocks` and `Backend.assumptions_required` are
  semantically weak despite checking. They should be quarantined or restated.
  The useful module result is `Module.composition_sound`; the useful backend
  result is explicit safe substitution under acceptance equivalence and
  assumptions.

- The proof-quality scanner rated `Section03_ProofMiningReward.lean` and
  `Section04_Claimability.lean` as `C`, mostly because they are generated
  decomposition proofs with broad automation and verbose comments. The smaller
  promoted packet covers the same operational surface with cleaner proof style.

- The disaster-context `Settlement.lean` rated `B`. The main formulas are
  useful, but CPMM monotonicity and product preservation should be ported into
  local style and replayed in the repo toolchain before being cited as public
  assurance.

## What The Math Now Says

ZenoDEX can now be organized as a disaster-minimizing theorem ladder:

```text
VerifierContextOK /\ BindingOK /\ PolicyOK /\ FreshnessOK
/\ SandboxOK /\ CodeIdentityOK /\ DeterministicOK
-> ZenoProofAdmissionOK
```

Every listed component is load-bearing in at least one Aristotle packet. The
practical consequence is direct: production admission should be a projection of
these fields, and every field should have a runtime rejection test.

```text
FullBinding(commitment_a, commitment_b) <-> commitment_a = commitment_b
```

Full binding is exact structural equality over the chosen fields. Partial
binding creates counterexample families, so any public proof or reward path
that omits a field must explicitly mark the omitted field as outside the claim.

```text
Conserved(batch_1) /\ Conserved(batch_2) -> Conserved(batch_1 ++ batch_2)
```

Settlement conservation composes when the local batch equations include all
declared outflows. This supports a batch-level audit lane and a public replay
receipt.

```text
AxisAdded -> ResidualRisk(new_axes) subset ResidualRisk(old_axes)
```

The coverage model gives a clean mathematical interpretation of the disaster
work: adding a real axis can shrink the residual bad-trace set; removing a
uniquely covering axis can widen it. The theorem does not claim the axis set is
complete.

## Implications For ZenoProof

ZenoProof does not need to be defined around a single VM. The math supports a
backend-neutral verifier-result interface:

- proof accepted;
- binding accepted;
- policy accepted;
- freshness accepted;
- sandbox accepted;
- code identity accepted;
- determinism accepted.

A zkVM is useful as one backend for public validity proofs. Wasm is useful as a
deterministic sandbox and portable replay target. Native subprocess verifiers
can remain a local replay backend. The protocol-level theorem should speak
about backend result equivalence and explicit TCB assumptions, then each backend
gets its own refinement proof or signed-result receipt.

For production, Wasm alone gives a sandbox lane. A complete trust story also
needs code signing, deterministic runtime pinning, artifact hashing, policy
root binding, and a replay receipt that maps exactly into the `contextOk` bits.

## Work To Complete

1. Promote the `fb6f30df` proof packet as the first canonical ZenoProof /
   ProofMining proof family. This is mostly done in
   `lean-mathlib/Proofs/ZenoDEXProofMiningClaimability.lean`.

2. Continue porting Tier 1 disaster theorems into `lean-mathlib/Proofs/` under
   the repo toolchain, keeping theorem names stable and recording receipts. The
   first compact basis file is `Proofs/ZenoDEXAristotleDisasterBasis.lean`.

3. Build a theorem-to-runtime matrix:

```text
Lean theorem -> runtime field -> source file -> public test -> replay command
```

No theorem should be used as a production claim until this matrix exists for
its assumptions.

4. Submit or write the next proof packets for:

- transitive O5 DAG closure and dependency closure completeness;
- exact-out inverse quote correctness and multi-hop slippage bounds;
- LP and CPMM rounding error bounds;
- temporal policy lifecycle, revocation, freshness expiry, and re-admission;
- backend refinement between Wasm, zkVM, and native verifier result records;
- code-signing, artifact identity, and release provenance monotonicity.

5. Keep Julia in the loop for arithmetic search. Julia should generate
counterexamples and boundary sweeps for median deviation, CPMM rounding, LP
round-trip loss, perps margins, and zUSD MCR headroom. Lean should receive the
restricted theorem surfaces that survive those sweeps.

6. Use Aristotle for proof search and theorem-ladder expansion, then accept
only the pieces that pass local build, trust scan, statement review, and runtime
mapping.

## Bottom Line

The Aristotle corpus is a substantial formal scaffold for ZenoDEX safety. It
does not yet constitute an end-to-end production proof. Its strongest immediate
value is a broad map of disaster-state gates, counterexamples, and promotion
candidates. The next engineering move is to turn the strongest theorem families
into local Lean files and attach each theorem to executable replay evidence.
