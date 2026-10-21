# ZRPF recursive soundness ledger V1

Status: research-only. Every authority and promotion field in the accompanying
profile is false. This package does not make ZRPF production-ready and does not
certify RISC Zero.

## Decision

ZRPF should stop treating a backend/version/control-ID tuple as a complete
security claim. The pinned RISC Zero v3.0.5 implementation exposes materially
different soundness estimates under three different assumption regimes, and a
recursive tree consumes one error term for every base and recursion proof event.

The immediate force multiplier is a machine-checked soundness ledger that:

1. names the assumption regime rather than saying only “bits of security”;
2. pins the circuit and protocol parameters that determine each per-event bound;
3. records the actual segment, lift, join, and resolve event counts;
4. applies an explicit composition theorem or conservative finite union bound;
5. is committed by the future ZRPF authority-manifest root; and
6. fails promotion when a model is ungoverned, event counts are incomplete, or
   the resulting floor is below policy.

The bundled example deliberately fails steps 3, 5, and 6. It uses a minimum
one-segment-per-node event count to expose the issue without granting authority.

## Critical finding: one backend has three assurance levels

RISC Zero v3.0.5 implements three calculator functions with different labels.
The first row is the calculator’s proven FRI list-decoding regime. The second
depends on proximity-gap and DEEP-FRI conjectures. The third depends on the
ethSTARK Toy Problem conjecture. “Proven” in this table is the upstream
calculator’s model label, not an end-to-end proof of the zkVM, ZRPF, Fiat–Shamir
in the random-oracle model, collision resistance, implementation correctness,
or the build pipeline.

| Explicit model ID | RISC-V PO2=20 | RISC-V PO2=22 | Recursion PO2=18 |
|---|---:|---:|---:|
| `proven_list_decoding` | 41.567039489746094 | 37.585384368896484 | 46.018375396728516 |
| `conjectured_strict` | 74.87677764892578 | 70.95629119873047 | 78.86270904541016 |
| `toy_problem_conjecture` | 97.14198303222656 | 95.29951477050781 | 99.75871276855469 |

Provenance of the numbers:

- The pinned [soundness calculator](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/zkp/src/prove/soundness.rs)
  defines the implemented models and formulae.
- The upstream [RISC-V soundness regression tests](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/zkvm/src/host/server/prove/tests.rs#L1087-L1134)
  assert the PO2=20 f32 results rounded in source as `41.56704`, `74.87678`,
  and `97.14198`. The decimals in the table are those exact f32 values rendered
  losslessly.
- The PO2=22 values replay the same calculator and RISC-V tapset at the pinned
  verifier’s [maximum accepted segment PO2](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/zkvm/src/receipt.rs#L898-L902).
  This is the fail-closed value for a profile that accepts all controls through
  that maximum; the default executor’s PO2=20 is not a sufficient worst case.
- The recursion values replay the same calculator with the pinned
  [recursion tapset](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/circuit/recursion/src/taps.rs)
  and [RECURSION_PO2=18](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/zkvm/src/host/recursion/prove/mod.rs#L58).

The replay used BabyBear with extension degree 4, inverse rate 4, 50 FRI
queries, fold 16, and minimum FRI degree 256. The RISC-V tap widths are
`[103, 1, 211]`; recursion tap widths are `[12, 23, 128]`; both have maximum
tap-combination size 6. These are pinned as data in the profile and rejected on
drift by the validator.

### Frontier in the literature

The calculator’s strict and proven regimes are grounded in
[DEEP-FRI](https://eprint.iacr.org/2019/336) and
[Proximity Gaps for Reed–Solomon Codes](https://eprint.iacr.org/2020/654).
RISC Zero’s pinned soundness notebook also explores a unique-decoding route,
but marks integration work and a more formal analysis as incomplete or
unpublished. That route is a high-value research hypothesis, not a current
production parameter claim. A backend upgrade must therefore replay and review
the assumption model; changing the version string alone does not close this
gap.

A newer result by Crites and Stewart,
[On Reed–Solomon Proximity Gaps Conjectures](https://eprint.iacr.org/2025/2046),
refutes specific up-to-capacity formulations: correlated agreement, WHIR’s
mutual correlated agreement, and DEEP-FRI list-decodability. It does **not** by
itself refute the Toy Problem conjecture, every FRI analysis, or RISC Zero as a
system. Nor is it automatic that its counterexamples match RISC Zero v3.0.5’s
particular `ETA=0.05`, `c1=c2=1`, `c_rho=1` instantiation. The release ledger
must therefore pin the exact paper, conjecture/theorem number, parameterization,
and version—not merely a label such as “FRI conjecture”—and record a reviewed
mapping. This package pins that identity and still accepts none of the models
for authority.

## Composition model

Let a base RISC-V proof event have failure probability at most
`2^(-b_base)` and a recursion proof event at most `2^(-b_recursion)` under one
explicit model. For `B` base events and `R` recursion events, the finite union
bound gives:

```text
epsilon_total <= B * 2^(-b_base) + R * 2^(-b_recursion)
b_effective    = -log2(epsilon_total)
```

This algebra does not require event independence. It does require a valid
per-event bound under the chosen model and complete accounting of all events
whose failure could admit a false root. A tighter backend composition theorem
may improve the result, but it must be stated and reviewed explicitly before it
replaces this envelope.

RISC Zero’s pinned recursive prover creates proofs through
[lift, join, and resolve](https://github.com/risc0/risc0/blob/8eb06ab020a92dc5b63ba6dd0836d432aba6d890/risc0/zkvm/src/host/recursion/prove/mod.rs#L73-L256).
For a full `f`-ary ZRPF tree with `N` leaves:

```text
I = (N - 1) / (f - 1)  internal nodes
T = N + I              total ZRPF guest nodes
E = T - 1              child-assumption edges
```

If node `i` uses `s_i` RISC-V segments and `S = sum(s_i)`, the minimal pipeline
accounting is:

```text
base events    = S
lift events    = S
join events    = S - T
resolve events = E
recursion      = S + (S - T) + E = 2S - 1
```

The example sets every `s_i=1`, so `S=T`. This is a minimum, not retained
telemetry. Extra segmentation, retry proofs, normalization proofs, or a changed
backend pipeline add events and reduce the calculated floor.

Wrapping a proof does not reset the earlier soundness budget. Under this
conservative model, the wrapper adds another possible failure event.

## What the existing 64-by-8 shape means

For 64 leaves and fanout 8, `I=9`, `T=73`, and `E=72`. The illustrative
one-segment ledger therefore has 73 base events and 145 recursion events (73
lifts plus 72 resolves).

| Model | Effective bits if those counts are exact |
|---|---:|
| Proven FRI list-decoding | 31.38729198260645 |
| Conjectured strict | 64.75457178445512 |
| Toy Problem conjecture | 88.98496367319508 |

Consequences:

- An unqualified “about 96 bits” backend statement is not a 96-bit 64-leaf
  system statement.
- Even under the Toy Problem conjecture and minimum event count, the PO2=22
  envelope is below 90 bits for this shape.
- Under the strict or proven-list models, increasing fanout cannot recover a
  target that a single leaf/lift already misses.
- At one million leaves with fanout 8 and the same minimum-event assumptions,
  the effective figures are about 17.45 proven-list bits, 50.82 strict-conjecture
  bits, and 75.05 Toy-model bits.
- Under the Toy model, PO2=22, fanout 8, and the same minimum-event assumptions,
  the largest valid full-tree leaf count retaining at least 80 bits is 32,341.
  This is an illustrative capacity calculation, not a safe production limit.

The useful breakthrough is not the particular cap. It is making the security
budget an input to fanout, epoch sizing, segmentation, and release policy.

## Profile contract

The example profile and schema are intentionally narrow:

- backend identity is exactly RISC Zero v3.0.5 commit
  `8eb06ab020a92dc5b63ba6dd0836d432aba6d890`;
- all circuit parameters and exact f32 observations are pinned;
- the three model IDs, labels, source functions, and assumption classes cannot
  be interchanged;
- all authority flags and every per-model acceptance flag must be false;
- no model or minimum security floor may be selected;
- event counts are explicitly incomplete and illustrative;
- topology, event-count, and union-envelope arithmetic are recomputed;
- duplicate JSON keys, non-finite numbers, BOMs, type confusions, missing
  sources, unknown fields, and value drift fail closed.

Validate it with only the Python standard library:

```bash
python tools/validate_zrpf_soundness_profile.py config/proof_profiles/zrpf_risc0_3_0_5_soundness_v1.example.json --json
python -m unittest discover -s tests -p 'test_validate_zrpf_soundness_profile.py' -v
```

The JSON Schema is for ecosystem tooling. The Python validator is the semantic
gate for this package; it applies cross-field equations that the schema alone
does not express.

## Lean theorem and exact scope

`lean-mathlib/Proofs/ZRPFSoundnessEnvelope.lean` proves an abstract list-composition result:

1. if an abstract risk function is zero on the empty event and subadditive over
   event union, the risk of a finite union is no greater than the sum of the
   individual risks;
2. if each base event is bounded by `epsilonBase` and each recursion event by
   `epsilonRecursion`, the combined risk is bounded by
   `base.length * epsilonBase + recursion.length * epsilonRecursion`; and
3. for a positive one-segment tree, lift-plus-edge recursion accounting equals
   `2 * nodeCount - 1`.

The module has no `sorry` or custom axioms. It does not prove the RISC Zero
per-event probabilities, random-oracle assumptions, cryptographic reductions,
Rust implementation refinement, or completeness of the event log. Those are
separate obligations that feed the proved algebra.

Verification note: this workspace did not provide `lean` or `lake`, so the Lean
module was not compiled here. It received only a static no-`sorry`/no-`axiom`
check and remains a proof candidate until the repository’s pinned Lean 4.27.0
CI compiles it.

## PR-sized next steps

1. **Backend regression vectors.** Add upstream-equivalent Rust tests for
   RISC-V PO2=20, RISC-V PO2=22, and recursion PO2=18 under every named model.
   Fail on parameter or f32 output drift and require an assumption review.
2. **Proof-event telemetry.** Make the prover emit a canonical receipt-sidecar
   count of segments, lifts, joins, resolves, and any new recursion program.
   Recompute it from retained artifacts; never trust a caller-supplied total.
3. **Soundness admission gate.** Generalize this research-only validator into a
   governed policy only after an accepted model and minimum floor are chosen.
   Reject unknown events, incomplete counts, and arithmetic drift.
4. **AuthorityManifestV1 binding.** Commit the soundness-profile root alongside
   the receipt-security profile, program/dependency manifest, statement schema,
   transcript/protocol identity, and provenance root. Construct the verified
   authority type only after receipt verification and recomputation.
5. **Composition theorem review.** Ask RISC Zero for the precise adaptive
   recursive-composition theorem. Replace the union envelope only with a
   reviewed tighter theorem whose hypotheses are machine-checkable at release.
6. **Unique-decoding experiment.** Reproduce and independently review the
   notebook’s unfinished unique-decoding analysis, add regression vectors, and
   keep it non-authoritative until the missing integration and publication
   obligations are closed.

## Files

- `config/proof_profiles/zrpf_soundness_profile_v1.schema.json` — strict research profile schema.
- `config/proof_profiles/zrpf_risc0_3_0_5_soundness_v1.example.json` — source-linked 64-leaf example.
- `tools/validate_zrpf_soundness_profile.py` — stdlib semantic validator and calculator.
- `tests/test_validate_zrpf_soundness_profile.py` — mutation and fail-closed tests.
- `lean-mathlib/Proofs/ZRPFSoundnessEnvelope.lean` — abstract finite-union and event-count proofs.
