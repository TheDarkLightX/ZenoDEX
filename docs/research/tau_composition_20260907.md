# Composing Tau requirements into reusable proposal controllers

Date: 2026-09-07. Status: experimental implementation and bounded native replay.
All artifacts have authority `NONE`; no settlement or Tau Net rule acceptance is
mounted by this work.

The useful result is an original application compiler around Tau's native
Boolean reasoning. It reuses small symbolic repair maps, discovers a safe
composition order, merges conflicting groups, and exports executable Tau
controllers. A second representation uses a common valid anchor and a shared
constraint residual to avoid nested expression growth. The implementation is
in [`src/tau_composition`](../../src/tau_composition/); the command-line entry
point is [`tools/tau_composition.py`](../../tools/tau_composition.py).

This is a measured application improvement. It does not establish a new
decision procedure, greater expressiveness than Tau, historical priority, or
that these are globally optimal research targets.

## Highest-value uses

| User story | Concrete behavior | Current evidence boundary |
| --- | --- | --- |
| As a ZenoDEX developer directing a coding swarm, I want one agent to add oracle freshness while other agents maintain authorization and recovery rules. | Reuse unchanged native results, check interactions, recompute changed groups. The developer reviews the combined meaning. | Implemented for Boolean equations; synthetic incremental replay. |
| As an operator working with planning agents, I want their liquidation, recovery, and cancellation proposals to satisfy eligibility and exclusivity together. | Produce a consistent proposal; retain every proposal already satisfying all requirements. Agents explain proposed changes to the operator. | Original action-flag example; exact Boolean oracle and native traces. Actual user intent and effect admission require host contracts. |
| As a human supervising an operational swarm, I want a predictable fallback when its proposed bundle is invalid. | Validate an environment-dependent anchor; keep valid proposals; repair invalid proposals using it. The human selects the fallback policy. | Common-anchor compiler and generated Tau. An all-zero anchor is rejected if any requirement forbids it. |
| As a Tau Net recipient assisted by an LLM, I want to understand whether an offered rule conflicts with my existing obligations. | Desired integration: native conflict reasoning and revision comparison; the LLM explains consequences and the human decides whether to accept. | Architectural target. Current generic stream exports are not Tau Net offer payloads. |
| As a protocol designer directing competing research agents, I want an example explaining why their individually correct components conflict. | Produce a failing order, derive its exact safe guard, and return concrete evidence that the agents can use to revise their designs. | Native two-rule counterexamples, exact projection, and guarded composition replay. |

Proposals can add or remove flags when the original proposal is invalid. User
consent, action preferences and forbidden changes must therefore be requirements
or separately enforced acceptance conditions. No minimum-edit, optimal trade,
price, collateral, or fairness objective follows from a reproductive map.

For ZenoDEX, the nearest practical integration is a developer workbench and
differential reference controller. It can propose compatible action flags while
the existing authenticated data producers and deterministic validators retain
effect authority. The research example does not replace mounted liquidation or
settlement business rules.

## What Tau contributes

| Primitive | Use in this study | Limit established by inspection or native probing |
| --- | --- | --- |
| `lgrs` | Produce symbolic reproductive solutions to Boolean equations. | A repair fixes all valid proposals; it need not minimize changes. Ordinary `solve` can also assign the environment and is insufficient for a parametric controller. |
| `valid` | Check parsed-map soundness, fixed solutions, preservation, anchors and refinement. | A recorded native verdict is solver evidence, not an exported independently checked proof object. |
| `qelim` | Eliminate proposal coordinates to derive feasibility and exact safe-order guards. | The exact exporter accepts a small Boolean equation fragment. A tested BV8 projection retained a quantifier and was rejected as unsupported. |
| Executable streams | Run emitted controllers on supplied input files and compare actual output rows. | The present controllers are memoryless. This is not temporal liveness or production throughput evidence. |
| Causal temporal reasoning | Distinguish present-input response from prediction of a future input. | Native REPL probes accepted current-input copying and rejected requiring yesterday's output to predict today's arbitrary input. API routing must be checked separately. |
| Specifications as values and rule revision | Candidate foundation for offer comparison and modular policy evolution. | Update continuity, temporal assumptions and the network profile need their own contracts. They are not implemented by the Boolean compiler. |

Primary capability reference: [Tau Language README](https://github.com/IDNI/tau-lang/blob/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/README.md).
The algebra of SBF values is broader than host booleans: native validation says
`all p ((p=0)||(p=1))` is false, while `all p (p|p'=1)` is true. Exhaustive
host-bit replay alone does not establish arbitrary-Boolean-algebra claims.

## Normative contract and algorithms

An input contract declares immutable environment coordinates `e`, mutable
proposal coordinates `x`, and named polynomial residuals `f_i(e,x)`.

```text
C(e,x) := every f_i(e,x) = 0
Required: C(e,P(e,x))
Required: C(e,x) -> P(e,x) = x
Required: output environment = input environment
```

These properties make the image of `P` exactly the legal proposal set and imply
idempotence. The host domain consists of exact Python booleans. The native
identities quantify over Tau's Boolean algebra. Data are not credentials:
an input named `proof_valid` or `authorized` carries no verifier authority.

The native-map compiler does the following:

1. Normalize each requirement with distinct environment/control roles. Ask Tau
   for its local map; independently check soundness and fixed solutions after
   parsing the result.
2. Add an edge `i -> j` when map `P_i` has not been proved to preserve `C_j`.
   Execute `i` before `j`. Disjoint write/read support is a sufficient local
   reason to omit the preservation query.
3. Topologically order the graph. For a cycle, merge its strongly connected
   requirements, request a joint native map, and recompute the interactions.
   Every merge reduces the number of groups.
4. Compose simultaneously within each map and sequentially across the chosen
   order. Reuse only matching normalized native results within the session.

Timeout, resource exhaustion, malformed output, or unsupported syntax gives
`UNKNOWN`. An unproved preservation obligation retains its dependency edge.
The application does not enable incomplete native search caps that could
report give-up as unsatisfiability.

For a supplied order `F`, the exact safe guard and feasibility are different:

```text
G_F(e) := forall x, C(e,F(e,x))
E(e)   := exists x, C(e,x)
```

The bounded cover compiler accepts up to eight supplied full orders. It derives
their guards, forms disjoint Boolean coefficients, requires the coefficient
remainder to be zero, and separately checks the final polynomial map natively.
Joining guard terms does not replace that last soundness check. It does not
search all possible orders or claim a minimum cover.

The common-anchor compiler requires a complete environment-only `a(e)` with
every `f_i(e,a(e))=0`, checked natively. It stores the residual and anchor:

```text
R(e,x) := OR_i f_i(e,x)
P_j(e,x) := (x_j AND NOT R(e,x)) OR (a_j(e) AND R(e,x))
```

The host evaluates the original proposal residual once, then rechecks a repaired
candidate. For host bits, any violation selects the whole anchor. Native export
uses a uniquely constrained same-step existential residual and emits only the
declared control outputs. Source sharing does not prove a single internal Tau
evaluation. A fresh satisfying assignment is insufficient for finding an anchor
that must work for every environment.

The construction is classical reproductive-solution algebra; see
[Martin and Nipkow, Boolean Unification (1989)](https://www.cs.rice.edu/~javaplt/411/24-spring/NewReadings/Unfication%20Theory/Boolean-unification---The-story-so-far_1989_Journal-of-Symbolic-Computation.pdf)
and [Asor, Theories and Applications of Boolean Algebras, Theorem 2.8](https://tau.net/wp-content/uploads/2026/03/Theories-and-Applications-of-Boolean-Algebras-0.1-1.pdf).
The implementation contributions are the composition/reuse strategy, exact
conditional-order experiments, bounded representation, and application replay.

## Counterexamples that shaped the implementation

**Restoring a prohibited action.** Let `paused AND debit = 0` and
`debit XOR credit = 0`. The separate native maps can be composed into
`(debit OR credit, debit OR credit)` after masking only the original debit.
At `paused=1, debit=0, credit=1`, the result violates the pause rule. Idempotence
and fixing common solutions do not alone imply sound composition. The exact
safe guard of that order is `paused=0`, although a legal proposal exists for
either pause state. Joint synthesis closes the conflict.

**Conditional cycles.** For `p' x OR p y'=0` and `p x OR p' y'=0`, neither
local repair preserves the other's constraint unconditionally. Opposite orders
have complementary exact guards. Boolean factor gluing produces `(0,1)` and
passes an independent native check. This is a small feasibility demonstration,
with no timing or novelty claim.

**Review regressions.** Independent review found reversed XOR/join precedence,
an incomplete order cover hidden by a valid all-zero default, and expression
expansion escaping native-parser limits. Permanent tests first reproduced each
failure. The parser now has native mixed-operator parity tests; incomplete
covers reject explicitly; expanded terms are bounded before recursive consumers.

The host limits are 16,384 expanded nodes, depth 96, and 1,000,000 canonical
term-JSON bytes. Counting uses shared object identities while charging every
expanded occurrence. Native output parsing additionally has its own stricter
4,096-byte/256-node/64-depth term profile. A profile rejection says nothing
about the native engine's ability to solve the equation.

## Formal evidence and practical comparison

- [TauReproductiveComposition.lean](../../lean-mathlib/Proofs/TauReproductiveComposition.lean)
  proves abstract composition, fixed-solution, exact-guard and guarded-selection
  results with explicit premises.
- [TauCommonAnchor.lean](../../lean-mathlib/Proofs/TauCommonAnchor.lean)
  proves scalar shared-anchor composition and commutation under mixing locality,
  including a counterexample showing why that premise matters.
- [TauPolynomialRepair.lean](../../lean-mathlib/Proofs/TauPolynomialRepair.lean)
  derives vector mixing locality by polynomial-syntax induction, then proves
  soundness, exact image, fixed solutions and shared-anchor composition over an
  arbitrary Boolean algebra.

These files contain checked mathematics. Parser/compiler correspondence, the
graph implementation, executable provenance and end-to-end DEX refinement are
separate obligations. Python/native differential and negative tests provide
bounded implementation evidence.

The final [experiment report](tau_composition_20260907/report.json) contains
all samples, source hashes, exact query counts, native traces, guard witnesses,
and representation comparisons. Ratios are reported only when both native-map
methods complete. Both methods solve the same relation but may select different
repair maps. Timings include application checking and native process costs;
they are local observations on synthetic families.

OrbitSynthesis currently provides finite-relation certificates and affine
dispatch. This compiler starts from symbolic requirements and delegates native
Boolean reasoning to Tau. No equivalent-task performance comparison against
OrbitSynthesis was run, and this work does not invalidate its existing results.

## Fable and Tricki contributions

Fable returned a substantive memo using `claude-fable-5-1` with Max effort.
It reviewed public context only and did not browse or inspect the implementation.
Its useful suggestions were the contract-composer priority, comparison of
feasibility with realizability, and shared-anchor residual representation.
Those suggestions were independently derived, implemented and checked where
described above. Fable's rankings and proposed speedups were hypotheses.

The [Tricki](https://tricki.sisask.com/) supplied research tactics: examine the
converse, test small cases, and decompose a ring using idempotents. The original
site returned an access error; retained tactic text and the accessible mirror
supported retrieval. These tactics prompted the unsafe-order witness and
conditional-factor experiment. Retrieval and model output are suggestion
sources, not proof. No Tricki text or engine implementation was copied into the
software.

## Tau Net and license boundary

Current [Tau Net rule sharing](https://github.com/IDNI/tau-testnet/tree/e3dbb3e8607125a10aae6213a1c5a2e85950e923#rule-sharing)
binds an offer to sender, recipient, rule text and expiry. Its offered-rule
profile permits one currently supported output, `o5`, one `always`, and forbids
references to the sender-guard input `i12` and nested temporal operations.
The node builds sender-scoped total rules. The documented conflict endpoint's
logical layer is unavailable through the native Python binding; a clean
structural result alone is insufficient. These are upstream source findings,
with no network replay here.

An actual integration must preserve exact offer bytes, recipient consent,
expiry, sender scoping, the supported stream profile, and mounted host meaning.
The generic multi-output `.tau` files emitted here must not be submitted as
offers without that separate adapter and its verification.

The original application invokes a separately installed Tau executable. It
vendors no Tau binary, solver implementation or Tau Parsing Library code.
The independent output parser recognizes a small Boolean term fragment.

The [versioned Tau Language license](https://github.com/IDNI/tau-lang/blob/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/LICENSE.md)
distinguishes permitted research and Tau-Net-related use from other commercial
use and excludes framework redistribution. Its
[NOTICE](https://github.com/IDNI/tau-lang/blob/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/NOTICE.txt)
requires separate licensing for direct use of the Tau Parsing Library.
The [Tau Net license](https://github.com/IDNI/tau-testnet/blob/e3dbb3e8607125a10aae6213a1c5a2e85950e923/LICENSE.md)
is a separate custom grant and expressly excludes the Language framework.
These licenses are not interchangeable.

Patent review identified [US12254082B1](https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/12254082)
and related published applications. Original mathematics and source attribution
do not establish freedom to operate. Commercial deployment scope, hosted-service
terms, applicable patent claims, and any redistribution require their own
assessment. This study provides no legal clearance.

## Replay

Choose the Tau binary explicitly; the repository's default discovery can select
a different local fork. This study used version `0.7.0-alpha (d80aa50c)`, SHA-256
`b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`.
Its containing checkout revision differed from its embedded revision, so a
reproducible source-to-binary build has not been established.

From the repository root, using a compatible separately installed executable:

```bash
python3 tools/tau_composition.py describe
python3 tools/tau_composition.py compile --tau /path/to/tau --example action_permissions
python3 tools/tau_composition.py compile --tau /path/to/tau --example action_permissions --zero-anchor
python3 tools/tau_composition.py compile --tau /path/to/tau --example conditional_cycle --two-order-cover
python3 tools/benchmark_tau_composition.py --tau /path/to/tau --out /tmp/tau-composition-replay --repeats 3
TAU_COMPOSITION_BIN=/path/to/tau python3 -m pytest -q tests/test_tau_composition*.py tests/test_tau_common_anchor.py tests/test_tau_anchor_export.py
```

Output directories must be new. CLI stdout is JSON: exit 0 means the requested
research operation completed, 2 means invalid input, and 3 means native or
representation results are unknown/unsupported. None grants an effect.

Single-file proof checks use the existing pinned Lean environment:

```bash
cd lean-mathlib
lake env lean Proofs/TauReproductiveComposition.lean
lake env lean Proofs/TauCommonAnchor.lean
lake env lean Proofs/TauPolynomialRepair.lean
```

The next useful research questions are measurable: how much proposal quality is
lost to a common anchor; whether a bounded anchor family improves it while
retaining compactness; and whether native contract analysis can provide useful
Tau Net offer previews within the real host profile. Temporal strategy
composition and BV arithmetic remain outside the proved application fragment.

These stories describe neuro-symbolic collaboration: people own goals and
consent; LLMs propose and explain; Tau computes consequences of explicit formal
inputs. The translation from a person's intent into those inputs remains a
review obligation. [Lessons and the next research target](tau_research_lessons_20260907.md)
record how this changes the next software design.
