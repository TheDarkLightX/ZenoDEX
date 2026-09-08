# Tau research completed-study checkpoint

Initially stopped at the user's request because today's compute credits were
exhausted. Work resumed under the user's later Fable/Claude delegation approval.
Three bounded research cycles are now implemented, reviewed and locally checked.
All work is saved in the shared checkout; Git history records any subsequent
commit. Preserve unrelated dirty and concurrent work; do not reset, clean,
stash or stage the whole tree.

Later steering: the user said Fable still has compute and requested delegating
the remaining tasks to it. A bounded 120,396-byte completion packet was prepared
from 15 newly authored research/proof/test files, with no unrelated repository
source or secrets. Automatic approval review rejected that source transfer to
the external Fable service because explicit permission for this exact payload
and destination was missing. No source was sent by the rejected call. Exact
payload-source hashes and status are in the second-cycle checkpoint JSON.
The user subsequently explicitly authorized sending it and assigning Fable 5.1
and Claude 5 agents to complete the plan. The full implementation request hit
Fable's session limit without returning code. After the reported reset, a smaller
codec request reached Fable but received a provider safeguard rejection, again
without code. Two Opus 5 Max review attempts timed out without usable findings.
These attempts provide no verification evidence.

The user then explicitly requested another Fable 5.1 retry with the full rest of
the work. A current 17-file, 123,806-byte packet was sent with safeguards enabled
and the earlier provider rejection disclosed. That request timed out after
20 minutes without usable files. The user then requested giving the work to
Opus 5. The 11-file, 84,826-byte implementation packet reached Claude Opus 5 Max,
which returned seven complete files in 1,152.303 seconds. Saved public-text
events preserved the complete files across multiple messages. Parent review
corrected source-validation, codec and reporting issues; final local checks and
the seven-case replay passed. Raw provider events and thinking remain excluded
from repository artifacts. See
[delegations.json](tau_swarm_20260907/delegations.json) for attempt statuses and
hashes. The two earlier public-context Fable design memos succeeded.

## Completed first cycle

- Original native Tau repair/composition package: `src/tau_composition/`.
- CLI: `tools/tau_composition.py`; reproducible experiment:
  `tools/benchmark_tau_composition.py`.
- Research, normative contracts and neuro-symbolic user stories:
  [tau_composition_20260907.md](tau_composition_20260907.md).
- Final source-bound experiment and validation:
  [report.json](tau_composition_20260907/report.json),
  [validation.json](tau_composition_20260907/validation.json).
- 68 focused tests passed with native Tau enabled. The final experiment checked
  2,096 original plus 64 shared-anchor Boolean rows, and 55 plus 4 native trace
  rows. Three Lean files passed single-file checks. All 24 experiment source
  hashes matched when the validation record was saved.
- Completed paired examples measured about 8.59x and 10.46x faster compilation;
  the smallest case was approximately equal/slightly slower. Shared-anchor
  source was 1,873 versus 45,825 bytes on the 12-coordinate example, about 24.5x
  smaller, with different repair choices. No general speed/optimality claim.
- Independent review closed parser precedence, incomplete-cover acceptance and
  host expression-growth defects. Existing active Tau subset and assurance
  checks, Ruff, scoped MyPy and the claims-registry check passed.
- No production, network admission, legal clearance or foundational novelty claim.

## Completed bounded second cycle: Tau Swarm

The user clarified that every persona is a person with an LLM or an agent swarm.
They requested a more ambitious follow-on opportunity and saved lessons.

The new package `src/tau_swarm/` computes one local choice domain per agent from
a shared global contract, a human-selected valid starting plan, and disjoint
ownership of proposed fields. Every combination of admitted local choices must
satisfy the global contract. Native universal projection expands the domains
sequentially; native equivalence, product-safety, anchor and final exact-cofactor
checks certify the result. This is an inclusion-maximal product, not necessarily
the largest product or the whole feasible relation.

Completed pieces:

- `models.py`: immutable blocks/problems/domains, local choice checks, and
  subject/environment-bound `LocalChoice` aggregation that rechecks the bundle.
- `compiler.py`: native exact one-sweep expansion and final obligations.
- `examples.py`: asymmetric choices, three-agent API-change planning, and a
  two-code-block counterexample to order-search optimality.
- `exports.py`: standalone local Tau compatibility gates and bounded native
  file-stream replay. It uses only the environment and that agent's coordinates.
- `inspection.py`: bounded local choices and concrete counterexamples explaining
  excluded choices, with named violated requirements. Eight dedicated tests
  passed, including stable rejection of malformed environment containers.
- `codec.py`, `tools/tau_swarm.py` and `tools/benchmark_tau_swarm.py`: completed
  closed JSON interface, parser-derived discovery, custom/example compilation,
  per-agent artifact export, bounded explanations and source-bound replay.
  Opus supplied these completion files and codec/CLI tests; parent review and
  independent codec review corrected and checked the integrated result.
- `lean-mathlib/Proofs/TauSwarmAutonomy.lean`: worker-checked proof of sweep
  safety, nonempty factors, exactness persistence, inclusion maximality, and
  the unsafe stale-parallel-expansion counterexample. Parent single-file replay
  passed with `lake env lean Proofs/TauSwarmAutonomy.lean` after resuming.

Earlier evidence retained:

- Model/aggregation tests passed, including changed subjects, mixed environments,
  ownership mismatch, bool lookalikes and forged inadmissible choices.
- 24 native exporter tests passed with explicit Tau.
- Parent's five independent native compiler tests passed: exact product oracles,
  human priority tradeoffs, stronger seed selection, projection mutation and
  UNKNOWN propagation. These were separate runs, not final combined acceptance.
- After resuming, all 45 existing swarm tests passed together with native Tau.
  The independent compiler/model review then found an avoidable global-alias
  limit. A 65-coordinate, two-block regression failed before repair and passed
  after restricting parser aliases to the environment and current block. The
  reviewer inspected and closed that fix. Nonconstant local projections retain
  their existing parser/representation bounds. See
  [core_review.md](tau_swarm_20260907/core_review.md).
- Native discovery retained 122 queries and 13 full sweeps. An independent finite
  oracle checked all 6,144 valid-anchor/order sweeps over 256 three-bit relations.
  Discovery JSON and current source hashes are saved beside
  [checkpoint.json](tau_swarm_20260907/checkpoint.json).

Final acceptance:

- **190 tests passed in 33.92 seconds**, native enabled, with no skips: 68 first
  cycle tests and 122 swarm tests. This includes the single-agent, local-capacity,
  codec round-trip, malformed-input and failed-replay regressions.
- The final software replay passed seven cases and nine environment slices:
  320 independent Boolean oracle rows, 84 native gate trace rows, 39 exclusion
  witnesses and 87 native query/execution records, in 10.92 seconds locally.
- All 30 second-cycle source hashes and all 24 first-cycle hashes match. Ruff,
  scoped MyPy, existing Tau subset/assurance and claims-registry checks passed.
- [Normative report and user story](tau_swarm_autonomy_20260907.md),
  [replay](tau_swarm_20260907/replay/report.json),
  [validation](tau_swarm_20260907/validation.json), and
  [integration review](tau_swarm_20260907/integration_review.md) record the final
  subject and limitations. Discovery runs are separate from final acceptance.

Concrete findings:

- Human permits a breaking API change. Schema-first allows three joint plans and
  retains breaking-change freedom; verification-first allows twelve plans and
  excludes breaking changes. The complete relation has fifteen plans.
- With allowed code pairs `{00,01,02,10,11,20}`, both orders from seed `00`
  produce three choices. Seed `11` exposes the four-choice product
  `{0,1} x {0,1}`. Trying all orders from one seed is insufficient for optimality.
- Individually feasible choices, or parallel expansions from a stale snapshot,
  can conflict when combined. Compilation updates must be sequential; issued
  choices must use the same subject and environment.

## Fable, prior art and lessons

Two substantive public-context calls succeeded with `claude-fable-5-1` at Max
effort. Fable recommended common-anchor residual sharing in the first cycle and
agent-facing envelopes in the second. It did not inspect repository source or
perform experiments. Treat its statements as suggestions; its second memo's
blanket claim that products are inexpressible should not be repeated as a claim
about all of Tau's BV support. Individual existential projections also do not
establish independently composable agent choices.

The one-sweep algorithm has direct prior art in
[Ignatov, section 4](https://arxiv.org/pdf/1602.07267).
[Polyadic formal concept analysis](https://www.cs.ubbcluj.ro/~dianat/publications/camera_ready_submission1_Rudolph_Sacarea_Troanca.pdf)
defines these maximal products; [Rudell, section 4.3.6](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1986/ERL-86-65.pdf)
explains why all variable orders can miss larger products. Claim original
application integration and checked experiments, not a newly invented theorem.

[Lessons learned](tau_research_lessons_20260907.md) records the human/LLM framing
and the first cycle's representation, semantic and validation lessons.

## Next research and preservation

The third cycle is complete as of 2026-09-08 UTC:

- [Tau artifact workbench](tau_workbench_20260908.md) connects local Tau choices
  to exact ordinary Python source in a bounded pure profile. The package,
  parser-derived CLI, independent CPython runner and fifth Lean proof are
  implemented. Final validation passed 299 native-enabled tests.
- The message pilot checks all 512 source combinations, of which 392 pass.
  Exact grouping reduces global class checks to 64. Default independent domains
  permit 128 source combinations; an oracle-selected valid anchor permits 192,
  the maximum product in this fixed pilot.
- Six agent-written equivalent replacements pass, with zero new Tau queries
  for local admission. All eight assembled revisions pass native Python replay.
  An explicit negative control fails in 24 of 64 relevant contexts.
- Classical Boolean factoring reduces the rendered residual from 4,080 to 541
  bytes. Two alternating pairs measured 13.089 versus 2.025 seconds median
  native compilation, a bounded 6.46x improvement over enumeration. Cached
  central checking is still much cheaper on this tiny workload.
- The final replay binds 49 source/evidence files, preserves all 24 first-cycle
  and 30 second-cycle hashes, and records 113 native operations plus independent
  CPython execution. See [validation](tau_workbench_20260908/validation.json)
  and [lessons](tau_workbench_lessons_20260908.md).

The following preservation rules continue to apply. The earlier planning-to-code
gap is now closed only for the declared finite profile; the next test is a real
ZenoDEX adapter workload and measured rework, as ranked in the third-cycle study.

1. Read root/path guidance and this checkpoint; inspect current Git status.
2. Preserve first-cycle source hashes. New follow-on modules are intentionally
   separate, so the successful first snapshot stays replayable.
3. Keep the completed second-cycle source snapshot and replay intact. Use a new
   output directory for any future replay and a new subject after code changes.
4. Connect a real ZenoDEX developer-and-swarm workload to the artifact checker.
   Measure accepted edits, human corrections and renegotiations against cached
   centralized checking. The finite message pilot does not measure human time.
5. Study preference-aware seed and order selection. Both can change useful
   freedom; neither currently has a general optimality claim.
6. Tau Net node integration, full-repository/release gates and a source-bound
   Python-to-Lean refinement proof remain outside the completed study.
7. Commit only a finished, successful, reviewed slice if still authorized. Check
   staged paths first and include only this task's files.

The native executable used throughout reports `0.7.0-alpha (d80aa50c)`, SHA-256
`b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`.
Choose it explicitly through `TAU_COMPOSITION_BIN`; source-to-binary build
correspondence remains unestablished. No new dependencies were installed.
