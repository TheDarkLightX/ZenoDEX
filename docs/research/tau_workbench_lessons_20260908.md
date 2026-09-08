# Lessons from compiling agent choices into actual code

Date: 2026-09-08 UTC. Experimental research; authority: NONE.
See the [study](tau_workbench_20260908.md) and
[replay](tau_workbench_20260908/replay/report.json) for measured evidence.

## What changed our engineering decisions

The earlier Tau Swarm compiler distributed Boolean planning choices. This
cycle gives those choices a concrete meaning: exact candidate source bytes,
complete component behavior, and an independently executed assembled program.
The highest-return change was closing that semantic gap. Additional report
fields alone would not have demonstrated useful work by a developer's swarm.

1. **Count behavior and source variants separately.** Twenty-four candidate
   files in the pilot represent twelve stage-specific behaviors. Grouping exact
   behaviors reduces 512 bundle checks to 64 class checks. Ordinary centralized
   checking can use the same grouping. The eightfold reduction belongs to the
   quotient, and equivalent-source reuse is available to both designs.
2. **Tau contributes compatible freedom in advance.** A local domain can contain
   multiple different behaviors while guaranteeing that every admitted choice
   works with every admitted choice of the other stages. The pilot's default
   product contains 128 actual bundles. Choosing from the complete feasible set
   of 392 bundles requires coordinating the choices; it is not an independent
   per-agent product.
3. **The complete intermediate domain matters.** A decoder that agrees with the
   desired result on the original 64 payloads can fail after another stage adds
   a tag. Full 256-value component equivalence prevents this particular mistake.
   The explicit negative control survives all initial payload checks but fails
   in 24 of 64 admitted encoder/adapter contexts. Its first saved failure is
   input 0, expected 0, observed 64. The Lean file includes a smaller Boolean
   counterexample to the initial-input-only rule.
4. **Human preferences select which freedom to retain.** Encoder-first and
   decoder-first expansion both permit 128 source bundles, while allocating
   behavior choices differently. A different valid anchor permits 192 bundles.
   An exhaustive 3,375-product oracle establishes the maximum for this pilot.
   Finding that anchor used bounded search outside Tau's sweep; the sweep is
   still an inclusion-maximal-product algorithm.
5. **Representation is an actionable Boolean-algebra lever.** Classical Shannon
   factoring preserves all 64 selector rows and reduces the rendered residual
   from 4,080 to 541 bytes. The paired replay measures the native compiler cost
   independently of source analysis. This is application-side engineering using
   established algebra, with no change to Tau's decision procedure.
6. **Cheap central checking remains a serious baseline.** On this tiny domain,
   cached centralized checking takes milliseconds and Tau compilation takes
   seconds. Local autonomy may be useful when coordination is expensive, work
   recurs, or policies change. This experiment does not measure those economics
   or establish that using Tau is the cheapest choice for a small one-off task.

## Lessons from review and falsification

The parser must describe exactly the bytes CPython will read. An encoding
declaration could otherwise make UTF-8 interpretation and native interpretation
disagree. The admitted profile now accepts only the checked UTF-8 encoding,
validates the whole syntax tree, and rejects unsupported source before loading.
Dead branches also remain within the grammar and resource limits.

Claimed behavior tables remain observations. Public builders rebuild from raw
tasks, and final selections and revisions evaluate the exact source again.
The independent replay checks both full component tables and the first failure
and checked-input count for each assembled bundle. Correct component tables
alone did not prevent a malformed child result from falsely claiming joint
success; three failing regressions exposed and closed that gap.

Evidence handling must preserve the work it describes. Tests now cover another
writer winning output-directory creation, a partial CLI artifact write, test or
plan drift during replay, and preservation of LF/CRLF candidate input bytes.
Reports are published after their dependencies. None of these observations is
a credential or a substitute for a runtime acceptance mechanism.

The fifth Lean proof establishes substitution through total closed-domain
pipelines and safe/maximal product lifting under explicit correspondence
premises. It does not verify the Python AST interpreter, CPython, source hashes,
or the native Tau executable. Machine-checked abstraction and measured
implementation agreement must remain separately named.

## Next opportunity, ranked by expected value

1. **A real finite ZenoDEX adapter migration.** Choose one existing control
   interface with a small, complete state alphabet, such as a finite status/tag
   translation. Pin the real producer and consumer, specify their observable
   contract, and compare actual proposed edits and rework against cached central
   checking. Advance only if the actual adapter fits an exact profile; never
   truncate monetary values to make a demonstration fit eight bits.
2. **Preference-aware repair of a changed component class.** When a replacement
   has new behavior, derive the smallest justified changes to other agents'
   admitted domains. Compare against full recomputation and the existing Tau
   repair/composition primitives. Human priorities and a valid anchor must remain
   explicit. This is a research target, not an implemented renegotiation engine.
3. **Proof-backed component summaries for wider programs.** Replace finite tables
   with independently checkable summaries only after defining the abstraction
   and a refinement proof. General Python merging, effects, temporal state and
   Tau Net rule admission substantially enlarge the trusted boundary.

The current result is a reusable finite artifact workbench plus a measured
representation improvement. It does not establish foundational novelty,
general swarm productivity, production readiness, or patent clearance. Original
application code and separately installed Tau retain their separate provenance.
