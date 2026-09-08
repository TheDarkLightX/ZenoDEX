# Lessons from the Tau composition and swarm cycles

Date: 2026-09-07. Research notes, not a production claim.

## The user is a person with an LLM or an agent swarm

A useful interaction begins with a person's goals, acceptable tradeoffs and
authority limits. Agents propose explicit requirements, candidate plans and
explanations. Tau computes consequences of the formalized inputs. The person
can inspect counterexamples and revise intent; an authenticated host and its
deterministic verifier still decide which external effects may occur.

This is more ambitious than using Tau as a final yes/no filter. A useful next
primitive should change what a human-and-swarm team can explore or accomplish:
reduce coordination, expose exact choices, preserve compatible alternatives,
or discover the precise dependency preventing independent progress.

## What the first cycle taught us

1. **Choose a representation problem with a measurable cost.** Small native
   symbolic solutions can be reused without enumerating a complete truth table.
   This is a different workload from OrbitSynthesis's finite relation inputs.
   Equivalent-task baselines are needed before claiming one replaces the other.
2. **Correct local components can interfere.** A repair can restore an action
   another requirement removed. Preservation implications and composition order
   are computational information, not merely documentation.
3. **Known algebra can expose a useful software opportunity.** Fable suggested
   common-anchor residual sharing. Independent derivation, Lean proofs and native
   replay made that suggestion concrete. Historical novelty was not established.
4. **Compact compilation and useful choices are different objectives.** A shared
   anchor can reset many otherwise-useful controls. For a human with several
   planning agents, preserving each agent's permissible alternatives can matter
   more than choosing one cheap fallback.
5. **Counterexamples are part of the product.** Small witnesses separated
   idempotence from safety, feasibility from an order's safe domain, and a true
   order cover from an implicit fallback. They give agents concrete revision
   tasks that a human can understand.
6. **A bounded native adapter needs bounded host work.** Native query caps did
   not constrain expression expansion after composition. Check expanded size
   and depth before recursive consumers, and retain an explicit unknown result.
7. **Test against the actual executable.** Host round trips missed native
   precedence; old runners changed generated definitions; a native constant
   controller could stop after one row. Native differential execution found
   distinctions that internal consistency tests could not.
8. **Treat model rankings as hypotheses.** Fable's successful Max-effort memo
   used public context only. It did not inspect source or run checks. Models
   can generate promising research directions without owning acceptance.
9. **Keep source, executable, legal and novelty evidence distinct.** An executable
   hash is useful evidence without being a reproducible build. Original code and
   a standard mathematical theorem do not establish patent freedom to operate.

## Second cycle: independent choices for a coordinated swarm

The second prototype uses Tau to derive separate choice spaces for
different agents such that **every combination of locally permitted choices
satisfies the shared global contract**. The human can then let agents work
concurrently within these formal spaces, with explicit conditions for
renegotiation. Actual agent execution and generated-code verification remain
outside the prototype.

For example, a developer and three agents own different proposed feature flags.
The developer supplies hard compatibility constraints and a known-valid seed.
The desired compiler returns a local constraint to each agent, retaining as many
independent alternatives as the chosen construction permits. The team can see
which global dependencies prevent additional autonomy.

The implemented algorithm uses universal projection of other agents' admitted
choices. Its result is an inclusion-maximal product. Product volume, economic
utility and preservation of a particular agent's freedom are separate
objectives. The direct prior art is
[Ignatov's sequential polyadic-concept expansion, section 4](https://arxiv.org/pdf/1602.07267).
The contribution under evaluation is the original Tau application, native
obligations, local gates, human-facing explanations and checked examples.

Further practical discrimination requires comparison against per-proposal centralized checking and
the first repair compiler. Measure surviving alternatives, native reasoning
cost, downstream coordination avoided in a declared workload, and cases where
coupled choices make independent envelopes too restrictive. If the construction
only yields a renamed mutex or trivial singleton, it has not earned a strong
practical claim.

## What the second cycle taught us

1. **Feasible local choices can still conflict.** An existential projection
   answers whether a choice has some compatible counterpart. Independent
   delegation requires compatibility with every combination the other agents
   may select. Universal cofactors preserve that distinction in the software.
2. **Compilation order is a human preference.** In the API-change example with
   breaking changes permitted, schema-first retains breaking-change freedom in
   a three-plan product. Verification-first exposes twelve independent plans
   while excluding breaking changes. The complete relation has fifteen plans.
   A larger count alone does not establish greater value for the human.
3. **Search the representation and the seed.** Both orders from the triangle
   example's zero anchor yield three combinations. A different valid anchor
   yields four. Exhausting the order space does not exhaust the space of useful
   products. This failure also has classical Boolean-minimization prior art in
   [Rudell, section 4.3.6](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1986/ERL-86-65.pdf).
4. **Compute sequentially, then delegate independent choices.** Expansion from
   the current domains preserves safety. Merging full expansions calculated
   against an old common snapshot can violate the global contract. A Lean
   counterexample and finite tests make that distinction explicit.
5. **Explain the cost of added freedom.** For each excluded local choice, show
   an allowed choice of the other agents and the named requirement their
   combination violates. This gives a human and their swarm a concrete
   renegotiation task. An exclusion is specific to the selected product; it
   need not mean that the choice is globally infeasible.
6. **Bind proposals to a common problem and environment.** A local choice from
   a different contract snapshot or human permission setting cannot simply be
   combined with current proposals. Bind both explicitly and recheck the
   original global contract when combining. Hashes identify the snapshot;
   caller-constructible records carry no execution credentials.
7. **Prior-art review can improve the result without proving novelty.** Finding
   the exact existing theorem redirected effort toward application semantics,
   informative failure cases and replay. A Tau implementation of known algebra
   can be useful without extending Tau's underlying decision procedure.
8. **Size a local interface by its local problem.** The first swarm compiler
   passed every global variable name into each local projection parser. Its
   64-alias parser bound then rejected a one-variable result in a 65-coordinate
   contract. Restricting aliases to the current block and environment closed
   that avoidable limitation. The native 1+64-block regression now passes
   without enumerating the global assignment space; local representation
   bounds still apply.
9. **Check model-written evidence tooling before using its results.** Opus
   returned seven completion files, including the replay tool. One change
   recorded a missing required source as `absent`, allowing an incomplete
   source record. Parent review restored a hard rejection and tested source
   drift as a failed replay. Model-generated validation is itself reviewed
   code, not independent evidence.
10. **Define the encoder's representable subset.** The in-memory term model
    admitted wider or noncanonical terms than the JSON decoder. The encoder
    now validates its output through that decoder and rejects any lossy or
    over-budget representation. Two failing regressions reproduced the gap
    before repair; independent review closed it afterward.

## Next practical experiment

Connect a small developer-and-swarm workflow to an independently checked
artifact contract: declared file ownership, compatible API changes and required
test evidence. Keep the human's authority and the actual code checker explicit.
Compare completed accepted tasks, human corrections and renegotiations against
a centralized checking baseline on fixed tasks. The current Boolean choice
counts do not measure those outcomes. Any stronger productivity claim requires
this additional evidence.

This file captures lessons in the repository. No persistent assistant memory,
production claims, deployment permissions or network rules are changed.
