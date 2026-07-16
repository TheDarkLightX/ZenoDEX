---
title: workflow
type: note
permalink: autonomous-tau-dex-review/experiments/math-research-memory/workflow
---

# Workflow

## Updated lesson from critical-region dispatch v1

- On the bounded exact corpus of `772` Jacobi/Gegenbauer obligations, adaptive
  regionalization mattered and derivative-root guidance did not.
- Refining only failing Bernstein leaves preserved `772/772` positive accepts
  and `0/7` false accepts while reducing total pieces from `3592` to `2928`,
  maximum pieces from `16` to `8`, and canonical bytes from `4076028` to
  `2663176`.
- The six-leaf budget is the clearest decision metric: equal subdivision leaves
  `240` `UNKNOWN`, while midpoint adaptive refinement leaves `5`.
- A derivative sign-variation landmark snapped to the `1/64` grid uses `2943`
  pieces and `4270358` bytes. It remains a falsified comparator because it is
  larger than midpoint refinement and slightly larger in bytes than equal
  subdivision.
- Exact coefficient-interpolated split points are an arithmetic resource risk:
  recursive denominators depend on coefficient height. Certificate compilers
  should bind denominator geometry independently of input coefficient height.
- The promoted research method is failing-region midpoint refinement backed by
  ordinary Bernstein certificates. Critical-point local models remain a
  separate future lane requiring a corpus where they beat this simpler policy.
- `AdaptiveBernsteinRegionCertificates.lean` now proves arbitrary-degree
  Bernstein-combination nonnegativity, exact power-to-Bernstein conversion,
  recursive de Casteljau evaluation, affine left-subdivision correctness, and
  adaptive-cover lifting. The Julia compiler binding has 12 exact differential
  checks. The remaining affine Lean gap is the right subdivision array.

## Updated lesson from the approximation-defect receipt bridge

- A paper-derived local-model architecture becomes executable only after its
  error components, region coverage, and overlap ownership have canonical
  machine-checkable representations.
- Separate `certified_bound` from `allocated_bound`. The allocation must
  dominate its upstream certificate before the total allocation can be
  compared with the model margin.
- Bind the whole receipt body, including certificate identifiers, regions, and
  overlaps, under one deterministic root. Arithmetic acceptance still depends
  on the external validity of those upstream certificate identifiers.
- The formal core is small: componentwise budget monotonicity, local absolute
  error gluing, finite-cover lifting, and overlap model mismatch by triangle
  inequality.
- The follow-on dispatcher experiment resolved the open algorithmic question:
  failing-region midpoint refinement reduces piece count and bounded
  `UNKNOWN`, while derivative-landmark selection does not improve the selected
  compiler.

## Updated lesson from the Deift-Zhou and Wang-Ma steepest-descent pass

- Nonlinear steepest descent transfers to ZenoDEX as a certificate-decomposition
  architecture: global factorization, decay-oriented deformation, localization
  at critical points, universal local models, explicit interaction bounds, and
  matched reconstruction.
- The dbar extension adds a weaker-regularity pattern: replace analytic
  continuation with an explicit interpolation defect and certify that defect
  through a separate norm/error budget.
- The first credible ZenoDEX seam is the existing high-degree
  Jacobi/Gegenbauer/Bernstein certificate menu. The papers do not establish any
  AMM, oracle, liquidation, or routing theorem.
- Promotion requires finite, verifier-checkable remainder constants. Asymptotic
  `O(...)` notation and floating-point local solves remain suggestion evidence.
- The follow-on cycle completed both targets: the local-model residual gluing
  theorem checks in Lean, and the dispatcher benchmark selects failing-region
  midpoint refinement over derivative-landmark splitting.

## Updated lesson from v197

- Gamification should split token rewards from non-token progress.
- The token reward law is:
  `reward <= min(VerifiedValue, BudgetCap, SybilAdjustedCap, TreasuryCap)`
  plus proof, anti-sybil, and receipt-scope gates.
- The bounded replay checks `12` quests: `5` accepted token rewards, `1`
  accepted XP-only quest, `6` rejected adversarial quests, and `0` invariant
  failures.
- Lean now checks the reward-meet spine: a reward below the four-way meet is
  below verified value, budget, sybil-adjusted cap, and treasury cap.
- Next cycle should connect quest receipts to real proof-mining, disaster
  witness, liquidity-support, and market-maker receipts.

## Updated lesson from v198

- Chaos engineering can be modeled as typed morphisms over a disaster-potential
  vector rather than as unstructured fault injection.
- The core law is:
  `SafeTransition(s -> s') := Risk(s') <= Risk(s) OR RecoveryCertificate(s -> s')`.
- The bounded replay checks `108` chaos cases: `54` accepted, `54` rejected,
  `12` direct repairs, `42` certified recoveries, `12` catastrophic rejections,
  and `0` invariant failures.
- Lean now checks the generic spine: if an accepted transition increases risk,
  the recovery-certificate branch must be present.
- Next cycle should map existing disaster-state harness axes into this risk
  vector so fuzzing can optimize for accepted risk increases.

## Updated lesson from v195

- An override branch must not be a free-form escape hatch. It needs its own
  witness language.
- The minimal exact bounded language for assumption-change packets uses `8`
  atoms: domain, surface binding, cap reference, nonce freshness, signer
  threshold, registry root, epoch freshness, and no-user-net acknowledgement.
- The bounded replay checks `13` packets: `2` valid, `11` adversarial, and
  `0` invariant failures. Every required atom has a private negative witness.
- Weaker languages such as text-only, authority-only, fresh-authority-only, and
  cap-and-ack-only all false-accept bad packets.
- Next cycle should decide whether this override packet language should become
  a concrete JSON schema and checker under `tools/`, or remain a research-only
  design until real governance signing rules are chosen.

## Updated lesson from v194

- Evidence-meet caps become more useful when compiled into a config guard, not
  just reported as recommendations.
- The launch/config guard law is:
  `LaunchFeeOK(surface) := fee_bps(surface) <= MeetCap(surface) OR AssumptionChangeOverride(surface)`.
- The bounded replay checks `10` candidate configs and `18` surface fee lines:
  `2` accepted without override, `3` accepted with explicit assumption-change
  overrides, `5` rejected, and `0` config invariant failures.
- The strongest distinction is semantic, not numeric: under-meet configs may
  claim the current evidence-backed user-net cap, while over-meet or uncapped
  configs can only proceed as explicit assumption-change reviews.
- Lean now checks the guard spine: if `(fee <= cap OR overrideRecorded)` and
  `cap < fee`, then `overrideRecorded` must hold.
- Next cycle should test the same guard against adversarial governance override
  packets: stale cap references, reused assumption IDs, signer threshold drift,
  conflicting override domains, and replayed approvals.

## Updated lesson from v193

- Fee caps should compose by meet, not by replacement. The new law is
  `MeetCap(surface) := min {cap(source, surface) such that cap exists}`.
- The meet compiler turns v190-v192 recommendation artifacts into `6`
  conservative user-value caps: `2` execution-backed and `4` synthetic-only.
- The execution-backed meet caps are lower than the execution-only caps because
  stress evidence is tighter: route surplus meets at `1800` bps and exact-out
  savings meets at `2000` bps.
- Lean now checks the algebraic spine: if `fee <= min(capA, capB)` and one
  source cap is safe relative to measured value, then user net remains
  nonnegative.
- Next cycle should promote the meet-cap artifact into a small runtime config
  checker that rejects any launch config exceeding the evidence meet unless an
  explicit governance override records the assumption change.

## Updated lesson from v192

- Synthetic calibration is not enough; v192 derives receipt values from actual
  CPMM router arithmetic in deterministic fixture markets.
- The execution-derived value laws are:
  `RouteSurplusValue := best_route_amount_out - direct_route_amount_out` and
  `ExactOutSavingsValue := direct_route_amount_in - best_route_amount_in`.
- Current result: `receipt_count = 20`, `accepted_count = 18`,
  `rejected_count = 2`, `route_receipt_count = 9`,
  `exact_out_receipt_count = 9`, `candidate_review_cap_count = 2`,
  `launch_parameter_claim_count = 0`, and
  `total_execution_receipt_invariant_failures = 0`.
- Next cycle should attach the same receipt emission shape to real quote/API
  traces or replay logs, so cap drift can be measured against market data.

## Updated lesson from v191

- A fee-cap model is not credible if every cap is backed by one fixture row.
  v191 adds a deterministic 32-row stress corpus with three accepted samples
  for each user-paid surface plus explicit adversarial rows.
- The receipt-to-cap bridge now has a stronger model-bug check: expected bad
  rows must reject for exact reasons, strict sample thresholds must fail
  closed, retail caps must remain under hard value rails, and no generated
  cap may claim launch-parameter status.
- Current result: `receipt_count = 32`, `accepted_count = 27`,
  `rejected_count = 5`, `candidate_review_cap_count = 6`,
  `launch_parameter_claim_count = 0`, and
  `total_stress_invariant_failures = 0`.
- Next cycle should replace synthetic rows with real route/protection/API
  receipts and keep the synthetic corpus as a regression oracle.

## Updated lesson from v190

- Tokenomics revenue work must model explicit fee surfaces, not just abstract
  value flow or staking allocation.
- Staking is an allocation/commitment surface; revenue comes from measured
  route surplus, exact-out savings, solver surplus, protection/automation,
  pro receipts/API, integrator flow, treasury market-making, arbitrage
  recapture, and bounded insurance premiums.
- Penalties can protect commitment schedules, but a policy that depends on
  penalty revenue is unhealthy and should fail the revenue model.
- The v190 model bug audit is now part of the method: gross revenue
  nonnegative, user-net identity, net-revenue identity, sink budget
  non-overallocation, survivor-rule consistency, named falsifier expectations,
  and optional Julia-vs-Python accounting cross-check.
- Add mutation sensitivity before trusting a tokenomics oracle: deliberately
  corrupt negative gross revenue, user-net identity, net-revenue identity, sink
  budgets, and survivor flags; the v190 receipt catches `5/5`.
- Add report-integrity replay before trusting generated research artifacts:
  regenerate the bounded search and compare counts, best survivor, model audit,
  and named-policy summaries. v190 passes `11/11` integrity checks.
- Add metamorphic laws for fee/reward/sink monotonicity so the model rejects
  local direction errors even when totals still look plausible.
- Close the "measured value" gap with typed receipt calibration before treating
  fee caps as serious: v190 now maps JSONL revenue-surface receipts into
  empirical value-density summaries and rejects rows where fees exceed measured
  value, protocol surplus capture exceeds surplus, penalties are primary, wash
  risk is too high, or primary revenue is negative net.
- Convert calibration into caps only through a fail-closed recommendation
  layer: user-paid caps require accepted user-fee receipts and hard value rails;
  penalties and protocol-surplus captures are explicitly not launch fee caps.
  The current fixture emits `6/11` review caps and `0` launch-parameter claims.
- Next cycle should feed real quote/action/API receipts into the calibrator and
  split retail fee surfaces from pro/integrator fee surfaces.

## Updated lesson from v182

- DLMF and Julia are most useful to this repo as a certificate-discovery
  pipeline, not as runtime dependencies.
- The first strong survivor is an exact Bernstein interval sign certificate for
  bounded univariate polynomial inequalities. This is a safe Tau/FIRE fast path:
  success discharges the universal inequality, failure remains `UNKNOWN`.
- Subdivision is the key optimization knob. In the bounded corpus, whole-interval
  Bernstein certificates solved `24/41` positive cases, while four equal
  subintervals solved `41/41`.
- The next frontier is proof closure:
  1. wait for Aristotle on the certificate soundness packet,
  2. integrate only after local `lake build` and placeholder scan,
  3. then prototype a Tau tutorial/demo that emits a Bernstein certificate and
     falls back to QE on failure.

## Updated lesson from v166

- Tokenomics modeling must define value before scoring policies.
- In a post-AGI setting, raw output and effort are weak value signals because
  AI can generate abundant candidate work. The scarce object is verified
  constraint closure: risk reduced, revenue enabled, trust added, cost reduced,
  liquidity quality improved, or future option value preserved.
- A hyper-deflationary launch should optimize productive deflation, not pure
  burn. The bounded winter grid rejected 100% burn and found survivors only
  when contributor, adopter, and treasury allocations remained positive.
- "Ponzi-shaped" should be modeled as a backing/funding dependency, not as a
  generic rejection of reflexive loops. Healthy loops pay from usefulness, fees,
  and budget; dangerous loops require future entrants to pay old promises.
- Attention, mining, and contribution meaning are legitimate post-AGI value
  candidates only after mapping them to scarce verified effects.
- Next cycle should replace scalar `VerifiedValue` with a vector-valued FIRE
  value score and test sybil/wash-trade exploitation plus PonziPressure against
  earned allocation and rebate mechanisms.

## Updated lesson from v167

- "Better than Bitcoin" must be defined as a value-object claim, not a price
  prediction.
- Bitcoin's early hope object combined scarcity, permissionless entry,
  security work, narrative clarity, and visible contribution. Modern Bitcoin
  retains scarcity and liquidity but has weaker ordinary non-cash contribution
  paths.
- The first FIRE frontier requires all of:
  productive deflation, verified work/fees, proof-work-usage hybrid entry,
  capped bounty/rebate rewards, bounded governance, and an earned-hope
  narrative.
- Next cycle should stress this object against adversarial attention farming,
  fake community metrics, bot mining, and governance capture.

## Updated lesson from v168

- Price appreciation should be explicit in FIRE tokenomics. The honest question
  is not whether price matters, but which causal channel drives appreciation.
- In post-AGI settings, an AI-owned protocol can accumulate cashflow and price
  pressure while still leaving humans outside the causal loop.
- The right FIRE metric is participatory price appreciation: price pressure
  multiplied by human participation in the source of that price pressure.
- Next cycle should turn the hand-scored components into an adversarial
  simulation: bots can fake attention, AI agents can capture work, whales can
  dominate ownership, and governance can redirect sinks.

## Updated lesson from v169

- Trust economics must distinguish entitlement from capacity. Reward should be
  bounded by verified contribution value; trust should control task risk,
  collateral, limits, finality, and attestation weight.
- A newcomer lane must actually reserve some low-risk work for newcomers. A
  label alone is not enough; the first version failed because trusted builders
  still won all easy tasks.
- The corrected capacity-plus-newcomer-lane mechanism improves human
  participation and participatory price while preserving zero unearned premium.
- Next cycle should add explicit attackers: sybil newcomer farms, AI workers
  with low human agency, whale capital, and governance parameter capture.

## Updated lesson from v170

- Newcomer access must be adversarially modeled. Naive access was captured by
  bot farms in the toy market.
- Capital gates reduce fake loss but can exclude cash-poor humans; proof-only
  markets risk AI capture; attention lanes risk bot capture.
- The first robust shape is hybrid: high receipt quality, per-identity rate
  limits, slashable attestation, proof weighting, and bounded newcomer quotas.
- Next cycle should add explicit price/liquidity dynamics so reward capture can
  be linked to token float, buyback depth, and price impact.

## Updated lesson from v171

- Price appreciation must be bridged to market mechanics. A hand-scored
  pressure metric can hide liquidity fragility and reward overhang.
- Thin liquidity can win raw price return while being a worse FIRE object.
- Human-owned rewards need a release/overhang constraint; otherwise the model
  rewards emissions that later become sell pressure.
- The next price cycle should add adversarial liquidity withdrawal and whale
  sell shocks, then measure recovery under buyback depth and treasury support.

## Updated lesson from v172

- Deflationary tokenomics must be tested under shock, not only under quiet
  growth.
- The bounded shock model rejected three tempting simplifications:
  thin-liquidity hype collapses under LP withdrawal and selling, pure burn has
  too little recovery budget, and over-rewarded participation carries too much
  reward overhang.
- The first survivor is a recovery circuit: treasury defense, reward throttling
  during drawdowns, liquidity support, buyback/burn, and human-owned rewards.
- Next cycle should test governance abuse of emergency controls and calibrate
  shock parameters against real AMM depth, sell-size, and fee-volume data.

## Updated lesson from v173

- Recovery circuits introduce governance attack surface. Emergency controls
  should be modeled as adversarial mechanisms, not only as stabilizers.
- Two opposite failures matter: false triggers that let insiders spend treasury
  opportunistically, and frozen controls that block legitimate shock response.
- The first survivor is evidence-triggered recovery governance: public receipts,
  TWAP-style guards, spend caps, cooldowns, slashable authority, and human
  reward floors.
- Next cycle should turn this into a receipt language: what exactly must be
  witnessed for drawdown, urgency, cap compliance, cooldown, and protected
  human reward floors?

## Updated lesson from v174

- The first recovery receipt language compresses 9 raw obligations into 3 exact
  macros over the bounded field cube: trigger, spend policy, and authority.
- The compression is useful because it gives a small checker surface without
  hiding the raw obligations. Each macro is still a conjunction of concrete
  fields.
- The next honest attack is upstream truth: if collusive providers can lie
  about TWAP, drawdown, slashability, or receipt publication, the three-macro
  checker can still accept a bad action.

## Updated lesson from v175

- Recovery receipts need provider-quorum assumptions stated explicitly. The
  compact law for the bounded model is `f < q <= n - h`.
- Under `n = 5`, `f = 2`, and `h = 1`, the minimal viable quorum is 3
  independent groups; full slash coverage is required for accountability.
- The next attack is common-control aliasing: three nominal providers are not
  enough if they are economically or operationally the same actor.

## Updated lesson from v176

- Provider independence must be witnessed, not assumed from key count.
- The bounded common-control model compressed five roots into three checks:
  economic identity, operational identity, and slash-pool separation.
- The next difficulty is privacy and verifiability: beneficial ownership and
  operator independence are exactly the fields attackers want to hide.

## Updated lesson from v177

- Privacy cannot be added after the independence check. The private receipt must
  jointly prove hidden independence relations, context binding, fresh registry
  membership, and unlinkability.
- Commitments alone are insufficient, and unbound ZK proofs are replayable or
  substitutable across provider keys, epochs, or evidence domains.
- The next frontier is a concrete circuit/interface: registry commitment,
  domain-separated nullifier, provider-key binding, epoch binding, and
  verifier-facing receipt schema.

## Updated lesson from v178

- A ZK proof blob is not a verifier receipt. The runtime boundary must bind
  circuit identity, verifying key, schema hash, registry root, provider key,
  epoch, evidence domain, relation statement, nullifier scope, and canonical
  privacy output.
- Partial binding leaves concrete substitution/replay families alive, even when
  the underlying ZK relation is sound.
- The next frontier is implementation wiring: define the runtime verifier
  schema and fail-closed parser/checker that enforces this interface.

## Updated lesson from v179

- ZenoDEX/FIRE needs reputation, but the safe shape is capacity and
  accountability, not yield.
- Trust vectors should be domain-specific, receipt-backed, decaying,
  slash-aware, and independence-aware.
- Trust-yield multipliers and stake-weighted reputation recreate old-power
  advantages. Flat receipt rewards preserve stale reputation. The next frontier
  is governance-safe bounds on reputation-vector weights.

## Updated lesson from v180

- Oligarchy is not mathematically unavoidable, but oligarchic drift is the
  default attractor when current power can increase the future weight assigned
  to current power.
- A reputation system that says "trust is capacity, not yield" still needs
  governance rails on the trust-vector weights. Otherwise stake, old receipts,
  or weak insider attestations can dominate task capacity.
- The bounded v180 envelope caps stake and old receipts while requiring recency,
  independence, domain fit, and slashing to remain live.
- The next frontier is an auditable runtime receipt for reputation parameter
  changes: a governance update should prove that new weights remain inside the
  safe envelope and that any exception is timelocked, bounded, and challengeable.

## Updated lesson from v181

- The best low-friction revenue pipe is not "charge a small fee everywhere."
  It is "charge against measured value density."
- Fee-on-improvement is structurally safer because its fee base is the surplus
  it created. Notional-based protection, receipt, automation, and integration
  fees can overcharge even when their static bps rail looks small.
- The bounded launch corpus makes basic user receipts look like a bundled or
  free feature unless a receipt creates measurable surplus. Advanced integrator
  receipt fees should be separated from retail safety receipts.
- The next frontier is calibration: replay real quote/action corpora and mine
  per-action value-density distributions before finalizing launch fee rails.

This file stores the high-signal research process and memory, not raw hidden chain-of-thought.

## Current working method

1. Pick a structural target.
- Prefer quotients, covers, cocycles, semirings, rewrite systems, potentials, basins, or obstruction bases.
- Avoid pure heuristic tuning unless it exposes a reusable object.

2. Choose the smallest honest domain.
- Use bounded DEX-shaped corpora first.
- State explicit support and falsification conditions.

3. Attack naive formulations quickly.
- If a theorem or witness fails, change the object definition rather than rationalizing the failure.
- Preserve falsified branches because they usually reveal the missing invariant.

4. Promote only geometry-changing objects.
- Good signs:
  - state compression
  - lower exact-evaluation count
  - lower unresolved overlap mass
  - lower obstruction norm
  - monotone descent under canonical rewrites
  - better admissibility under the same caps

5. Separate local from global.
- Local: patches, defect laws, rewrite steps, residual operators.
- Global: covers, cocycles, closures, basins, normal forms.
- The best objects link the two through a compositional law.

## Tactics that have produced wins

- Normalize by symmetry.
- Abstract to numerical invariants.
- Carry curvature explicitly.
- Replace dense failures with sparse obstruction sets.
- Replace raw search spaces with canonical normal forms.
- Prove a stronger compositional inequality first, then weaken.
- When transport or cost minima collapse, switch to potential/energy geometry.

## Current frontier heuristic

When stuck, ask:
- What hidden variable did the current object forget?
- Can that variable be carried by a local section, defect, or potential?
- Can the global problem be reframed as gluing, closure, or quotient over those locals?
- If a minimum-based formulation collapses, is the real invariant a descent law instead?

## Updated lesson from v9-v10

- If quotient basins collapse to a single point, the missing variable may be concurrency rather than classification.
- In rewrite systems, count not only which normal form exists, but how many independent corrections can be executed per round.
- When a transport minimum collapses and a basin count collapses, look for a depth/width law.

## Updated lesson from v11

- If a rewrite system is really preserving serial fibers, count the search space as a shuffle object before doing any permutation work.
- Prefix forests often collapse to a small lattice of progress coordinates; this is a better DP state than the raw trace prefix.
- Exact factorization can be deeper than approximation: use it when the semantics really admits it.

## Updated lesson from v12

- Once a progress simplex exists, do not stop at compression. Try to lift counts, energies, and occupancy measures onto it exactly.
- The right compressed object is often strong enough to support exact path-integral style computation.
- Search gets qualitatively better when a compressed state space is not only smaller but analytically closed under the quantities you care about.

## Updated lesson from v13-v14

- After counts and occupancy, the next natural lift is transport: exact edge flow, cut concentration, additive 1-form integration, and divergence.
- A compressed state object becomes much more valuable once it supports a calculus, not just a catalog.
- When a bounded execution semantics admits exact edge flow, try to move from combinatorics to discrete geometry.

## Updated lesson from v15

- After discrete calculus, the next lift is control geometry: exact future potentials and local branch sensitivity.
- A compressed state object is strongest when it supports not just conservation and integration, but local decision relevance.
- Curvature-like quantities are a good next target once additive integrals are exact.

## Updated lesson from v16-v17

- Exact boundaries can disappear even when control fragility is real. In that case, replace boundary sets with margin fields and occupancy-weighted near-boundary fronts.
- The breakthrough pattern here is refinement of the object, not insistence on the first formalization.
- When an exact geometric locus is too thin, the right invariant may be a thickened front carrying most of the relevant mass.

## Updated lesson from v18-v19

- After discovering a thick instability front, try to coarse-grain it into exact shells rather than refining it indefinitely.
- If the coarse-grained shell process closes exactly, that is usually a better object than the raw front.
- The strongest control-theoretic facts may appear first as hazard monotonicity, not as an optimal closed-form policy.

## Updated lesson from v20

- A DP is often not the end of the story. Once a compressed state object exists, ask whether its value function decomposes into pairwise kernels plus a deterministic debt term.
- The strongest breakthroughs so far came when a recursive exact quantity collapsed into a closed combinatorial kernel.
- When a first closed-form theorem fails away from the source state, look for the missing backlog/debt term rather than abandoning the whole decomposition.

## Updated lesson from v21

- Sometimes the real breakthrough is not a more complicated object but a collapse: a value-function theorem can imply a remarkably simple optimal policy.
- After deriving a closed-form value law, always test whether the induced policy collapses to a simple ranking rule.
- The strongest simplifications came only after building enough machinery to prove they were not naive guesses.

## Updated lesson from v22

- After a strong closed-form policy law appears, perturb it. If it survives a weighted family, that robustness is itself part of the breakthrough.
- Distinguish carefully between value laws and expected-cost laws; the first weighted theorem failed because I crossed that boundary.
- A corrected weaker theorem is better than a false stronger one, especially when it clarifies exactly which operator is being closed-form.

## Updated lesson from v23

- After a law survives one concrete corpus, abstract the instance family before claiming anything like universality.
- If a perturbation family still produces no obstruction, record the empty obstruction search as evidence; that boundary is informative.
- Once bounded universality survives both lower-action weights and pair-specific nonnegative penalties, the next search should target richer, context-sensitive interaction tensors rather than adding more confirmation.

## Updated lesson from v24-v25

- The first genuine obstruction family came from future-gated penalties, not from past-looking pair penalties.
- When a greedy law breaks, look for a graph object behind the failure before inventing a more complicated local heuristic.
- The useful correction was not another ad hoc score; it was the minimum feedback weight of the remaining precedence graph.
- After finding a counterexample family, ask whether the exact Bellman value is really a disguised combinatorial optimization problem on a residual graph.

## Updated lesson from v26

- After finding an exact correction law, immediately widen the model family before treating it as a real breakthrough.
- If the same residual graph law survives denser perturbations, prefer strengthening the law's domain over adding new decorative objects.
- The right progression is: corpus -> abstract family -> first obstruction -> exact correction -> denser-family stress test.

## Updated lesson from v27-v28

- Once an execution-side object stabilizes, port it into a DEX-core-shaped model instead of continuing to decorate the toy model.
- For bounded same-direction CPMM batches, executed volume collapsed to a one-dimensional barrier schedule before surplus did.
- When one objective component collapses exactly and the next does not, keep the quotient and study the residual rather than abandoning the collapse.
- The right next object after an exact quotient is often a residual cocycle or bounded correction law for the remaining objective components.

## Updated lesson from v29

- After quotienting a main objective, look for a constructive graph on the residual states before guessing another scalar correction.
- If optimal states are connected to the quotient canonical state by short adjacency moves that preserve the collapsed objective, that graph is the right carrier for the next theory.
- Local unit bounds on edge defects are more valuable than weak global heuristics; they suggest a future potential or cohomology object.

## Updated lesson from v30

- After finding a constructive residual graph, test whether the local defect is actually an exact local differential before searching for a global potential.
- If the global residual on an edge equals a prefix-local two-step computation exactly, prefer that local form over weaker continuous or sign heuristics.
- Integer quantization matters: a sparse unit-valued local form is usually a stronger object than a smooth approximation that predicts the wrong zero set.

## Updated lesson from v31

- After an exact local differential appears, the next serious question is integrability: build the connected residual graph and test potential consistency before looking for more decoration.
- If the local form integrates and cycle holonomy vanishes, the next obstruction is not cohomological at that level; shift attention to control on zero-delta plateaus.
- A false greedy ascent law is still useful if it identifies the missing quotient: in this case the first correction is plateau collapse, not a new weighted edge score.

## Updated lesson from v32

- If a potential exists but strict positive-edge ascent fails, quotient by zero-delta plateaus before inventing a more elaborate controller.
- Plateau collapse can convert an apparently messy residual policy problem into a tiny DAG with exact ascent guarantees.
- Once the quotient ascent law is exact, the next frontier is the rare higher-depth cases inside that quotient, not the already-resolved global potential layer.

## Updated lesson from v33

- After a quotient law isolates a rare residual family, test whether the remaining potential collapses to one coordinate before reaching for a higher-dimensional tensor.
- In the first rare batch residual family, the right coordinate was outlier slot, not a more complicated permutation statistic.
- After finding a slot law, normalize by additive constants and build a phase atlas; the phase diagram is often the real object, not the raw values.

## Updated lesson from v34

- After finding a small bounded atlas, widen scale before treating the phase count as fundamental.
- A robust object can survive scale broadening even when its phase diagram grows substantially; universality of the carrier and universality of the phase count are different claims.
- Once slot universality survives but the phase atlas expands, the next target is the phase-boundary law, not another universality check.

## Updated lesson from v35-v36

- When a broadened phase diagram becomes richer, look for its finite fan and adjacency skeleton before chasing individual transition formulas.
- If the additive phase object and its adjacent-difference field are in exact correspondence, carry the theory forward in gradient coordinates; boundary laws are usually cleaner there.
- Distinguish three layers explicitly: carrier universality, phase fan geometry, and differential boundary law. The first two are now stable; the third is the live frontier.

## Updated lesson from v37

- After identifying a clean primitive carrier, test the first direct generator for it and isolate the failure set rather than assuming the carrier itself is wrong.
- A sparse defect pocket with a tiny defect alphabet is a strong sign that the next object is a boundary law for the obstruction set, not a replacement of the underlying carrier.
- Separate exact global differential structure from local generator exactness; the former can survive while the latter fails in a narrow regime.


## Updated lesson from v38

- After a local generator fails in slot space, change basis before looking for a correction law; gradient coordinates can expose triangular structure that slot coordinates hide.
- If the trailing differential is exact on a widened family, treat that as a causal filtration law and search for corrections only on the earlier coordinates.
- Once a defect is front-supported, the next target is a small boundary grammar or correction predicate for that front, not a replacement of the whole carrier object.

- Generated gradient symbol, even combined with outlier sign, does not determine the correction exactly on the widened grid; the next correction law must carry additional prefix/load state.


## Updated lesson from v39

- When a front-supported defect survives basis change, test whether it is exactly an omitted-completion effect before searching for a new boundary grammar.
- A triangular correction law is much stronger than an error histogram: it says the failed local generator is missing a structured suffix term, not misreading the whole state.
- Once the correction collapses to a tiny unit-valued alphabet, the next task is a boundary law for symbol selection, not a new global invariant.


## Updated lesson from v40

- After finding an exact omitted-completion law, immediately test whether the correction factors into smaller carry pieces before searching for a boundary grammar.
- If one carry component is sparse and unit-valued, treat it as the true residual frontier; the rest of the correction object is already solved.
- The right progression here was: defect pocket -> triangular filtration -> suffix correction -> carry chain -> sparse terminal carry.


## Updated lesson from v41

- After a sparse carry is isolated, inspect the terminal branch states directly; often the residual is just a one-unit reserve perturbation plus a floor threshold.
- A pure arithmetic floor-crossing law is a better stopping point than an opaque sparse-case classifier.
- Once the terminal correction is reduced to a floor crossing, the remaining frontier is a boundary law for when that crossing occurs, not a new correction object.

## Updated lesson from v133

- When a local frontier theorem is clean but the global pointwise extension
  fails, search for an integrated value budget before trying another pointwise
  identity.
- Compare AMMs at the same external price, not only at the same reserve
  coordinate; many global economic statements want a price-level quotient, not a
  state-indexed curvature field.
- If a paper keeps a normal-form hypothesis that should follow from symmetry and
  homogeneity, promote that derivation into the formal backlog immediately; it
  is usually the missing bridge between elegant analysis and honest theorem
  scope.

## Updated lesson from v132

- When a column-generation or branch-price paper is too global to transfer directly, reuse the current best bounded selector as the incumbent and test the paper as a local destroy-repair operator around that incumbent.
- For exact-out candidate growth, measure the neighborhood cost separately from winner lift; a same-cap slot replacement is a different object from a budget increase.
- If a destroy-repair pass repairs the residual slice without widening the cap, attribute the gain to integrality-aware replacement, not to a larger candidate budget.
- On the widened CPMM smoke slice, compare same-budget repair against cap lift on the exact same threats; if repair wins there, treat slot replacement as the primary object and cap lift as fallback only.
- If no tiny perfect trigger appears, keep the best balanced trigger instead of pretending the branch is solved; high recall plus large spend reduction is a valid intermediate object when the fallback remains fail-closed.
- If the next obvious richer family only adds vacuous conditions, stop enlarging that trigger class; switch to a structurally different trigger family or accept the current gate as the honest stopping point.
- A gated lane can already be the right stopping point if it materially beats the current fallback while preserving benign cases and spending only a small fraction of the always-on repair budget.


## Updated lesson from v132 breakpoint routing

- A near-perfect objective-value transfer is still not promotable if it misses the canonical winner on flat plateaus.
- In routing, separate:
  - value recovery
  - canonical winner recovery
  - quote-call cost
- Continuous or breakpoint seeds can be excellent compression devices while still failing the canonicalization bar; add an explicit plateau-canonicalization step before claiming replacement.

## Updated lesson from v132 breakpoint refinement

- When the only mismatch is a canonical plateau miss, the right refinement is often a small deterministic tie-recovery pass, not a return to the full baseline search.
- A repaired solver can still be meaningfully cheaper than baseline even if the repair is global in one coordinate; measure the repaired cost rather than assuming the fix destroys the gain.
- In this routing seam, the honest progression was:
  - breakpoint seed
  - detect plateau miss
  - add explicit leftward equal-output recovery
  - then reevaluate support and cost separately.

## Updated lesson from v132 exact-out truth audit

- In exact-out split routing, “feasible at full target `Q`” is not the same object as “feasible for some positive split up to `Q`”.
- If a full-domain audit uses only pools feasible at `Q`, it can silently erase winner-threatening pools that are infeasible at `Q` but feasible at smaller legs.
- Before trusting any exact-out support or winner audit, first validate that the full-domain surface includes all partially feasible pools up to the target.

## Updated lesson from v132 exact-out probe ladders

- After correcting the full-domain surface, the next real misses split into:
  - wrong probe scale
  - then slot ceiling
- A single small secondary probe is too weak; some omitted critical pools are only attractive at an intermediate split size.
- A short probe ladder that includes high-mid scales can collapse most of the remaining misses before any cap increase is needed.

## Updated lesson from v132 targeted robustness

- When full truthful sweeps are too expensive, target the empirically dominant threat patterns first instead of stalling.
- A residual random-corpus miss can overstate how much machinery is needed; structured threat-family checks can show that the main object already works on the highest-risk families.
- Separate the main repair object from the residual fallback object explicitly:
  - main object for dominant structured threats
  - fallback only for the unexplained residual slice

## Updated lesson from v132 widened breakpoint routing

- After a repaired bounded solver survives one corpus, widen reserves, fees, and trade-size regimes before promoting it mentally from “interesting” to “supported.”
- Exact support surviving widening is much stronger than a single bounded win; once that happens, shift the frontier from viability to comparative advantage against the next-best repeated-solve candidate.
- For this routing seam, the breakpoint-plus-canonical-scan object survived widening cleanly, so the next useful comparison is amortized neighboring-amount reuse rather than more breakpoint surgery.

## Updated lesson from v132 Newton hot-start routing

- A repeated-solve transfer can be real without becoming the primary solver; compare it against the best repaired primary method, not just the old baseline.
- Preserving exact winners on neighboring-amount sequences is necessary, but not sufficient for promotion; if the mean-call gain over the repaired solver is tiny, classify it as a secondary amortization layer.
- In this seam, hot-start reuse survived exactly but only marginally beat the repaired breakpoint solver, so the larger structural gain still belongs to the breakpoint object.

## Updated lesson from v132 exact-out knapsack routing

- When an exact-out routing surface already has one constrained output dimension, test a direct output-mass DP before assuming the only honest approach is full selected-domain enumeration.
- A paper can still transfer even if its full asymptotic theorem is not reproduced; the important question is whether its structural DP/compression idea collapses the actual bounded oracle surface.
- In this seam, the first CPMM selected-domain corpus already collapsed exactly to an output-mass DP, so the next frontier is widening and curve-family scope, not existence.

## Updated lesson from v132 widened exact-out DP routing

- If an allocation law survives widened CPMM and supported non-CPMM families, stop treating the inner allocation search as the main bottleneck.
- Separate two layers explicitly:
  - selected-pool-set allocation
  - selected-pool-set completeness
- In this exact-out seam, the first layer now looks solved on the tested domains; the honest remaining question is whether the prefilter/selection layer omits necessary pools.

## Updated lesson from v132 exact-out prefilter audit

- Once the inner allocation layer collapses cleanly, immediately audit support soundness of the upstream prefilter instead of continuing to polish the solved layer.
- A low support-soundness rate on random bounded corpora is stronger guidance than another exact-allocation win; it tells you where the real failures live.
- In this seam, the allocation DP survived exactly while the current prefilter failed frequently, so the next productive work is repaired cover-subset search or stronger selection contracts.

## Updated lesson from v132 exact-out support vs correctness

- After a prefilter support audit fails, do not immediately call it a winner-correctness failure. Measure three things separately:
  - support soundness
  - canonical winner preservation
  - contraction / dominance preservation
- In this seam, poor support soundness coexisted with exact winner preservation and exact contraction on the same bounded random corpus.
- A repair that searches for the smallest subset reproducing the winner is a winner-cover, not a support-cover. It can preserve correctness while worsening support completeness.

## Updated lesson from v132 exact-out structured support gaps

- After separating support soundness from winner correctness, search for the smallest structured witness. The first useful question is “what is the minimal family?”, not “how often does it happen under one random seed?”
- In this seam, the smallest support-only witness already appeared at `4` pools in a fully symmetric CPMM family. That means early stopping and duplicate symmetry can create certificate gaps even before candidate-cap overflow becomes relevant.
- Once that happens, split the frontier in two:
  - benign support gaps from symmetry
  - winner-threatening support gaps from heterogeneity

## Updated lesson from v132 exact-out gap split

- After finding the first benign and threatening witnesses, do not stop at the symmetry/heterogeneity dichotomy. Measure the whole split.
- In this seam, heterogeneous-but-benign gaps dominated threatening heterogeneous gaps, so heterogeneity by itself is not the right discriminator.
- The next honest object is a pattern classifier over heterogeneous families, not another generic “prefilter bad” summary.

## Updated lesson from v132 exact-out pattern classifier

- After the heterogeneity split, classify by multiplicity shape and perturbation kind. Threat often concentrates in a small number of pattern families.
- In this seam, the dominant threatening classes were outlier-quality patterns such as `3+1::reserve_fee` and `3+1::reserve_only`, not arbitrary mixed heterogeneity.
- Once a small elevated-risk pattern family appears, the next question is no longer “is the prefilter bad?” but “can a targeted selector patch that family without paying for full support completeness?”

## Updated lesson from v132 exact-out partial repair

- After identifying the elevated-risk pattern family, test the cheapest selector that specifically addresses the observed omission mode before reaching for a heavier redesign.
- In this seam, completing omitted tied cluster members repaired a meaningful fraction of threatening cases and preserved all benign cases, but it did not solve the mixed outlier families.
- That means the right progression is:
  - pattern classifier
  - cheapest pattern-specific repair
  - then identify the remaining omission mode and add only the next missing ingredient.

## Updated lesson from v132

- When a paper-derived object is audit-facing rather than execution-facing, measure it under a fixed review budget instead of forcing it into a utility-maximization frame.
- For reporting surfaces, top-k harmful-mass capture is often the right metric:
  - `better_report_surface -> more severe bad cases surfaced under the same review budget`
- A strong first anchor does not imply a final promoted surface is single-anchor:
  - attestation-first won the first simple comparison,
  - but the learned reporting surface mixed oracle and attestation pressure.

## Updated lesson from v132-routing

- When a literature paper matches the repo's exact canonical objective, prioritize it ahead of generic faster optimizers.
- A paper that gives the right objective and a wrong certificate boundary is still lower-value than a paper with weaker asymptotics but the right fail-closed semantics.
- The best ranking order for routing literature is:
  - exact objective match,
  - deterministic/certificate-compatible recovery,
  - then asymptotic speed.

## Updated lesson from v132-mconvex

- A structurally beautiful discrete-convex transfer can still fail immediately on the real routed domain if the neighborhood notion is wrong.
- Preserve the falsifier:
  - the naive one-unit transfer local-optimality law failed on the bounded exact-out CPMM corpus in most cases.
- After a routing-theory transfer fails, do not promote the solver; refine the neighborhood, domain, or reformulation first.


## Updated lesson from v132 paper widening

- Distributional-robustness papers belong first in shadow-side risk envelopes or treasury controllers, not in consensus execution, unless the ambiguity radius and worst-case certificate can be made replayable and explicit.
- Information-duality papers are useful only when the dual variable prices a real external assumption such as stale oracle data, delayed attestations, or partial Tau visibility.
- Illiquid-market duality belongs in accounting, treasury, insurance, or valuation layers; do not force it into exchange-time execution semantics.
- No-duality-gap results act as honesty gates: before trusting a stochastic dual or controller formulation, first check whether the formulation is even in a class where the dual meaningfully matches the primal.

## Updated lesson from v132 seam mapping

- A paper becomes materially more useful once it is pinned to a concrete repo boundary rather than just a plausible domain. For the new batch, the real seams are replayable risk-envelope packs and stale-information gates.
- If the repo already encodes a fail-closed boundary such as `max_oracle_staleness_epochs` or attestation age, the right imported object is often a pricing or explanation layer around that boundary, not a replacement decision rule.

## Updated lesson from v132 concrete problem passes

- After seam mapping, force a paper into one explicit repo-shaped optimization or valuation problem. If you cannot write the variables and loss/utility, the transfer is still too vague.
- For robustness papers, derive the uncertainty tuple from an existing replay pack before inventing a synthetic state space.
- For information-duality papers, start from already-enforced freshness or age constraints and treat the dual object as pricing those constraints, not as inventing a new execution optimizer.

## Updated lesson from v132 first experiments

- A concrete bounded experiment is a much stronger filter than a plausible formulation. The Wasserstein transfer looked reasonable on paper but did not beat the nominal baseline on the first replay-style seam.
- Information-value objects can clear the bar earlier because they attach naturally to already fail-closed freshness boundaries and can be tested as allocation/diagnostic layers without touching execution semantics.
- When a first bounded experiment shows zero separation from baseline even after a small sensitivity pass, downgrade the candidate quickly unless a clearly richer seam exists.

## Updated lesson from v132 anchor experiment

- After a paper clears the baseline-improvement bar, the next useful question is not "can it attach somewhere?" but "where should it attach first?"
- A three-anchor comparison can cheaply rule out a plausible but too-sparse boundary. Here, the external Tau assumption boundary remained too narrow to justify first attachment, while attestation age dominated.

## Updated lesson from v132

- For literature-transfer work, keep the paper loop separate from breakthrough claims: one paper, one `ideas/insights/plan` triplet, one current frontier.
- The first pass should extract the actual operator and its admissible domain before any ZenoDEX transfer story is allowed.
- A paper should be promoted only if it yields a reusable DEX object, solver lane, invariant family, or proof-relevant formulation; otherwise it stays a bridge reference.
- For optimization papers, the deepest practical question is usually the handoff boundary:
  - `continuous_or_stochastic_solver_output -> deterministic_certificate_or_replay_gate`.
- If that handoff cannot be stated clearly, the paper is not ready for transfer into a high-assurance DEX workflow.
- If the repo already has bounded candidate/certificate lanes for the same decision surface, a new optimizer must justify itself only as candidate-domain shaping or advisory compression, not as a replacement of canonical winner logic.
- For controller-search papers, land the first transfer in the shadow or replay perimeter before even thinking about live decision paths.
- If a candidate paper only reformulates a one-dimensional monotone decision that the repo already solves exactly with bounded search and explicit guards, do not upgrade the solver stack; record the formulation insight and move on.

## Updated lesson from v100

- Once a formal world model exists, the next high-leverage move is usually not more generic KRR prose but typed retrieval over contract, gap, and evidence surfaces.
- For software-shape work, the surviving object can be a queryable contract atlas rather than a new arithmetic law; record that object explicitly and keep its claim tier honest.
- The right next frontier after a contract atlas survives is to convert the most valuable slices into replayable certificate lanes, not to widen the atlas indefinitely.


## Updated lesson from v42

- After solving a sparse correction exactly in one family, widen the family before treating the mechanism as real mathematics.
- If the trailing exactness and prefix-supported defect survive widening, the next object should be an automaton or grammar for the family, not another single-family correction patch.
- A good abstraction step is: special case -> exact correction -> widened family -> family-level carrier object.

## Updated lesson from v68-v71

- Once the object stack begins to factor into `map -> compact -> tiny branch`, treat that factorization as a first-class result; it is the bridge from mathematical object to GPU-shaped implementation.
- Separate three claim tiers explicitly:
  - descriptive oracle-backed objects,
  - symbolic compilers over oracle-derived state,
  - direct arithmetic compilers from amounts alone.
- Do not overclaim the bridge objects. A nearly exact amount-only chart with a reserve-band tiebreak is useful evidence, but it is not yet a clean direct arithmetic law if its key count is nearly one-per-case.
- The next head-side arithmetic candidates should be judged by compression, not only exactness. A direct amount-only profile that becomes exact only after near one-key-per-case refinement is a bridge atlas, not a breakthrough.
- Subtracting the solved tail scalar from prefix floor-deficit profiles did not recover the head symbolic code; the head side still needs a better arithmetic carrier than naive head-pressure scans.

## Updated lesson from v72

- When a full direct arithmetic compiler is not yet clean, search for an exact dominant-mass fast path rather than forcing universality.
- A mathematically smaller but operationally better object is:
  - exact on accepted cells,
  - direct from amounts alone,
  - and paired with an explicit residual fallback boundary.
- For product use, an exact fast-path fan over ~90%+ of cases can be higher ROI than a weak universal chart with almost no compression.

## Updated lesson from v43-v44

- After widening a family, separate what stays universal from what actually breaks. Here the universal part was stronger than expected: exact trailing coordinate and unit-bounded defect survived through `n=8` even though interval support broke at `n=6`.
- Once support-shape simplicity breaks, do not jump straight to a higher-dimensional classifier. First test whether the defect still factors through a tiny event process. In this line it did: each coordinate defect became a single suffix carry event.
- After finding a single-event law, inspect the hidden state walk directly. A monotone unit-bounded reserve-gap walk is a much better object than a large support-pattern table because it explains why the event is unique.

## Updated lesson from v44-v46

- After isolating a family-level event process, try to collapse it again: monotone is weaker than signed-block, and single-crossing is weaker than last-nonzero-event.
- The right progression here was process compression: defect support -> single event -> event index -> compiled exact generator.
- A useful test for genuine ROI is whether the new object stack can be compiled back into an exact algorithm on the widened family. Here it can, which is why the equal-fiber line is now promotable as a real solver theorem candidate.

## Updated lesson from v47

- After obtaining an exact-by-family compiler, perturb the family minimally before trying to generalize it wholesale.
- The right first transfer test here was one perturbed peer, not an arbitrary heterogeneous family.
- A useful stability result is not only exact transfer rate; it is residual concentration. If most nonzero failures lie in a simple cone, the exact family law is still a strong advisory engine and a good base for the next correction object.

## Updated lesson from v48

- After finding a concentrated transfer residual, test whether it lives in a tiny generator cone before inventing a richer classifier.
- Cone compression is a stronger object than a histogram because it gives a reusable residual basis.
- If a 3-generator span already covers nearly all transfer cases, the next correction search should focus only on the exceptional atlas, not the bulk family.

## Updated lesson from v49

- After finding a near-exact transfer cone, search first for an exact low-perturbation region before attacking the full residual pocket.
- A useful transfer theorem often has the form: exact up to a perturbation threshold, concentrated exceptions beyond it.
- Once the exception pocket is single-digit, the next search should target that pocket directly rather than re-optimizing the bulk region.

## Updated lesson from v50

- After finding a near-exact transfer cone and a tiny exception pocket, test whether the full residual closes under a small generator basis before inventing a more complicated classifier.
- A generator tower is a stronger object than a flat exception atlas because it tells you how transfer complexity grows with perturbation.
- Exact-by-family, exact-by-threshold, near-exact cone, and exact residual basis is now the right hierarchy for evaluating DEX-side ROI.

## Updated lesson from v51

- After finding an exact residual basis, always test whether a change of coordinates shrinks the basis itself.
- Representation change is a real breakthrough when it reduces the exact residual basis, not just the observed histogram.
- In this line, gradient space is now the preferred search space for transfer-law refinement beyond equal-fiber symmetry.

## Updated lesson from v52-v53

- After finding an exact residual basis in the right coordinates, search for a semantic generator family before looking for a larger theorem.
- A better basis is not only smaller; it should have an interpretable grammar. Here, interval-boundary generators were stronger than arbitrary gradient vectors.
- Once an exact semantic basis exists, compute the minimal normal form distribution. If the mass collapses into zero/one/two-object cases with a singleton exception, that is a stronger breakthrough than a flat exact-basis claim.
- The current best transfer workflow is: exact family compiler -> coordinate compression -> semantic basis -> minimal normal form -> isolate the singleton exception.

## Updated lesson from v54

- After finding an exact normal form, widen the family and test whether the normal form is merely corpus-specific or nearly universal.
- Separate the strongest symbolic exception from the broader near-universality statement; they answer different questions and should not be conflated.
- When a widened family leaves only one or two exceptions, the next search should explain those exceptions as siblings of the same mechanism before inventing a larger new regime.

## Updated lesson from v55-v56

- After finding a sharp boundary law on a narrow window, widen the lattice and expect the strongest version to fail.
- Do not discard the law immediately; replace it with an atlas if the widened failure set is still tiny and structured.
- The right sequence here was: near-window boundary line -> spike law -> widened atlas -> reserve-scale concentration.
- A useful breakthrough is often a compressed failure atlas, not a universal theorem.

## Updated lesson from v57-v58

- After getting an exact motif atlas, try collapsing motifs into semantic families before searching for new numeric features.
- If the family grammar still feels ad hoc, test whether a single scalar coordinate classifies the families exactly.
- The right compression ladder here was: raw gradient symbols -> semantic motifs -> motif families -> tail-charge classifier.
- When a one-scalar classifier appears after several abstraction layers, it is usually the right coordinate for the next arithmetic explanation.

## Updated lesson from v59

- After compressing an exception atlas to a one-scalar family classifier, test the next larger lattice to see whether the grammar truly breaks or just acquires a higher-order rung.
- If only one new higher-order symbol appears, treat it as a ladder extension of the existing family before inventing a broader new grammar.
- The current ladder is: near-universal zero/one/two-interval regime -> tiny three-interval atlas -> unique four-interval super-tail lift.

## Updated lesson from v60

- After compressing an exception atlas to a one-scalar classifier, look for an exact arithmetic law for that scalar rather than more symbolic taxonomy.
- The right move here was to separate the local terminal swap into continuous and floor-deficit parts.
- If the continuous residual is uniformly subcritical, the rounded floor-deficit term becomes an exact global law.
- This is a stronger endpoint than a motif atlas because it upgrades symbolic structure into arithmetic structure.

## Updated lesson from v61

- After finding a higher-order ladder extension, test whether the new rung lives in a disjoint numeric band of the arithmetic coordinate that already explains the lower rung.
- If the bands separate with a clean gap, search for the simplest exact threshold before inventing a richer state machine.
- Here the right sequence was: symbolic tail classifier -> arithmetic floor-deficit law -> super-tail ladder -> one-dimensional threshold bifurcation.

## v62
- `tail_flux_floor_duality_v1`: on the widened one-perturbed-peer lattice, the tail exception coordinate is exactly the same scalar whether computed as interval-boundary tail flux or as the arithmetic terminal floor-deficit law.
- `head_tail_interval_factorization_v1`: every widened first-perturbed-family gradient residual factors exactly into a scalar tail charge plus a zero-tail head residue; on the 24k-case lattice the head atlas has finite size and the tail charge remains bounded by 2.

## v63
- `head_residue_interval_normal_form_v1`: after removing the exact scalar tail coordinate, the widened first-perturbed-family head residue still admits an exact bounded interval grammar.
- `unit_head_atlas_v1`: the widened head residue atlas is finite and unit-valued; every head coordinate lies in {-1,0,1}.

## v64
- `head_disjoint_interval_law_v1`: after removing the exact scalar tail coordinate, the minimal head interval decomposition is always pairwise disjoint on the widened first-perturbed family.
- `head_block_forest_v1`: the widened head residue is therefore a tiny disjoint block forest with at most three blocks.

## v65
- `head_semantic_forest_atlas_v1`: the exact 31-pattern widened head forest atlas collapses to 12 semantic families once only block types are retained.
- `head_forest_type_dominance_v1`: almost the entire widened head side lies in the zero / one-block / prefix-suffix semantic families.

## v66
- `head_boundary_word_atlas_v1`: the widened head semantic forest grammar collapses to a 9-word signed boundary language.
- `span_resolved_family_code_v1`: the only 3 ambiguous boundary words are resolved exactly by a simple span/gap code.

## v67
- `ambiguous_word_gap_law_v1`: the only three ambiguous widened head boundary words are resolved exactly by their internal gap pattern.
- `oriented_gap_comparison_v1`: for the nontrivial 3-boundary words, family type is decided by a simple oriented comparison of the two interior gaps.



## Updated lesson from v68-v69

- After an exact family compiler exists, ask whether its dominant stages factor into GPU-shaped kernels before trying to build a full production accelerator.
- The right evidence is not vague parallelizability; it is exact batched kernels with measured speedups and explicit factorization (map / compact / tiny-branch).
- For this line, the tail scalar law is the strongest accelerator target, then the head boundary-word compiler, then only a tiny residual branch layer.


## Updated lesson from v70

- After a symbolic classifier stabilizes, test whether it is missing only a translation/anchor coordinate; that can upgrade a family classifier into an exact residual compiler.
- The strongest transfer breakthrough so far came from turning: boundary word + gaps + anchor -> exact head, then combining that with the exact tail scalar law.
- This is the first point where the widened first-perturbed family is solved end-to-end without brute-force order search.


## Updated lesson after the v71 false start

- A symbolic or anchored classifier over oracle-derived head state is not yet a direct amount-to-head compiler. Do not treat it as a runtime advisory engine.
- The current GPU-scaled kernels are exact subkernels of the compiler stack, not yet a full direct amount-to-order compiler.
- The open frontier remains a direct arithmetic law for the head side; rounded prefix floor-deficit vectors and their continuous order type are not sufficient.

## Updated lesson from v71-v74

- After an exact symbolic/oracle-backed compiler exists, search first for a dominant exact direct-amount fast path instead of forcing a universal compact arithmetic law immediately.
- If the fast path covers most of the lattice, build a staged exactifier on the residual rather than broadening the search too early.
- Distinguish clearly between:
  - a bridge exactifier: exact but weakly compressed, often near one-key-per-case
  - a compressed law: exact with genuine structural compression
- A useful hybrid architecture can still be a real breakthrough if it is:
  - direct from amounts
  - exact end-to-end on the target family
  - layered as cheap fast path plus small residual exactifier
- Current hierarchy for the widened first-perturbed family:
  1. `dominant_easy_fan_v1` exact fast path
  2. `fallback_zero_gate_v1` exact zero/nonzero split on most residual mass
  3. `sheet_residue_exactifier_v1` exact amount-only residual exactifier
  4. `three_stage_amount_compiler_v1` exact direct-amount compiler

## Updated lesson from v75

- After obtaining an exact staged compiler, factor it into kernels explicitly before attempting acceleration.
- Exact batched execution is not enough for a GPU/scaling claim; if the batch path still runs Python loops around symbolic/oracle subroutines, treat it as execution-shape evidence only.
- Promotion rule for accelerator claims:
  - exactness under batching is necessary
  - measured speedup must be materially > 1 before calling it a scaling breakthrough
- Current v75 outcome:
  - kernel algebra is real and useful
  - batched implementation is exact
  - but the implementation is not yet low-level/vector-native enough to claim a speed breakthrough

## Updated lesson from v76-v77

- Once a residual exactifier exists, split the residual into semantic sides before searching for more arithmetic compression.
- Here the useful split was:
  - zero residual head word
  - nonzero residual head word
- On the nonzero side, search first for the simplest amount-space carrier before trying larger symbolic atlases.
- `gap_pair = (a-c, b-a)` turned out to be the right first carrier: it solved most of the nonzero residual immediately.
- When a generic tiebreak works, look for a cleaner semantic refinement of it. Here reserve decade replaced a looser digit rule.


## v78
- `gap_tail_resonance_pocket_v1`: on the stage-3 nonzero residual, `(gap_pair, tail_charge)` is exact on `76 / 78` cases and leaves only one ambiguous resonance pocket of mass `2`.
- `single_pocket_scale_threshold_v1`: that sole resonance pocket is resolved exactly by a coarse reserve-scale threshold on `c // 10_000`.

## v79
- `reserve_ratio_quantization_band_v1`: on the stage-3 nonzero residual, `gap_pair + round(S*c/a)` is exact across a wide quantization band (`203` exact scales in `1..300`).
- `minimal_exact_ratio_quantizer_v1`: the smallest exact scale is `S = 35`, and it improves the exact symbolic nonzero residual law from `78` keys down to `77` keys.

Interpretation:
- This is a cleaner exactifier than reserve decade because it is a reserve-normalized arithmetic coordinate rather than a coarse bucket.
- It is still a symbolic-state compiler, not yet the final compressed arithmetic head law.


## v80
- `stage3_ratio_digit_exactifier_v1`: the full `234`-case stage-3 residual is classified exactly by `fallback_key + round(53*c/a) + a_mod10`, reducing the exactifier key count from `234` to `226`.
- `stage3_exactifier_plateau_v1`: the same arithmetic exactifier shape is exact across a broad scale plateau (`234` exact scales in `1..300`), with best scale `S = 53`.

Interpretation:
- This is the first exact compression improvement on the full stage-3 residual, not just the nonzero slice.
- It is a better direct-amount exactifier than the old reserve-sheet bridge key, but it is still not yet the final compressed deep law for the head side.


## v81
- `tail_pressure_bit_carrier_v1`: the nonzero stage-3 residual is classified exactly by `(gap_pair, tail_charge, boundary_sign@0)` with `77` keys.
- `dual_boundary_sign_carrier_v1`: the same nonzero residual is classified exactly by `(gap_pair, boundary_sign@0, boundary_sign@3)` with `77` keys.

Interpretation:
- These are semantically cleaner than the old reserve-decade tiebreak for the nonzero stage-3 slice.
- They do not improve the best full stage-3 exactifier from `v80`; their value is explanatory and structural rather than a full-residual compression win.

## Updated lesson from v82-v84

- After finding an exact mixed discrete/coarse exactifier, immediately test whether the pair is genuinely irreducible or is only a disguised single scalar band.
- Here the right progression was:
  1. replace the old `a_mod10` digit rule with a cleaner reserve-side pair,
  2. verify that the pair preserves the broad exact scale plateau,
  3. test whether the pair itself collapses to a single scalar band index.
- Promotion rule:
  - a pair carrier is useful,
  - but a single exact scalar carrier is a stronger mathematical object and a better kernel target.
- Current exact stage-3 frontier:
  - `fallback_key + round(53*c/a) + triadic_band_scalar(b)`
  - where `triadic_band_scalar(b) = 3 * floor(b / 20000) + ((b // 1000) % 3)`.

## Updated lesson from v85

- After finding an improved exactifier, test whether some upstream symbolic coordinates are actually redundant once the new arithmetic carrier is present.
- Here the right move was to challenge the whole fallback key, not just the tail-side residue.
- Reduction rule:
  - if the same exact key count survives after dropping symbolic fields, promote the reduced symbolic/arithmetic law as the stronger object.
- Current stronger stage-3 law:
  - `(fallback_ratio_bucket, fallback_boundary_word, round(52*c/a), triadic_band_scalar(b))`
  - with `triadic_band_scalar(b) = 3 * floor(b / 20000) + ((b // 1000) % 3)`.

## Updated lesson from v86

- After reducing symbolic structure, test whether the remaining symbolic carrier itself is replaceable by a single scalar anchor.
- Here the fallback boundary word was not fundamental: once the reserve-side scalar band and ratio bucket were present, the amount-profile first-support index was enough to replace it exactly.
- Stronger object rule:
  - prefer exactifiers built from scalar amount-derived coordinates over symbolic words when the key count does not worsen.
- Current strongest direct amount-only stage-3 law:
  - `(fallback_ratio_bucket, round(52*c/a), triadic_band_scalar(b), first_support(amount_profile(a,c,b)))`.

## Updated lesson from v87

- After a fully scalar exactifier exists, test whether two scalar coordinates can be fused linearly without losing the exact plateau.
- A real breakthrough is not just removing symbols; it is reducing the number of scalar coordinates while preserving exactness and plateau width.
- Current strongest stage-3 law:
  - `(r100 + 16 * triadic_band_scalar(b), round(52*c/a), first_support(amount_profile(a,c,b)))`
  - exact on all 234 stage-3 cases
  - broad exact plateau (`224` exact scales in `1..300`)
  - `220` exact keys.

- After finding a compact exactifier, search for lower-dimensional embeddings before inventing new features.
- When a one-scalar embedding exists, derive the forbidden-weight spectrum from cross-label collisions; this is stronger than reporting a best-fit weight.
- Promote theorem-shaped complements/thresholds over isolated exactifier fits whenever possible.

## process lesson from v97
- After a scalar exactifier becomes theorem-shaped, move from spectrum to chamber geometry.
- Look for quotient reduction (`affine forms -> merged components`) and prove optimality as `max safe merges before first cross-label collision`, rather than as a raw best parameter search.

## process lesson from v98-v99
- After proving a scalar optimum by collision geometry, refine from counts to local support-class atlases.
- A good next theorem is often not another weight law, but a description of which local merge classes realize the optimum and which longer-span classes appear immediately off the optimum.

## process lesson from v100
- After a local support atlas is found, quantify its prevalence over the whole exact-weight set.
- Distinguish generic exact behavior from structurally optimal exact behavior; here, span-1 exactness is common, but maximal span-1 merging is unique.

## process lesson from v101
- When a routing approximation object resists direct scalar collapse, test for low-height interval grammars first.
- Exact low-height grammar plus small family count is enough to justify advisory/refinement experiments even without a direct scalar law.

## Updated lesson from v102-v104

- Once a raw interval grammar appears, immediately try two compressions: semantic words and adjacency geometry. A small semantic atlas plus a star-fan/rigidity object is a better reusable frontier than a flat family histogram.
- When a local optimal pattern exists (like the 728 chamber), test whether its support classes transfer to a larger but still exact set before treating it as purely local.
- A good transfer object is small, support-class based, and exact on a widened set even if it is not yet universal.

## Updated lesson from v105-v108
- After a local transfer code widens once, immediately test whether the widening is governed by a low-modulus phase coordinate before inventing new symbolic carriers.
- If a modulus appears, split it into arithmetic factors when possible. Here `mod 18` became a cleaner phase-lattice object `(mod 9, parity)`.
- Equally important: package the first sharp negative threshold. Here the same support-class code stops admitting simple low-modulus lifts at `merge>=2`, even after adjoining `merge_count` and `max_span`.
- Promotion rule: a widened transfer object is stronger when it comes with both a positive ladder (`merge>=5,4,3`) and a clean break law (`merge>=2`).

## Updated lesson from v109
- A negative threshold result should be challenged once with a richer but still low-complexity support signature before being treated as a hard barrier.
- Here `merge>=2` broke the simple `Omega + mod + merge/span` ladder, but recovered exactly after enriching the support signature to five small support statistics and adjoining a composite CRT phase.
- Promotion rule: distinguish 'no simple lift' from 'no exact low-complexity lift'. The first can still hide a structured composite-phase object.

## Updated lesson from v110
- After recovering a broken threshold with a richer signature, immediately test the next threshold with the smallest plausible enrichment before escalating complexity.
- Here `merge>=1` still resisted the `merge>=2` pattern even after adding one extra simple support statistic, which makes the break law sharper and more trustworthy.
- Promotion rule: when a transfer ladder extends through several thresholds and then sharply fails at the next simple enrichment, record that failure as a first-class object rather than silently broadening the feature search.
## v113
- Stronger negative theorem pattern: after a successful CRT recovery at one threshold (`merge>=2`), the next threshold (`merge>=1`) may still resist both one-extra-stat and one-interaction-CRT enrichments.
- Promotion rule: package these failures as threshold frontiers rather than leaving them as unrecorded probes.
## v114
- Route transfer lesson: neutral-incidence alone is too coarse, but neutral-incidence plus a tiny symbolic prefix of the support words closes the bounded family exactly.
- General pattern: when a star-fan center code collapses too much, enrich it with minimal prefix data before trying heavier arithmetic carriers.
## v115
- Threshold-ladder lesson refined: a sharp negative theorem for simple enrichments does not imply the threshold is unrecoverable. At `merge>=1`, the right recovery object is the full same-label support histogram plus a minimal exact modulus.
- Discovery rule: after a failed sparse-support lift, test the full histogram carrier before declaring a hard boundary.
## v116
- Route transfer lesson refined: neutral-incidence alone is too coarse, but the bounded route family becomes exact with exactly three extra symbolic features.
- Minimality rule: when an enriched code closes the family, check 1-feature and 2-feature impossibility before claiming the triad is meaningful.
## process lesson from v117-v118
- After finding an exact same-partition quotient, immediately test asymmetric quotients across natural label splits; here the `merge>=1` carrier compressed further from `57` to `55` only after allowing different zero/nonzero partitions.
- Minimality claims are worth packaging even when the search is slightly expensive, because they distinguish a structural quotient from another lucky grouping.
## process lesson from v119
- Once a carrier compresses but the minimal exact modulus does not, stop looking for more support aggregation as the primary lever. The next object should attack phase geometry directly.
## process lesson from v120-v121
- After proving exactness is the complement of a forbidden spectrum, do not stop at the spectrum. Package the subspan exact set as a chamber atlas and track the density ramp toward the automatic exact regime.
- A useful four-step phase workflow is now:
  - forbidden spectrum,
  - first exact modulus,
  - chamber atlas,
  - asymptotic density ramp.
## process lesson from v123
- After building a divisor-spectrum chamber atlas, check the upper-half regime separately. Above `span/2`, divisor closure often collapses to self-difference avoidance, which is a much cleaner object than the full forbidden spectrum.
## process lesson from v124
- After self-difference avoidance appears in the upper half, replace the divisor-spectrum view with a gap-run view on the ordered difference set. Chamber geometry then becomes ordinary missing-run geometry.
## process lesson from v125
- After the gap-run law is established, switch from chamber identity to spacing geometry: exact chambers are the positive spacings between consecutive ordered self-differences with augmented boundaries.
- Once chamber geometry is spacing geometry, the next object is usually a gap-length or scarcity law, not another chamber atlas.

## process lesson from exact-out residual cap-lift work
- After a fallback is justified only by one corrected random witness, do not jump straight to a full widened truthful sweep if that sweep is too expensive.
- First build a witness-centered local perturbation harness around the residual case.
- If the same repair survives across that local slice with benign preservation intact, treat it as a real structural class rather than sample noise.
- Current exact-out instance of that rule:
  - omitted-pair slot-ceiling cases survived the witness-centered slice under `probe_ladder + cap5`, so the fallback is now a real class candidate, not just one random hit.

## Updated lesson from v126-v127

- Once a threshold ladder is explicit, package the arithmetic regime sequence itself as an object; this prevents re-running the whole search just to recover the same frontier.
- If support compression stops but phase rigidity remains, the next search should target phase geometry, not more support aggregation.
- On the routing side, once a star fan and a minimal transfer code both exist, combine them into a single factorization object before searching for finer chambers.
## process lesson from v128
- Once a threshold family is widened with a richer carrier, re-run the full divisor-spectrum and upper-half gap-law program on that exact carrier instead of assuming the earlier phase geometry persists unchanged.
- If the same forbidden-spectrum and gap-run laws survive on the richer carrier, treat that as a genuine phase-law transfer, not just a repeated computation.
## v130
- Validated `record_gap_spine_v1`: long upper-half exact chambers form a monotone record spine with records `(1512,1520,9)`, `(1597,1608,12)`, `(1644,1667,24)`, `(1669,1695,27)`, `(1737,1769,33)`.
- Validated `threshold_tail_bands_v1`: long-gap thresholds activate in nested tail bands: `>12` starts at `1644`, `>24` starts at `1669`, `>28` and `>32` start at `1737`.
## v131
- When a control-plane gate and an execution path share the same threshold surface, measure the guard gap directly. A zero gap means the control gate does not protect the action path.
- Separate invariant preservation from extractable-value safety. The zUSD core preserved its stated invariants here, but still exposed a profitable liquidation band.
- When a chaos campaign finds a sharp threshold, package the threshold band itself as the object instead of storing only witness traces.

## process lesson from v132 wider paper scan
- When a new paper family maps onto an already-supported seam, reuse the existing bounded experiment harness before inventing a new synthetic domain.
- Here the information-shadow seam was already honest enough to test both zero-adjustability-like gates and `K`-policy bundles, which produced measurable results quickly.
- Small discrete policy bundles can saturate a bounded oracle upper bound; if that happens, defer continuous policy families until a seam appears where interpolation still adds value.

## process lesson from v132 Maher residual check
- Once a guarded repair lane is already materially better than the current fallback, isolate the last miss class before widening the trigger family again.
- If the only exact-recall residual fix is a blunt singleton-style fallback that fires on large benign mass, stop and keep the cheaper guarded lane.

## process lesson from v132 Tellache bridge
- When a paper needs a linear lex master but the live core is nonlinear, do not force a fake linearization of the whole mechanism.
- First reuse any exact collapse already discovered in the repo and ask whether the residual quotient admits an honest master-column interpretation.

## process lesson from v132 decision-diagram global exact-out
- Once a fixed-set inner DP survives, do not assume selector repair is the only remaining route.
- First test whether selection and allocation collapse together into a single bounded layered carrier such as a decision diagram.
- If that carrier stays exact with materially fewer states than full-domain enumeration, treat it as a stronger reference oracle before deepening more local heuristic repairs.

## process lesson from v132 decision-diagram matched comparison
- After a global bounded carrier survives, compare it directly against the best current local lane before calling it a runtime candidate.
- If the global carrier wins exactness at roughly equal quote budget but uses more internal states, classify it as an exactness-first reference oracle rather than a blanket replacement.

## process lesson from v132 DD vs guarded Maher
- After a local repair lane is already the best runtime-side heuristic, compare the global carrier against that lane too, not just against the older selector baseline.
- If the global carrier still wins exactness after the best guarded local repair, stop deepening local selector patches and move the global branch toward bounded gap/certificate work.

## process lesson from v132 restricted vs relaxed DD
- Once a relaxed DD lower bound becomes exact on the tested slice, stop treating the frontier as a primary-objective problem.
- The remaining search target is then tie memory: the smallest extra state needed to recover canonical choice after the objective has already collapsed.
- Width sweeps are useful here because they reveal whether the missing information is large or genuinely tiny.

## process lesson from v132 objective-frontier projection
- After a low-width restricted lane misses canonical recovery, do not assume the missing state is the obvious tie variable.
- First isolate the exact-objective frontier explicitly and test projection there.
- If projection on the objective frontier already recovers the canonical winner, then the real problem is frontier recovery, not canonical tie memory.

## process lesson from v132 DD frontier recovery
- Once a relaxed DD objective table is already exact on the claimed slice, measure whether frontier projection adds any new quote work before designing a more elaborate certificate lane.
- If frontier projection stays exact and consumes zero extra quotes, the next promotion target is the composed lane itself, not a separate tie-memory gadget.
- State compression can still matter even when quote work is flat; in that case classify the gain honestly as carrier compression, not oracle-efficiency.

## process lesson from v132 DD residual stress
- After a composed bounded lane survives broad widened corpora, stress it on the hardest known residual family from the competing heuristic branch before promoting it.
- If it survives there with the same cost pattern, treat that as a stronger promotion receipt than another random-corpus replication.

## process lesson from v132 DD supported boundary
- After a bounded composed lane survives random corpora and one hard residual family, do not generalize it across adjacent curve-family slices without a structured pattern sweep.
- Random wide corpora can miss thin but real structured boundaries; targeted pattern scans are the right next move once a composed lane looks promotion-worthy.

- DD promotion posture from v132:
  - Promote the composed DD lane only on the narrower declared domain that excludes the supported reserve_only boundary.
  - Use exact DD as the fallback on that boundary; do not promote the leg-aware carrier in its current form.

## process lesson from v132 DD declared-domain comparison
- Once a composed bounded lane has both a surviving domain and an excluded boundary, stop talking about “general performance” and write the declared contract explicitly.
- Compare the lane only against the strongest competing runtime lane on the included slices.
- If unique exactness lift is concentrated in one slice while parity holds elsewhere, promote the lane as a bounded exactness oracle rather than as a blanket runtime default.

## process lesson from v132 DD guarded shadow lane
- After the declared domain is explicit, encode the route policy mechanically before discussing promotion.
- Use three routes, not one:
  - composed lane on supported slices,
  - exact fallback on known excluded boundaries,
  - selector default elsewhere.
- If the guarded lane stays exact and the selector gap is small, keep it as a shadow/oracle object until a runtime-cost story exists.

## process lesson from v132 mixed DD shadow harness
- After a guarded shadow lane looks clean in aggregate, force it through a per-case replay-style harness before trusting the route policy.
- Log route choice, guarded answer, selector answer, and disagreement flags on every case.
- If all observed lift concentrates in one route, stop talking about the lane as a monolith and promote only that route's exactness claim.

## process lesson from v132 larger CPMM DD shadow pass
- After the per-case shadow harness identifies the lifting route, rerun that route on a larger focused replay corpus before discussing runtime candidacy.
- Measure cost explicitly:
  - mean quote calls
  - quote-call ratio
  - mean state mass
- If the focused route is both more exact and cheaper, its posture changes materially; record that explicitly instead of leaving it under the broader shadow-lane label.

## process lesson from v132 CPMM DD runtime bar
- Once a route becomes a real bounded runtime candidate, stop relying on narrative memory alone and write an explicit acceptance bar.
- The bar should name:
  - route fence
  - exactness target
  - cost target
  - replay-log requirement
- Also make the replay runner configurable enough that regenerating receipts is cheap and routine.

## process lesson from v132 executable runtime bar
- After writing a promotion bar, encode it as an executable report immediately.
- A runtime-candidate claim should have:
  - a reusable replay runner,
  - a JSONL log,
  - and a bar-check report with criterion-level booleans.
- This avoids “green by narration” and makes regressions obvious on the next replay.

## process lesson from v132 DD shadow adapter
- Once a research lane has:
  - a declared route guard,
  - a replay runner,
  - and an executable promotion bar,
  package the comparison logic into a non-core adapter before discussing runtime integration.
- The adapter should expose:
  - route decision,
  - guarded quote,
  - selector quote,
  - disagreement metadata,
  without leaking the lane into `src/core/`.
- Then repoint replay harnesses at the adapter so the integration surface, not private experiment helpers, is what stays exercised.

## process lesson from v132 DD shadow CLI
- After the adapter exists, add a file-driven shadow entrypoint before discussing any runtime-facing integration.
- The right CLI object is:
  - JSON in
  - adapter evaluation
  - summary JSON out
  - optional JSONL per-case log
- That keeps replay/shadow usage operational without importing research harnesses or touching the functional core.

## process lesson from v133 lookup BAO compiler
- If a symbolic lookup table or Q-table is meant to carry semantics rather than just a heuristic score, first ask whether it is determined by atom images and extends by union.
- On finite powerset carriers, the safe executable unary class is: zero-preserving additive operators, equivalently relation-image maps built from per-atom images.
- Thresholded or masked Q operators are promotable only after compiling into that class; otherwise they stay advisory and should not be treated as runtime semantics.

## process lesson from v134 binary lookup BAO compiler
- After a unary symbolic operator survives, the next safe extension is not arbitrary pair lookup tables but separately additive binary operators.
- On finite powerset carriers, the executable binary class is: zero-preserving in each argument and union-preserving separately in each argument, equivalently determined by pair-atom images.
- A two-input symbolic operator should be treated as semantic only after it compiles to a pair-atom / ternary-relation form; otherwise it remains heuristic metadata.

## process lesson from v135 typed lookup BAO compiler
- After the untyped binary compiler survives, the next serious object is a typed mixed-carrier operator `P(S) x P(C) -> P(T)` rather than more experiments on a single undifferentiated carrier.
- On finite typed powerset carriers, the executable mixed class is still the separately additive one, now read as source/capability pair-atom images into targets.
- This is the first semantic shape that honestly matches state x capability -> target, so future Tau operator work should build here instead of returning to untyped lookup tables.

## process lesson from v136 typed operator acceptance gate
- After a semantic operator class stabilizes, package the admission rule as an executable gate immediately.
- The right gate shape is: well-formed domain check, target-range check, zero-preservation check, separate-additivity check, then canonical pair-atom receipt on success.
- This avoids semantic drift by forcing every new operator proposal through the same deterministic acceptance path.

## process lesson from v137 typed operator registry gate
- After an operator acceptance gate exists, add registry discipline immediately instead of trusting repeated manual admission.
- The right registry rule is: legal under the semantic gate, then unique under a canonical semantic receipt hash, with same-id same-receipt proposals treated as idempotent.
- This separates three different failure modes cleanly:
  - semantic illegality,
  - duplicate semantics under a new id,
  - duplicate id with changed semantics.

## process lesson from v138 receipt-backed Tau operator manifest
- After registry discipline exists, package admitted operators into a canonical manifest immediately instead of treating the registry state as the final artifact.
- The right manifest rule is: one legal owner per semantic receipt hash, chosen canonically, plus a replayable receipt and a manifest hash over the sorted entries.
- This turns operator extensibility into a file-shaped object that can be verified fail closed and made order-invariant across proposal order.

## process lesson from v139 Tau operator manifest checker
- After a manifest object exists, the next value is a file-oriented checker immediately, not a deeper registry abstraction.
- The checker should separate parse failures, schema failures, and semantic verification failures, and return explicit receipts instead of only booleans.
- This is the right extraction point before moving the object into repo-level tools, because it proves the file shape is stable enough to validate directly from disk.

## process lesson from v140 Tau operator library bootstrap
- After a manifest checker exists, the next honest step is a tiny named library bootstrap rather than a broad operator ecosystem.
- The bootstrap rule should be: checked manifest plus required role bindings, then reconstruct executable operators directly from manifest receipts.
- This proves that the manifest artifact is not just archival; it can carry a disciplined operator surface without touching the functional core.


## process lesson from v141 score-table typed operator compiler
- After the typed operator library surface exists, the next honest bridge from lookup/Q ideas is not raw learned control but a compiler from bounded score tables into accepted typed operators.
- The safe rule is: threshold or mask only at typed pair-atom scope, then extend by union and pass the typed acceptance gate.
- Direct thresholding on full subset tables can remain complete and in-range while still failing separate additivity, so it should be treated as heuristic metadata unless the gate accepts it.
- This gives the right controller architecture shape: score tables -> accepted typed operators -> named roles -> deterministic source policy.


## process lesson from v142 score-table symbolic policy synthesizer
- After score tables compile into accepted named roles, the next honest bridge is bounded source-policy synthesis over the current grammar, not direct promotion into runtime policy.
- Representability and uniqueness are different questions: a bounded label family can be exactly representable while still leaving multiple matching policies.
- The right deterministic response is a total-key canonical representative plus an explicit ambiguity count, while the right semantic response is to add more corpus constraints if uniqueness matters.


## process lesson from v143 policy identifiability corpus search
- After bounded source-policy synthesis exposes ambiguity, the next honest step is an identifiability search over the full bounded domain, not immediate grammar expansion.
- Removable ambiguity and structural aliasing must be separated explicitly: extra cases can collapse the former but not the latter.
- When a residual alias survives on the full bounded domain, record the exact alias law and treat uniqueness as a grammar/operator-family issue rather than a corpus-size issue.

## process lesson from v144 policy equivalence quotient
- After structural full-domain aliasing is exposed, the next honest synthesis target is the quotient by bounded behavioral equivalence, not the raw syntactic policy set.
- Canonical representatives should be treated as administrative names for semantic classes, with alias members recorded explicitly as metadata rather than silently discarded.
- Once quotienting restores uniqueness on the bounded corpora that matter, keep the grammar fixed; only widen the grammar if the quotient class itself remains ambiguous.

## process lesson from v145 quotient policy PCC bridge
- After quotient-level uniqueness is established, the next honest step is to push the canonical quotient winner through the existing non-core artifact chain before widening the grammar.
- Residual full-domain aliases should be preserved as explicit metadata alongside the canonical representative instead of being silently erased during artifact generation.
- A quotient-synthesized policy that reaches a current PCC obligation is strong evidence that the semantic/controller lane and the artifact-trust lane are now connected on the bounded domain.

## process lesson from v146 alias-aware symbolic policy lane
- After quotient synthesis reaches the artifact-trust lane, the next honest improvement is to make residual alias provenance first-class on the symbolic policy itself instead of keeping it in experiment-side sidecars.
- Provenance metadata should be treated as part of symbolic policy identity if later receipts and obligations are expected to account for it explicitly.
- When alias metadata is first-class, demand two separate checks: identity should change at the symbolic-policy layer, while lowered bounded semantics should remain unchanged unless the actual selector changes.

## process lesson from v147 direct alias policy synthesizer
- After alias-aware provenance becomes first-class in the symbolic policy lane, the next honest step is to move synthesis onto the repo-level builder rather than keep assembling policy JSON ad hoc inside experiments.
- Direct builders should be judged against exact artifact reproduction, not only semantic equivalence, when the downstream receipts and hashes already treat the artifact shape as part of the contract.
- Once the direct builder reproduces the canonical alias-aware source artifact exactly and still reaches the current PCC lane, the remaining work shifts from construction mechanics to richer corpora and grammar pressure.

## process lesson from v148 alias-aware replay corpus classifier
- After direct alias-aware policy synthesis works, the next honest question is not grammar growth but replay-corpus quality: does the corpus isolate one quotient class or still leave multiple classes alive?
- Distinguish two kinds of non-uniqueness explicitly: multi-class ambiguity is a corpus problem, while alias-bearing uniqueness is a metadata problem already handled by the alias-aware schema.
- When two different corpora isolate the same unique quotient class and emit the same alias-aware policy hash, treat that as replay-level synthesis stability and spend the next effort on richer controller families instead of reworking the current builder path.

## process lesson from v149 two-literal controller family pressure
- After replay stability is established for the current simple grammar, the next honest widening step is to measure replay pressure under a slightly richer family before changing any schema or runtime surface.
- Grammar widening should be blocked by corpus pressure, not by taste: if the richer family keeps multiple quotient classes alive on the current replay corpus, then the corpus must improve before the schema does.
- If the richer family still normalizes to the old simple canonical representative on the full bounded domain, preserve the simpler schema and treat the richer family as analysis-time pressure rather than immediate artifact-surface growth.

## process lesson from v150 minimal replay extension for richer family
- After a richer grammar shows replay pressure, the next honest move is a minimal witness search over missing replay cases rather than an open-ended request for more data.
- Corpus upgrades should be recorded as exact witnesses when possible: “no 1-case extension works, this 2-case extension does” is a stronger steering object than a generic ambiguity complaint.
- If the minimal replay extension restores uniqueness while preserving the same simple canonical winner, prefer enriching the corpus first and defer any schema widening until a future family actually changes that winner.

## process lesson from v151 richer family replay upgrade bridge
- After a richer family gets a minimal replay extension, the next honest check is whether the upgraded family really forces a new artifact surface or simply normalizes back into the current one.
- Keep provenance and semantics separate: a richer family can legitimately change source-policy hash through a different quotient witness while leaving the lowered artifact and PCC-facing behavior unchanged.
- When the upgraded richer family restores the same selector, alias members, and lowered artifact as the current canonical policy, treat the prior pressure as a corpus gap rather than immediate evidence for schema widening.

## process lesson from v152 three-literal family upgrade stability
- After finding a minimal replay upgrade for one richer family, the next honest check is whether that same upgrade generalizes to the next larger family before searching for new witness sets.
- If one replay upgrade stabilizes several strictly larger bounded families while preserving the same canonical winner, treat that as evidence that the corpus repair is structural rather than narrowly overfit.
- Keep pushing family size first and schema size second: only widen the artifact surface after a replay-upgraded larger family actually changes the full-domain canonical representative.

## process lesson from v153 monotone closure saturation
- After several widening steps preserve the same canonical winner, stop testing larger monotone families one by one and compute the full closure directly.
- A closure-equality result is a better stopping certificate than another family-size benchmark: once the bounded family already saturates the closure, further widening in that operator class is exhausted.
- When the replay-upgraded corpus isolates one class in the full closure, treat it as the current bounded baseline for that literal set and move the frontier to new literals or non-monotone operators instead of larger monotone formulas.

## process lesson from v154 boolean atom partition closure
- After the monotone lane is saturated, do not continue widening formulas blindly; switch to the exact atom partition of the bounded domain and compute the Boolean closure directly.
- For the current literal set, the right non-monotone object is not another enumerated family but the powerset of the induced atom partition, because that gives an exact frontier count immediately.
- If the replay-upgraded corpus that was sufficient for monotone closure still leaves multiple Boolean classes alive, treat that as a replay-baseline gap for the non-monotone lane rather than as evidence that the monotone results were unstable.

## process lesson from v155 Boolean-closure minimal replay extension
- After a new non-monotone closure object survives, run an exact minimal replay-extension search immediately instead of guessing which extra cases might help.
- When the closure is expressed as unions of induced atoms, the right replay witness object is an atom-cover description; minimal case witnesses should then be interpreted as representatives of the still-free atoms.
- If every minimal witness shares the same atom-level structure, record that structure as the steering object and stop thinking in raw case ids.

## process lesson from v156 Boolean atom basis corpus
- After a Boolean closure and its minimal replay extension are known, package the reusable replay baseline explicitly as a one-representative-per-atom basis corpus.
- Basis corpora are better frontier-closing objects than more family benchmarks, because they immediately tell you whether remaining work is about formulas or about new literals.
- Once a minimal Boolean-complete basis exists for the current literals, stop spending research cycles on larger formula families over those literals and move the frontier to new literals or new operator families.

## process lesson from v157 input-test literal refinement
- After formula families over the current literals are exhausted, the next honest move is to search for new primitive tests and quotient them by their bounded semantic pattern before discussing language growth.
- Primitive-search cycles should report both best single refiners and the minimal basis for full bounded separation, because those answer different design questions.
- When the unique minimal full-separating basis is just coordinate-bit tests, treat that as a signal to add guarded input primitives first and postpone more exotic operator growth until those bits are exhausted.

## process lesson from v158 input-augmented monotone closure
- After discovering a new primitive basis, do not assume replay sufficiency carries over; recompute the exact policy-language closure under the enlarged primitive set immediately.
- Distinguish observation power from definability power: a primitive set can fully separate bounded cases as raw signatures while still requiring a new replay basis for the positive policy language built from those primitives.
- When new primitives enlarge the closure but do not change the current size-1 target selector, treat the next task as replay-basis repair before considering more primitive growth.

## process lesson from v159 augmented monotone basis repair
- After a primitive expansion breaks an existing replay basis, repair the basis immediately with an exact minimal witness search before adding any more primitives.
- If the minimal replay repair is unique, promote that exact witness into the canonical baseline instead of carrying a set of equivalent alternatives.
- Once a primitive set has both an exact closure measurement and an exact repaired replay basis, the next frontier is no longer basis maintenance but genuinely new primitives or operator families.

## process lesson from v160 coordinate-basis monotone completeness
- After a new primitive basis stabilizes, compare its exact closure against the full abstract function class it plausibly targets rather than only against previous family benchmarks.
- If a basis already generates the full positive language on the bounded cube, stop all further positive-formula research over that basis immediately.
- Once positive completeness is proved, the only honest next frontiers are non-monotone primitives or richer action/program structure such as KAT/GKAT-style guarded semantics.

## process lesson from v161 non-monotone adjoinability frontier
- After the positive-language frontier is closed, the right non-monotone next step is an exact adjoinability scan over a bounded primitive library rather than ad hoc formula growth.
- Report frontier growth by subset size, not just by a single winner: singleton, pair, triple, and maximal bases answer different design questions and expose where marginal expressivity saturates.
- If a bounded non-monotone library still tops out far below the full Boolean algebra, treat that as evidence to search for genuinely new primitives or move to guarded-action structure, not as a reason to keep permuting the same library.


## process lesson from v162 Boolean algebra literature refresh
- Free or complete Boolean-algebra ceilings are useful for syntax and denotation, but runtime carriers still need a finite executable quotient with a canonical parity rail.
- Treat operator enrichment as a new semantic object every time; do not inherit executability or constructivity just because the base Boolean layer was tame.
- When a repo already has a finite clopen/prefix carrier plus canonical symbolic equivalence, prefer strengthening that rail over importing atomless or complete semantics into runtime design.

## process lesson from v163 disaster guard hitting quotient
- When disaster axes accumulate, quotient them by required safety obligations before adding more named examples.
- Treat a new candidate state as useful only if it either maps to a known obligation class with a replay witness or forces a new obligation atom.
- Pair the executable quotient search with a proof transfer law: representative coverage should imply coverage for every axis in the same obligation class.

## process lesson from v164 proof-carrying disaster antichain minimizer
- After equality quotienting, prune by subset dominance before solving guard cover; equality classes are not minimal if one signature strictly contains another.
- Treat the subset-maximal obligation antichain as the real replay frontier for a fixed obligation language.
- Route candidate axes through a novelty classifier before adding them to replay: duplicate and dominated axes are regression material, while new atoms are research-frontier material.

## process lesson from v165 private-obligation guard optimality certificate
- After antichain pruning, try to prove guard-cover optimality by private required obligations before running exhaustive set-cover search.
- A selected guard with a private required obligation is forced in every valid cover; collect one such witness per selected guard when possible.
- If private witnesses do not cover every selected guard, split the remaining problem into disjoint shared-obligation blocks and only then use bounded residual search.

## process lesson from v182 DLMF/Julia certificate menu
- Use the DLMF math-agent loop: conjecture -> look up DLMF identities -> translate into Lean/Tau/Rust/Python/Julia -> test numerically or exactly -> formalize a restricted theorem -> generalize only after the restricted theorem checks.
- When a polynomial fast path works on a clean bounded corpus, immediately add an adversarial special-function stress family instead of promoting the fast path as universal.
- Treat DLMF as a source of exact theorem shapes and stress generators, not as runtime numerical evidence. Julia may generate rational certificates and counter-pressure, but Tau/FIRE acceptance still needs symbolic proof objects.
- If a sufficient certificate fails on a true nonnegative family, log it as `UNKNOWN` negative knowledge and add a second certificate family rather than weakening the checker.
- After an experiment proof packet closes, promote the reusable theorem surface into the main local proof library before writing tutorials or papers; this catches integration drift that standalone packets miss.
- Pair every promoted certificate theorem with a tiny replayable checker/demo that reports `ACCEPT` only with a theorem name and otherwise returns `UNKNOWN`.
- After hand-picked demos pass, auto-generate a full-corpus replay spec from the discovery report so the operational checker is tested against the exact research corpus, not only curated examples.

## process lesson from v184 Legendre/Turan reference adapter
- After a special-function family defeats a generic certificate, test a neighboring reference family before generalizing the failure.
- Compare families by certificate profile, not only by truth: Chebyshev envelopes were true but Bernstein-hostile, while Legendre envelopes and Turan differences were true and Bernstein-friendly in the bounded range.
- A reference adapter should record whether it creates a new theorem rule or merely improves dispatch order. v184 improves dispatch order and supplies bounded certificates; it does not yet supply a general Legendre theorem.
- When local mathlib lacks the named special-function surface, keep the result in the executable-certificate tier and route formal soundness through the generic certificate theorem.

## process lesson from v185 Gegenbauer reference adapter
- When a neighboring family remains Bernstein-friendly, widen along a meaningful parameter axis before adding a new theorem recognizer.
- Normalization matters: testing `C_n^lambda(2*x-1) / C_n^lambda(1)` makes the envelope obligation comparable across `lambda`.
- Certificate profiles can distinguish family roles: normalized Gegenbauer envelopes needed up to `16` pieces, while normalized Turan differences needed only `8` in the bounded profile.
- If a generic certificate continues to cover a widened reference family with zero false accepts, promote a dispatch heuristic before attempting a heavier special-function formalization.

## process lesson from v186 asymmetric Jacobi boundary
- Do not generalize a Turan-style inequality from symmetric orthogonal-polynomial families to asymmetric families without endpoint checks.
- A failed Bernstein certificate should be immediately classified: certificate weakness, exact endpoint falsifier, or interior sampled falsifier. v186 showed the failures were exact endpoint counterexamples.
- Endpoint normalization can make envelopes behave well while breaking adjacent Turan-style claims; profile theorem shapes separately.
- The next useful Jacobi step is not more subdivision. It is a corrected Turan statement or normalization.

## process lesson from v187 route interval graph certificates
- For DEX route math, look for dual certificates before improving search heuristics: a positive potential can prove no-positive-cycle structure and also give prefix upper bounds.
- Julia exact rationals are useful when the object is a bridge between real-valued intuition and integer execution; use them to preserve exact floor errors and avoid floating-point artifact claims.
- A route-pruning idea should report false prunes, not only pruning rate. Zero false prunes on a bounded corpus is the signal that the next step is a proof target, while higher pruning rates can wait.
- Opportunity logic should compose with budget logic: a treasury or market-maker path should require both an opportunity certificate and a spend/burn/budget guard before it becomes admissible.
- When a discovery cycle yields both a local integer interval lemma and an abstract certificate lemma, promote those two reusable pieces first; leave full runtime optimality for a later composition proof.

## process lesson from v188 Gasper-cone Jacobi Turan orientation
- When a reference family fails, search for the missing side condition before abandoning the theorem shape. v188 shows the v186 Jacobi Turan failure was a cone/orientation issue.
- Endpoint counterexamples are stronger than certificate failures. They should trigger recognizer narrowing, not deeper subdivision.
- Mirror symmetries can turn a one-sided theorem into a practical two-sided recognizer: right-normalized Jacobi in the `beta >= alpha` cone plus the `x -> 1-x, alpha <-> beta` mirror gives the oriented endpoint rule.
- The useful optimization shape is fragment filtering: test cheap symbolic side conditions first, then emit a small certificate only when the fragment is inside the theorem's domain.
- Record the theorem import boundary explicitly. The bounded recognizer has exact certificates, while the full Gasper theorem still needs Lean closure or a trusted reference bridge.

## process lesson from v189 endpoint obstruction extraction
- After a bounded recognizer finds exact endpoint falsifiers, try to extract the endpoint formula before expanding the corpus.
- A closed obstruction formula is better than a larger counterexample table because it supplies the recognizer's cheapest necessary-condition gate.
- Promote the algebraic skeleton even if the full special-function theorem remains external; this cleanly separates local proof from reference-backed theorem import.
- After the identity is proved, immediately prove the sign theorem used by the runtime/filter. The sign theorem is what turns a formula into a fail-closed recognizer gate.
- If a proof assumes adjacent ratios, define the coefficient recurrence locally and prove the ratio update next; this shrinks the trusted gap without needing the full special-function theorem.

## process lesson from v196 derivative Bernstein monotonicity
- Before adding a derivative certificate to a sign menu, test whether it is
  merely a rephrasing of ordinary Bernstein positivity on the same partition.
  In v196 it was redundant for endpoint-based sign nonnegativity.
- The right Tau optimization surface is the original formula shape, not only
  the polynomial family. Derivative certificates are valuable for monotonicity
  because they reduce a two-variable order obligation to a one-variable sign
  certificate.
- Equal dyadic subdivision is a useful first guardrail, but true monotone
  square-derivative cases with non-dyadic roots remain `UNKNOWN`. The next
  certificate menu should add adaptive critical-point splitting before claiming
  broad monotonicity coverage.
- Once the Lean bridge names the exact theorem surface used by `ACCEPT`, sidecar
  packaging is enough for a tutorial demo. Extractor-shaped benchmarks are the
  next quality improvement, not a blocker for a scoped tutorial.
