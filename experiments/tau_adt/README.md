# Tau Language ADT & Tables — experiment findings (V2, 2026-09-02)

**Status:** EXPERIMENTAL EVIDENCE — authority NONE, nothing mounted; dual-agent
program (Fable lead + Opus adversarial co-experimenter). §§1–4 are each backed by
a machine-checked contract file and reproduced by both agents (the lead re-ran
`opus_run_all.sh`, 15/15, and Opus re-ran the lead's suite, 6/6); §5's numbers
are single-run on one machine and not cross-reproduced between the two harnesses.

**Binary:** Tau 0.7.0-alpha, upstream HEAD `0ac2756f` (ADTs merged 2026-08-28),
built from IDNI/tau-lang with the parser submodule. NOTE: upstream rewrote main's
history — the repo's pinned `external/tau-lang` (2026-06-25, twin `9d7e50f4`) is
pre-ADT; requalification requires a fresh clone and reopens O-003A/O-002/O-003B.

**Corpora:** `tau_experiments/` (lead, 6 files, 6/6) and `opus_tau/` (adversary,
15 files, 15/15 under the fail-closed runner `opus_run_all.sh`). Full adversarial
report: `opus_tau_experiments_report.md` (805 lines, 2026-09-01–02, sha256
967a07ff04ab02682bb7e6eb7532da0bc84b1ef2b8813b2cb2e915329c2e6c64).

## 1. What was validated — with its scope stated exactly

| Construction | File | Scope of the validation |
|---|---|---|
| Relational algebra, meet/join/overlap half: JOIN=meet, UNION=join, SELECT=partial meet | exp1 | 4/8 (queries 1,2,7,8); the complement-based MEMBERSHIP/DIFFERENCE half passes its contract but is broken as a claim for time-varying probes — see F5 |
| Nullifier spent-set overlap; `[t<N]` epoch windows at run level | exp2 (b,c) | sound |
| Raw pointwise-revision mechanism measured: merge on satisfiable, no-op on unsat | exp3 | NOT a working governed ledger — any accepted amendment empties the accumulated table one step later (F4) |
| Admission-kernel branch structure: ternary exclusive + total, machine-checked | exp4 + F10 | control flow only; all three original branch CONDITIONS were wrong (F1/F2/F3) |
| Epoch-versioned policy table (superseded reading provably unreadable outside its window) | exp5 (repaired) | sound; FD is an explicit hypothesis, never schema-carried (F9) |
| Audit-diff REMOVED half: `T1 & T2' = 0` proves append-only (`T1 <= T2`) | exp6 | REMOVED half sound; the ADDED half inherits F5 (false alarms on time-varying rows) |
| Crossing table: `BIDS & ASKS & LAW != 0` decides book-cross with the clearing pair as entailment witness | opus_new1 | interesting, not load-bearing: ~n^3.7 last-step, 32.5 s for a 16x16 book — does not deploy at book scale |
| Key-projected registry: replay guard with a theorem over ALL adversary specs | opus_new2 | the THEOREM is the durable artifact; as a live table ~n^2.2 last-step (13.3 s at 64 keys) — the set itself belongs in Python |
| Guarded escrow: conservation stated jointly with directional monotonicity | opus_new3 | sound AND schema-shaped: essentially flat (0.125→0.213 s for 2→8 cells) — the deployable kind |
| Repaired admission kernel (codes 0/9/7/8/6; defeats F1/F2/F3) | opus_new_admission_kernel_v2 | sound against the three attacks; not governable (F4) and policy-bounded (~16–24 clauses, §5) |

## 2. Design laws (each learned by a working exploit)

- **F1** Registries must store KEY-ONLY projections; overlap of whole rows is not
  membership (same-key spends with differing payloads are disjoint values).
- **F2** Admission is ENTAILMENT (`spend & policy' = 0` or, preferred at scale,
  `valid always (spend -> policy)`); consistency (`spend & policy != 0`) is the
  law-ADOPTION test and admits unauthorized spends. Choosing the sound test is
  free: membership costs the same as overlap (§5).
- **F3** Input malformedness must be checked (`key' = 0` = TOP poisons a join-
  accumulated registry permanently — one-line denial of service).
- **F5** `{A} | {B}` = `(always A) or (always B)` ≠ `always(A or B)`. Complement-
  based DIFFERENCE/audit-ADDED is unsound for time-varying probes; use `{A||B}`
  when probes come from an untrusted channel (changes JOIN semantics — decide
  row time-constancy first).
- **F6** A bv[n] conservation equation is a mod-2^n ring identity — compatible
  with minting. Safety lives in guards; the capacity guard is `b <= MAX - d`
  (`x + y <= MAX` itself wraps and is vacuous).
- **F7** A bare formula in a `{ }` constant is implicitly always-closed:
  `[t<N] && row` collapses to 0. Windowed facts must be implications
  (`[t<N] -> row`), i.e. window guards build MEET (rule) tables, not join tables.
- **F9** ADT schemas cannot carry uniqueness/functional dependencies — an FD is
  an explicit hypothesis in every query that needs it.

## 3. Dead ends (recorded; do not retry)

- **F4 (decisive):** any ACCEPTED pointwise revision — including a benign,
  consistent amendment naming none of the machine's streams — discards the run's
  accumulated stream state one step later (spent-set := F; the verdict stream
  returns to the boundary code; and the input-to-channel mapping shifts, so after
  a revision an operator cannot tell which channel an input will reach — a spend
  was observed landing on the governance channel and being adopted as law).
  Control/attack pair differs only in the amendment. Engine-level; no in-language
  workaround. **Pointwise revision cannot govern an accumulating machine.**
  Governance must live outside the run (epoch re-basing) — consistent with the
  epoch-based settlement model the lead maintains in the repo, though the repo
  was off-limits to this study and that fit was not re-verified here. (Hedge kept deliberately: no literal code-9
  replay after a revision was observed; the machine returns to a state identical
  to one that admitted the same spend.)
- Complement-based audit-diff over `{A}|{B}` with untrusted probes (see F5).
- Expecting schema-level uniqueness from ADT types (see F9).
- Growing law by MEET inside a running kernel at scale (~n^3.1 last-step, n^2.4 global; walls at 200–300
  clauses one-off, and at ~32 policy clauses inside a per-step kernel — §5).

## 4. Harness and backend laws

- **F8** The engine prints translation failures on STDOUT with EXIT 0 and still
  emits a verdict → `%N`-grepping harnesses are fail-OPEN. Any Tau contract that
  gates a decision must fail closed on engine `(Error)` lines, non-zero exit, and
  empty matches (see `opus_run_all.sh`). On the repo's own
  `tests/tau/test_specs_syntax.sh` (read post-sign-off by both agents): the
  matcher is VERIFIED narrower than the engine's error vocabulary — the script
  builds `strip_ansi` precisely so `(Error)` markers can be matched, then
  narrows the match to "Syntax Error" — a real latent gap, worth closing
  defensively. There is NO WITNESS that the F8 translation-failure class is
  reachable through that invocation: in six probe shapes against the study
  binary, no `(Error)` ever arrived with exit 0 (the file runner EXECUTES a
  spec; it does not decide the entailment queries where translation failures
  fire), and the one reachable non-syntax error exited non-zero and was caught.
  The script also self-describes as a syntax-by-execution check — a weak F8
  instance at best. The Python-driven tau tests were not audited.
- **Backend framing:** cvc5 is Tau's bitvector BACKEND, not a second opinion —
  upstream documents the core language and algorithms as independent of it, so
  there is no dual-solver arrangement to lose. The accurate statement: a
  time-constrained BITVECTOR formula fails to reach the only procedure that can
  decide its bitvector content, and the engine answers regardless; pure-sbf
  time-constraint formulas emit no error at all.

## 5. Measured performance walls (single-run, one machine, alpha build)

Lead's axes (`bench_scaling.py`, answers verified):

| Axis | Measurement | Consequence |
|---|---|---|
| bv width 8→64 | flat ~0.19 s | value width is free |
| `{ }`-table rows | 0.18s@2 → 1.4s@16 → 5.3s@32 → 21.5s@64 | spec-value tables ≤16 rows; shard |
| ADT schema totals | 0.26s@12 rows, linear | schema cells are free |
| kernel run steps | ~0.1 s/step at small state | per-intent gating viable only with small state |

Adversary's axes (`opus_bench_forms.py` and kin — the decision-driving numbers):

| Axis | Measurement | Consequence |
|---|---|---|
| direct form (`sat`/`valid always`) | ~n^1.8 last-step (n^1.3 global): 4.4s@200 clauses, 15s@400 | the scaling road, but accelerating — extrapolate with the last-step figure |
| `{ }` single-constant conjunction | ~n^1.6 last-step (n^1.9 global), survives 400 (148 s) | usable for mid-size one-offs |
| law accumulated by MEET | ~n^3.1 last-step (n^2.4 global), WALLS at 200–300 clauses | never grow law by meet at scale |
| admission via `{ }` entailment vs direct | 66x at 64 policy clauses (118.9 vs 1.79 s); TIMEOUT at 128 vs 5.7 s direct | ask admission DIRECTLY; cliff between 32 and 64 |
| policy inside a running kernel | 1.5s@16 clauses → 43.7s@32 | practical ceiling ~16–24 clauses per running kernel |
| crossing table | ~n^3.7 last-step (n^2.1 global), 32.5s@16x16 | does not deploy at book scale |
| key-projected registry (live) | ~n^2.2 last-step (n^1.3 global), 13.3s@64 keys | live set belongs in Python; keep the theorem |
| guarded escrow | flat (0.125→0.213 s for 2→8 cells) | the deployable kind |
| `solve` vs `n`; membership vs overlap | equal cost each pair | witnesses are free; the SOUND test is free |

Exponents are quoted as "last-step (global fit)"; every series except the
`{ }` single constant ACCELERATES, so the last-step figure is the extrapolation
basis. Cost tracks disjuncts and clauses in the formula — never value width or
tuple member count. Whole-corpus wall clock (21 files, 10.6 s) proves nothing about
deployability. Caveat: the `{ }` scaling issue is acknowledged upstream; if that
work lands, the form benches must be re-run before trusting any `{ }`-path
conclusion. The data-plane exclusion rests on row count and would not move.

## 6. Partition recommendation (autonomous DEX) — bounded by the measurements

- **Data plane OUT of Tau:** balances, pools, books, the live nullifier set,
  matching, settlement math. Every row-in-formula encoding walls 4–6 orders of
  magnitude below even a toy DEX; no tuning closes that.
- **Admission/policy plane IN Tau, bounded:** fixed schema; the gate stated in
  DIRECT form (`valid always (spend -> policy)`), never `{ }` entailment; at most
  ~16–24 policy clauses inside a running kernel and ~200 as a one-off; the policy
  pinned as ONE pre-normalized constant recompiled offline — never grown by meet
  inside the run. Registries key-projected, with the live set in Python and the
  all-specs theorem as the Tau artifact.
- **Audit plane IN Tau, offline, unreservedly** — the strongest fit in the study:
  append-only proofs (`T1 & T2' = 0`), guard theorems, epoch-versioned policy
  reads, aggregate invariants over summary rows.
- **Governance plane OUT of Tau's runs** — on correctness grounds (F4), not
  speed: epoch re-basing outside the run (the lead's repo already follows this
  shape; not re-verified within this study).

## 7. Proposed landing (pending review)

`experiments/tau_adt/` carrying both corpora + both runners + this document;
broaden `tests/tau/test_specs_syntax.sh` to fail on any engine `(Error)`
marker — because it is free and correct (the matcher is narrower than the error
vocabulary, §4), not because a live hole was demonstrated — and audit the
Python-driven tau tests likewise; PopperPad: F4 dead end, F5/F6/F7 knowledge entries. Requalifying
`external/tau-lang` is a separate decision (reopens O-003A/O-002/O-003B).

## 8. Upstream addendum (2026-09-02, verified at d80aa50c)

Ten upstream commits landed after this study's pin (0ac2756f), verified against a
rebuilt binary at d80aa50c:

- **Whole-ADT definition arguments** (demo_4.4, 1a01ef71): a tuple-typed argument
  flattens at parse time, so a definition takes a whole record exactly when it
  declares one parameter per flattened member. Verified: `norm(u,v):sbf := u | v`
  then `ex p:Point (norm(p) = 0)` decides T. This improves admission-plane
  ergonomics (typed record predicates without hand-plumbed members); the
  performance walls of section 5 are untouched.
- **Language-level fail-open CLOSED for type mismatches** (787abef6): a definition
  call whose argument types can never match its parameters now errors loudly
  ("disagrees with the argument types of its definition ... can never match")
  instead of being silently ignored. Verified live. This closes a hazard one
  layer below F8 that this study did not name: a policy predicate silently
  no-opping on a type mismatch.
- **Arity mismatches still neither vanish nor error**: a 2-parameter definition
  applied to two whole Points flattens to a 4-argument application that persists
  unexpanded in the output (verified: `ex b4,b3,b2,b1 twop(b4,b3,b2,b1)`). No
  verdict is fabricated, but no error is raised either — the F8 fail-closed
  harness discipline (match verdicts exactly, treat unexpanded applications as
  failure) remains mandatory for admission-plane contracts.
- Crash/hang classes fixed upstream: typed head on a formula-bodied definition
  (was crash, e3d2fcc8), recurrence cases with mismatched argument types (was
  hang, f3704eef); REPL session type definitions now visible to later commands
  (e04744a0).

The section 6 partition recommendation is unchanged.
