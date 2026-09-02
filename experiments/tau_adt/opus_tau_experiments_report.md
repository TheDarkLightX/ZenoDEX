# Independent validation, attack and extension of the Tau ADT table experiments

**Author:** Opus (independent co-experimenter)
**Date:** 2026-09-01
**Binary:** `scratchpad/tau-lang-upstream/build-Release/tau` — Tau 0.7.0-alpha, build `0ac2756f`
**Workspace:** `scratchpad/opus_tau/` (all my files), plus one repair in `scratchpad/tau_experiments/exp5_time_indexed_tables.tau`
**Scope note:** the ZenoDEX repo and its worktrees were not touched.

---

## Counts

| | |
|---|---|
| **validated** | **1** (exp3) |
| **broken** | **4** (exp1, exp2, exp4, exp6) |
| **fixed** | **1** (exp5) |
| **new table kinds** | **3** (+1 repaired admission kernel) |

**Read the "broken" count carefully: all four of those files PASS their own
contracts, and every individual query in them returns the annotated answer.**
What is broken is the claim each file draws from its queries. That gap is the
whole reason the attack corpus exists — a contract harness that only checks
`%N` lines cannot catch any of these four.

**Top correctness finding:** any accepted pointwise revision — including a
benign, consistent amendment that mentions none of the machine's own streams —
resets the accumulated stream state of the running specification, so the exp4
admission kernel's spent set empties (`o0sp := F`) and its verdict stream
returns to the boundary code one step after any governance action.

**Top efficiency finding:** every table construction in this study — mine
included — is built on the `{ }` spec-as-value path, which is the one
`nomic_07_the_map.tau` warns has a known scaling issue. Measured, the same
admission question costs **66x more** through `{ }` entailment than asked
directly at 64 policy clauses (118.9 s vs 1.79 s) and **times out** at 128 where
the direct form answers in 5.7 s. The map's claim for the direct form is
verified on our binary: correct and fast at 200 clauses (4.4 s) and still fine
at 400 (15 s).

---

## 1. Validation

Re-run of the lead's suite on the stated binary, `TAU_TIMEOUT=900`,
`TAU_BA_COMPONENT_FACTORING=1`:

```
$ cd scratchpad/tau_experiments && TAU_BIN=<tau> ./run_experiments.sh
PASS  exp1_relational_algebra.tau
PASS  exp2_zenodex_tables.tau
INFO  exp3_governed_ledger.tau (manual contract)
PASS  exp4_admission_kernel.tau
FAIL  exp5_time_indexed_tables.tau (results: got [F F F F T F] want [T T T F T F])
PASS  exp6_audit_diff_table.tau
4/5 ok        (exp6 arrived mid-session; it passes too)
```

Only exp5 failed mechanically. Per file:

### exp1 — relational algebra — **BROKEN (claim), queries all correct**

Contract `T T T F T T T T` reproduces exactly. Each of the eight answers is a
true statement about the values involved. **H1 ("the encoding closes under the
full relational algebra") is false**: see finding F5. The JOIN/UNION/SELECT
half (meet, join, overlap) is sound; the MEMBERSHIP and DIFFERENCE half is
sound *only* for probes that are constant in time, which the file never says.

### exp2 — ZenoDEX table kinds — **BROKEN (2a), 2b and 2c sound**

Contract `T F T T` and `EXPECTED-TF T T T F F F F` reproduce. Parts (b)
nullifier overlap and (c) the `[t<3]` run-level epoch window are sound and are
the good half of the file. **H2a's "conservation theorem" carries no safety
content**: finding F6.

### exp3 — governed ledger — **VALIDATED**

No machine contract; the file's recorded transcript is its evidence, and it
reproduces line for line — `u[0] := F`, `ia[1] := oflag[t]=1`,
`ir[1] := o9[t]=0 && o9[t]=1` (the round-robin gotcha the file documents),
`u[1] := always oflag[t]:tau' = 0`, the 91-character updated specification,
`ob[1] := F`, `u[2] := F`. The file is accurate about what it measured. Its
*hazard statement* is understated by a wide margin — finding F4 — but that is
an extension of the file, not a defect in it.

### exp4 — two-lattice admission kernel — **BROKEN (three independent breaks)**

Contract `EXPECTED-CODES 0,9,7,8` reproduces exactly. The construction is
nevertheless defeated three separate ways: F1, F2, F3. One structural claim
survived attack and is now machine-checked: F10 (refuted attack).

### exp5 — time-indexed tables — **BROKEN → FIXED**

The only mechanical failure. Root cause and repair: finding F7. Now passes
honestly, with part (b) rewritten because it consisted of two propositional
tautologies (finding F9).

### exp6 — audit diff table — **BROKEN (claim), queries all correct**

Arrived mid-session; contract `T T T T T` reproduces. Its `REMOVED = T1 & T2'`
claims are sound — `REMOVED = 0` genuinely proves `T1 <= T2`, which is real
append-only evidence. Its `ADDED` claims inherit F5 and produce false alarms.

---

## 2. Attacks

Everything below is reproducible; each has a contract file in
`scratchpad/opus_tau/` and is checked by `opus_run_all.sh`.

### F1 — CRITICAL — exp4 admits a double-spend with code 9

The replay test is `(registry & i1) != 0`, an **overlap of the whole spend
spec**. The registry stores whole spend rows, and two spends that share a
nullifier but conflict in any other column are **disjoint as values**, so the
overlap is empty and the replay is not seen.

Root cause, one line (`opus_new2_key_registry_table.tau` query 4):

```
n (({ onul[t]:bv[8] = { #x04 }:bv[8] && oauth[t]=1 })
 & ({ onul[t]:bv[8] = { #x04 }:bv[8] && oauth[t]=0 })) = 0
%1: T          <- the two spends of nullifier 4 do not meet
```

Exploit — `opus_attack_exp4_doublespend.tau`, unmodified exp4 kernel, inputs
`onul=4 && oauth=1` then `onul=4 && oauth=0`:

```
o0res[0] := 0
o0res[1] := 9    o0sp[1] := always oauth[t]:tau' = 0 && onul[t]:bv[8] = { 4 }:bv[8]
o0res[2] := 9    o0sp[2] := (always oauth' = 0 && onul = { 4 }) || (always oauth = 0 && onul = { 4 })
```

Nullifier 4 admitted twice; the registry now holds two rows with the same key.
`oauth=0` is a well-formed spend under exp4's own policy (`oact -> oauth` is
satisfied by `oact=0`), so this is not a malformed input.

### F2 — CRITICAL — exp4 admits a policy-violating spend with code 9

The policy test is `(policy & i1) != 0` — **consistency**. An admission gate
needs **entailment**, `i1 & policy' = 0`. A spend that performs the destructive
action while asserting no authorization is consistent with `oact -> oauth`
(choose `oauth=1`) but does not entail it.

```
n (({ oact[t]=1 }) & ({ oact[t]=1 -> oauth[t]=1 }))  != 0     %1: T   consistent
n (({ oact[t]=1 }) & ({ oact[t]=1 -> oauth[t]=1 })') != 0     %1: T   NOT entailed
```

`opus_attack_exp4_policy.tau`, input `oact[t]=1`: `o0res[1] := 9`.

This is the deeper of the two: consistency is the *correct* test for the nomic
law-accumulation machine exp4 borrowed the shape from, where a proposal that
merely fails to contradict the constitution should be adopted. Reused as an
admission gate the same test means "we could not prove this spend illegal",
which is not authorization.

### F3 — HIGH — one input permanently disables exp4 (registry poisoning)

Nothing constrains the shape of `i1`. A tautological spec is the **TOP** element
of the tau algebra (`n ({ oz[t] = oz[t] })' = 0` → `T`). Joining TOP makes the
registry TOP, after which `(registry & x) != 0` for every nonzero `x`.

`opus_attack_exp4_poison.tau`, inputs `oz[t] = oz[t]` then two fresh spends:

```
o0res[0] := 0
o0res[1] := 9    o0sp[1] := T        <- registry is now TOP
o0res[2] := 7    o0sp[2] := T        <- fresh nullifier 9  rejected as replay
o0res[3] := 7    o0sp[3] := T        <- fresh nullifier 11 rejected as replay
```

One line of input, permanent denial of service, no recovery path in the machine.

### F4 — CRITICAL — **top finding** — any accepted revision resets accumulated state

exp3's header calls the hazard "a satisfiable amendment that CONTRADICTS the
running spec REPLACES it". The measured behaviour is much stronger: **any
accepted revision — consistent, tightening, and mentioning none of the
machine's streams — discards the accumulated stream state one step later.**

Control, `opus_exp3_control_noamend.tau` — same machine, same rows, every
amendment unsatisfiable so revision never fires:

```
ob[0] := F
ob[1] := always orow[t]:tau' = 0
ob[2] := always orow[t]:tau' = 0
ob[3] := always orow[t]:tau' = 0     <- append-only holds
```

Attack, `opus_attack_exp3_benign_amend.tau` — identical except that `oflag[t]=1`
is offered on the amendment channel at step 2:

```
ob[1] := always orow[t]:tau' = 0
ob[2] := always orow[t]:tau' = 0     <- amendment accepted here
ob[3] := F                           <- the appended row is GONE
```

The amendment mentions neither `ob` nor `ir`. The two runs differ in nothing
else. Applied to the admission kernel (`opus_attack_exp4_gov_replay2.tau`,
exp4 plus `u[t] = i2[t]`, spends file-driven):

```
o0res: 0,9,7,7,0,8,8,8,8,8,8,8,8,8,8,8,8
              ^ amendment accepted     ^^ boundary state again
o0sp[3] := always oauth' = 0 && onul = { 4 }
o0sp[4] := F                          <- spent set emptied
```

Every nullifier ever spent is unspent again. **Honest limit on this claim:**
the revision also detaches the file-bound spend channel, so subsequent steps
read `i1 = 0` and answer 8; I did **not** observe a literal code-9 replay in
this transcript. What is observed is that the kernel returns to a state
identical to step 0, where the identical spend *was* admitted with code 9. The
console variant (`opus_attack_exp4_gov_replay.tau`, codes `0,9,7,7,0,8,0,8`)
shows the reset recurring on each revision, and shows that after a revision the
input-to-channel mapping shifts so a spend can land on the governance channel
and be adopted as law.

**Consequence for ZenoDEX:** pointwise revision cannot govern a running
settlement machine. A governed kernel and an accumulating kernel are not
composable on this engine. exp4's "no external validator" property is exactly
what fails — the machine cannot be amended without being destroyed.

### F5 — HIGH — exp1/exp6 complement operators are unsound off the constant rows

A table written `{ A } | { B }` is `(always A) OR (always B)`, **not**
`always(A OR B)`. The two differ, strictly, and the gap is precisely the set of
streams that move between rows over time. Every operator built on a table's
complement inherits the gap.

Machine-checked in `opus_attack_exp1_difference.tau` (sbf, so no translator
involvement). `PRICED = { hi=1,lo=0 } | { hi=1,lo=1 }`;
`P = { ([t<3] -> key2) && ([t>=3] -> key3) }`:

```
(3)  P entails always(okhi=1) - its key is a PRICED key at EVERY step   T
(4)  yet  P & PRICED' != 0    - DIFFERENCE reports P as unpriced        T
(5)  CONTROL: a time-CONSTANT priced row is correctly swallowed         T
(6)  ({A}|{B}) <= {A||B}                                                T
(7)  {A||B} has models outside ({A}|{B})  - strict, and this is the gap  T
(8)  REPAIR: against {A||B}, P is a member and DIFFERENCE drops it       F
```

(3) and (4) together are the contradiction. The same row makes exp6's audit
diff report a spurious `ADDED` against an unchanged table.

**Repair:** encode a table as one constant with an internal disjunction,
`{ A || B }`, whenever the probe is not known to be time-constant. Then P is
correctly a member and a genuinely absent row still survives the difference.
The choice is not cosmetic: `{A}|{B}` is right when rows are *known* to be
time-constant facts, `{A||B}` when probes come from an untrusted channel — as
they do in any admission setting.

### F6 — MEDIUM — exp2's conservation theorem is a ring identity

`(x - d) + (y + d) = x + y` holds in `bv[8] = Z/256` for **every** `d`, with no
hypothesis. `opus_attack_exp2_wraparound.tau` proves the general form outright
(query 3, `T`), so no hypothesis remains that a transfer could violate. The
theorem is therefore satisfied by the transfer that mints value:

```
(1) transfer 250 out of a balance of 10 still "conserves"     T
(2) and in that same transfer  alice: 10 -> 16,  bob: 5 -> 255 T
```

256 units created, sum preserved mod 256, conservation "proved" throughout.

**Repair** (queries 4–6, and `opus_new3_guarded_escrow_table.tau`): guards are
what carry the safety content. `d <= b.alice` yields `c.alice <= b.alice`;
`b.bob <= 255 - d` yields `c.bob >= b.bob`. Note the capacity guard must be
written `b.bob <= 255 - d` and **not** `b.alice + b.bob <= 255` — the latter sum
wraps, so the guard is vacuous. I made exactly that mistake first and the
theorem came back `F`; the failing form is documented in the escrow file.

### F7 — MEDIUM — exp5's time-guarded rows were dead values

A tau constant is read under an implicit `always`, so `{ [t < 3] && oid[t]=1 }`
asserts "for all t, t < 3", false at t=3, and the row collapses to 0:

```
n { [t < 3] && oid[t]:bv[8] = { #x01 }:bv[8] } = 0      %1: T
```

exp5 claimed `T T T F` for four values that are all `0`; the binary answered
`F F F F` and only the fourth "control" agreed, by accident. **Fixed** with the
implication form — the same shape exp2(c) already used at run level:

```
n { [t < 3] -> oid[t]:bv[8] = { #x01 }:bv[8] } != 0     %1: T
```

The repaired part (a) proves the reading is *entailed* inside its epoch and the
cross-epoch forgery is *impossible* (meet = 0), not merely unproven.

### F8 — MEDIUM — the contract harness is fail-OPEN

Mixing time constraints with bitvector columns inside a constant makes the
engine print `(Error) Failed to translate the formula to cvc5: ...` **on
stdout**, exit code **0**, and still print a verdict. `nomic_run_all.sh` and
`run_experiments.sh` score by grepping `^%N:` only, so a file whose bitvector
decision procedure never ran scores `PASS` identically to a fully decided one.

I did not observe a wrong answer — all six verdicts I hand-checked were
correct — so this is a harness finding, not a soundness bug. Details and a
minimal repro: `opus_tau/opus_cvc5_faildopen.md`. Mitigation:
`opus_tau/opus_run_all.sh` fails closed on engine `(Error)` lines, on non-zero
exit, and on a contract that expects output but matches none. Its error gate
excludes `tau> ` echo lines — the REPL echoes input, so a comment quoting an
error string trips a naive gate, which happened once while writing exp5.

### F9 — LOW (structural) — a fixed ADT schema cannot express a functional dependency

exp5's original part (b) proved two propositional tautologies: the first
restated a hypothesis as its conclusion, the second asked for a violation of an
FD it had already assumed. Neither said anything about tables. The honest
content, now in the repaired file:

```
(b1) ex t:Tab (t.r1.id = t.r2.id && t.r1.qty != t.r2.qty)      T
```

Uniqueness is **not** a property of an ADT table type — it must be carried as an
explicit hypothesis in every query that needs it. Once carried it has real
consequences (b2 proves FD transitivity over three rows, with a non-vacuity
witness). For ZenoDEX: key uniqueness is never free from the schema.

### F10 — REFUTED ATTACK — exp4's verdict branches are exclusive and total

The brief asked whether two branches can fire at once or a step can get stuck.
Neither. The formula-level ternary `c ? A : B` normalizes to `(~c | A) & (c | B)`
— a genuine if-then-else, which the engine prints itself at run start. Now
machine-checked over the three tau values the conditions read
(`opus_refuted_exp4_branch_exclusivity.tau`, `T F F T T T`): totality holds,
both pairwise overlaps are unsatisfiable, and all three branches are reachable
so neither result is vacuous.

**This is a real result, not a non-finding.** exp4's control flow is sound; what
is wrong is what the branch *conditions* test. Anyone repairing exp4 should keep
the branching and change the tests, which is what my kernel does.

---

## 3. New table kinds

Three new kinds plus a repaired kernel. All carry nomic-style contracts with
unsat controls and pass under the fail-closed runner.

### Kind 1 — the CROSSING TABLE — `opus_new1_crossing_table.tau`

`EXPECTED-RESULTS: T T T T T F`

Existing kinds answer "is this row present?". A book must answer a relational
question: "do these two tables admit a pair whose prices cross?" Bids and asks
are ordinary table values over **disjoint column streams**, so their meet is the
full cartesian product; the matching law is a third value containing no rows at
all, and the crossing set is the meet of the three:

```
BIDS  = { obpx=5, obq=10 } | { obpx=7, obq=4 }
ASKS  = { oapx=6, oaq=8  } | { oapx=9, oaq=3 }
LAW   = { obpx >= oapx }
CROSS = BIDS & ASKS & LAW
```

"The book crosses" is the single decidable question `CROSS != 0`, and the
clearing pair is forced — `CROSS` **entails** `(bid 7, ask 6)`, so no other pair
is in it. Query 5 is the control that makes query 4 mean something: drop LAW and
the same non-crossing book "matches", because the bare product is non-empty.

**ZenoDEX surface:** the CLOB admission gate. A batch may be admitted only if
`CROSS` is non-empty, and the pair that clears is the membership witness — both
decided without running a matching engine. It composes with the repaired kernel:
crossing is a policy predicate, the order id is a registry key.

### Kind 2 — the KEY-PROJECTED REGISTRY — `opus_new2_key_registry_table.tau`

`EXPECTED-RESULTS: T T T T T T`

The direct repair of F1, as a table kind rather than a patch: registry rows are
**key-only projections** `{ onul = k }`, and admission joins the key, never the
row. The payoff is a theorem quantified over **all tau values** — every spend an
adversary can write, not a list of cases:

```
type Sp = {row: tau}.
n all v:Sp (((v.row != 0) && ((v.row & { onul[t]:bv[8] = { #x04 }:bv[8] }') = 0))
        -> ((v.row & ({ onul[t]:bv[8] = { #x04 }:bv[8] } | { onul[t]:bv[8] = { #x09 }:bv[8] })) != 0))
%1: T
```

with its non-vacuity witness, and the falsification of the full-row alternative
alongside it. **ZenoDEX surface:** nullifier / replay-guard tables, and any
"used exactly once" set — order ids, intent hashes, epoch receipts.

### Kind 3 — the GUARDED ESCROW TABLE — `opus_new3_guarded_escrow_table.tau`

`EXPECTED-RESULTS: T F T T`

The repair of F6 as a kind: a balance table whose guards are part of the schema
contract, and whose conservation claim is stated **jointly with directional
monotonicity**, which is the half that actually fails at the wrap boundary.
Three cells, one move, with the two guards that make it sound. The important
query is (3), the attack control: **drop the guard and a depositor gains while
conservation still holds** — a conservation theorem alone is compatible with
minting. **ZenoDEX surface:** deposit/withdraw, escrow lock/release, vault
rebalancing — any two-table value movement.

### Repaired kernel — `opus_new_admission_kernel_v2.tau`

`EXPECTED-CODES: 0,9,7,8,6`

exp4 with all three breaks closed, keeping the branch structure that F10 shows
is sound. It adds a declared **key channel** `i2` and a binding check the
machine verifies itself, so the host cannot lie about the key:

| code | condition | closes |
|---|---|---|
| 6 malformed | `i1 & i2' != 0` (key not entailed) or `i2' = 0` (key is TOP) | F3 |
| 7 replay | `registry & i2 != 0` — key-projected | F1 |
| 8 policy | `i1 & policy' != 0` — **entailment**, not consistency | F2 |
| 9 admitted | `registry := registry \| i2` — the key, not the row | |

Measured on the three attack sequences that defeated exp4:

```
o0res[0] := 0
o0res[1] := 9   admit nullifier 4        o0sp[1] := always onul = { 4 }
o0res[2] := 7   ATTACK 1 (oauth=0 replay)  <- exp4 gave 9
o0res[3] := 8   ATTACK 3 (unauthorized)    <- exp4 gave 9
o0res[4] := 6   ATTACK 2 (TOP)             <- exp4 gave 9 and poisoned
o0sp[4] := always onul[t]:bv[8] = { 4 }    <- registry intact
```

**It does not fix F4.** No in-kernel change can: the reset is a property of the
engine's revision procedure, not of the specification. This kernel must not be
combined with a `u` channel.

---

## 4. Assessment — what belongs in the repo, what does not

**Worth keeping as an experimental corpus** (`experiments/tau_adt/`, marked
experimental, pointer-only per the segregation rule):

- **The attack corpus.** Eight contract-checked files that encode findings F1–F7
  and F10. These are the durable artifact: each is a negative result that a
  future ADT experiment can be run against. F5 and F6 in particular are
  *reusable lemmas about the substrate*, not facts about the lead's files.
- **`opus_run_all.sh` and the F8 note.** If any Tau contract ever gates a
  ZenoDEX decision, a fail-open harness is disqualifying. This is the smallest
  piece of work here with the clearest payoff. **Unverified extrapolation:** I
  claimed in an earlier draft that this "applies to the existing `tests/tau/`
  scripts today". The ZenoDEX repo was off-limits this round and I never read
  those scripts. Whether they are fail-open must be checked before the claim is
  repeated.
- **Kind 2 (key-projected registry).** Its *theorem* is the durable part —
  quantified over all specs rather than over examples, and cheap to check. Its
  *table* is not deployable: 64 keys costs 13.3 s (§5.4), so the registry
  belongs in Python with Tau proving the projection law it must satisfy.
- **Kind 3 (guarded escrow).** The strongest keep. It is the one kind that is
  schema-shaped rather than data-shaped, so it is essentially free to widen
  (2 → 8 accounts: 0.125 → 0.213 s, §5.4), and the `255 - d` versus
  `x + y <= 255` distinction is a real integer-math trap the repo's
  checked-arithmetic discipline should record whether or not Tau is adopted.

**Interesting, not yet load-bearing:**

- **Kind 1 (crossing table).** The prettiest construction here and genuinely
  ZenoDEX-shaped, but two problems compound. It decides *whether* a book
  crosses, not *how it clears* — no volume, no priority, no (A,B) objective —
  and it is the worst-scaling thing I built: ~n^3.7 in book side length, 32.5 s
  for a 16×16 book (§5.4). A real book is thousands of levels. As a matching
  engine it is out by orders of magnitude; only as a tiny admission predicate
  over a pre-reduced top-of-book could it earn its place.
- **The repaired kernel.** Sound against the three attacks and a good
  demonstration, but two independent limits: F4 means it cannot be governed, and
  §5.3 puts its practical policy ceiling at ~16–24 clauses (1.5 s at 16, 43.7 s
  at 32) because the entailment test fires every step. A settlement kernel that
  cannot be amended without being destroyed, and that caps out at two dozen
  policy clauses, is not deployable as it stands.

**Dead ends — record and stop:**

- **Pointwise revision (`u`) as a governance mechanism for any accumulating
  machine.** F4 is decisive and I see no in-language workaround: the reset is in
  the engine. Anything built on "the run IS the institution" plus an amendment
  channel inherits it. This is the single most valuable thing learned, and it is
  a negative.
- **Complement-based DIFFERENCE / audit-diff on `{A}|{B}` tables with untrusted
  probes.** Usable only with the `{A||B}` encoding (F5), which changes the JOIN
  semantics too — the redesign is not free, and should not be attempted without
  deciding first whether rows are time-constant by construction.
- **Expecting uniqueness or any schema constraint from ADT table types.** F9.

**Honest overall read.** The ADT substrate is genuinely good at what the
tutorials claim for it: tables as values, membership and selection as algebra,
negative answers as proofs, and quantification over a structured space —
including over *all specifications*, which is what makes the Kind 2 theorem
strong in a way a test suite cannot be. Where it is currently unsafe is at every
point where a construction crosses from that static algebra into a running,
accumulating, amendable machine: F3, F4 and F5 are all instances of the same
pattern, an operation whose meaning was fixed for well-behaved constant inputs
being handed an adversarial or time-varying one. The four "broken" files all
pass their contracts, which is the finding underneath the findings.

---

## 5. Efficiency: how much of a DEX can live in Tau?

All timings: this machine, Tau 0.7.0-alpha `0ac2756f`, single run each, hard
timeout stated per table. **Absolute seconds do not transfer between machines;
the clause counts, the growth exponents and the walls do.** Scripts:
`opus_bench_forms.py`, `opus_bench_kinds.py`, `opus_bench_corpus.py`,
`opus_bench_kernel_policy.py`. Axes are chosen to complement
`bench_scaling.py` (which sweeps bv width, fact-table rows, ADT schema size and
kernel run length) — nothing here duplicates those.

### 5.1 The corpus itself is fast, which proves nothing

Every file in both suites, whole-file wall clock (`opus_bench_corpus.py`):

| | files | total | slowest file | per query |
|---|---|---|---|---|
| my corpus | 15 | 7.0 s | 0.77 s | 0.055–0.154 s |
| lead's suite | 6 | 3.7 s | 1.14 s | 0.101–0.126 s |

21 files, **10.6 s total, nothing over 1.2 s**. This is the trap: at
demonstration scale every construction in this study is instant, so the corpus
carries no information about whether any of it is deployable. That is what the
rest of this section is for.

### 5.2 Verifying the map's claim — direct form vs `{ }` spec-value

`nomic_07_the_map.tau` claims the direct form is "measured correct and fast far
beyond real-world rule-set sizes (200+ clauses)" while "the spec-as-value
one-off path still has a known scaling issue there". Same logical question — an
N-link implication chain plus a contradiction — asked four ways. Timeout 300 s.

| clauses | A `sat always` | B `valid always` | C `n { chain } = 0` | D `n ({c1} & … & {cN}) = 0` |
|---|---|---|---|---|
| 17 | 0.229 | 0.207 | 0.332 | 0.449 |
| 40 | 0.499 | 0.534 | 1.374 | 1.834 |
| 80 | 1.069 | 1.055 | 4.030 | 10.456 |
| 120 | 1.999 | 1.942 | 12.692 | 37.261 |
| 200 | **4.446** | **4.554** | 28.379 | 182.576 |
| 300 | 8.837 | 8.315 | 94.428 | **TIMEOUT** |
| 400 | 14.976 | 16.030 | 148.101 | **TIMEOUT** |

Every answer returned was correct (`F` for the unsat chain, `T` for the
entailment and for the value-is-zero queries).

**The map's claim is verified, with one correction.** The direct form is indeed
correct and fast past 200 clauses — 4.4 s — and keeps going to 400 at 15 s. Its
growth is **~n^1.3 as a global fit over 17→400, but ~n^1.8 across its last
doubling (300→400)** — it is mildly superlinear and *accelerating*, not the
"roughly linear" the map states. Anyone extrapolating should use the last-step
exponent, which is the conservative one.

**A note on every exponent in this section.** These series accelerate, so a
global fit and a last-doubling exponent differ, sometimes by a lot. Below I give
**last-step (global)** for each, and the last-step figure is the one to
extrapolate from:

| series | last step | global fit |
|---|---|---|
| direct `sat` | **n^1.8** (300→400) | n^1.3 |
| `{ }` single constant | **n^1.6** (300→400) | n^1.9 |
| law by meet | **n^3.1** (120→200) | n^2.4 |
| crossing table | **n^3.7** (8→16) | n^2.1 |
| key registry | **n^2.2** (32→64) | n^1.3 |

The `{ }` single-constant form is the only one that *decelerates*. The ordering
that matters is unchanged either way: direct beats `{ }`-one-off beats meet, and
the two data-shaped kinds are the steepest things measured.

**The `{ }` warning is understated.** Two different `{ }` shapes behave very
differently, and the map does not distinguish them:

- **C, one constant** (`{ }` holding the whole conjunction): **~n^1.9 global,
  n^1.6 last-step**, survives 400 clauses at 148 s. Slow, not fatal, and the only
  series here that decelerates.
- **D, law accumulated by meet** (one constant per clause, `&`-chained):
  **~n^2.4 global but n^3.1 across its last measured doubling**, and it hits a
  wall between 200 and 300 clauses. **This is the shape the nomic living
  constitution and exp4's kernel actually use.**

The `{ }` penalty relative to direct grows from 1.5x at 17 clauses to ~10x at
300–400 for shape C, and from 2x to **41x at 200 and unbounded past 300** for
shape D.

### 5.3 The per-trade admission question — the measurement that decides the DEX

This is the query a DEX would run on every trade: does this spend satisfy an
N-clause policy? Asked as `{ }` entailment (`n (spend & policy') = 0` — the form
my repaired kernel uses) and directly (`valid always (spend -> policy)`).
Timeout 200 s.

| policy clauses | `{ }` entailment | direct `valid` | penalty |
|---|---|---|---|
| 4 | 0.149 | 0.138 | 1.1x |
| 8 | 0.268 | 0.211 | 1.3x |
| 16 | 0.626 | 0.397 | 1.6x |
| 32 | 2.973 | 0.868 | 3.4x |
| 64 | **118.920** | 1.794 | **66x** |
| 128 | **TIMEOUT** | 5.665 | — |

The `{ }` path falls off a cliff between 32 and 64 clauses: **2x the policy
costs 40x the time**. The direct form is linear-ish throughout and answers 128
clauses in 5.7 s.

And the cliff is not an artifact of one-off queries — it appears **inside the
running machine**, earlier, because the test executes every step
(`opus_bench_kernel_policy.py`, my repaired kernel, policy size swept, two
spends, verdicts correct at `0,9,7` throughout):

| policy clauses | 2 | 4 | 8 | 16 | 32 |
|---|---|---|---|---|---|
| seconds | 0.610 | 0.657 | 0.933 | 1.525 | **43.702** |

**The repaired kernel's practical policy ceiling is roughly 16–24 clauses** at a
two-second admission budget. That is a real number to design against, and it is
small.

### 5.4 The new table kinds at 2x/4x/8x

| crossing table (bids × asks) | 2×2 | 4×4 | 8×8 | 16×16 |
|---|---|---|---|---|
| seconds | 0.378 | 0.474 | 2.446 | **32.512** |

| key registry (keys) | 2 | 4 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|---|
| seconds | 0.135 | 0.204 | 0.365 | 0.879 | 2.929 | **13.338** |

| guarded escrow (ADT cells) | 2 | 3 | 4 | 6 | 8 |
|---|---|---|---|---|---|
| seconds | 0.125 | 0.139 | 0.193 | 0.167 | 0.213 |

Two of my three kinds are **data-shaped and scale badly**: the crossing table
grows ~n^3.7 in book side length across its last doubling (n^2.1 as a global fit
— it accelerates) and needs 32 s for a 16×16 book; the registry grows ~n^2.2
last-step (n^1.3 global) and needs 13 s for 64 keys. A real book has thousands of levels and
a real nullifier set has millions of entries — four to six orders of magnitude
past these walls.

The third is **schema-shaped and essentially flat**: widening the escrow table
from 2 to 8 accounts costs 0.125 s → 0.213 s. This matches the lead's ADT axis
(`adt_total_rows2..12`: 0.076 → 0.260) and their bv-width axis
(`bv8..bv64`: 0.183 → 0.216, free). **Cost tracks the number of disjuncts and
clauses in the formula, not the width of the values or the number of tuple
members.** That single sentence is the whole efficiency story.

### 5.5 Query form at fixed content

Eight-row fact table, same data, four question forms:

| form | seconds |
|---|---|
| `n (probe & table') = 0` — membership | 0.440 |
| `n (probe & table) != 0` — overlap | 0.426 |
| `solve` — membership plus witness extraction | 0.428 |
| `sat always (…)` — direct, simpler question | 0.064 |

Two usable facts. **Witness extraction is free**: `solve` costs the same as the
`n` decision, so if you are paying for the verdict, take the model too — that is
where a settlement witness or a counterexample comes from at no extra cost.
And **membership and overlap cost the same**, so preferring the sound test
(membership/entailment) over the cheap-looking one (overlap) costs nothing —
which matters, because F1 and F2 are both bugs caused by using overlap where
entailment was required.

### 5.6 Recommended partition for a DEX

Grounded in the measurements above, not in taste.

**Out of Tau — the data plane.** Balances, pools, order books, the nullifier
set, routing, batch clearing, per-trade matching, settlement arithmetic over
real volumes. Every Tau encoding that puts *rows* in the formula is superlinear
with a hard wall two orders of magnitude below a toy DEX: 64 fact-table rows is
21 s (lead's axis 2), 64 registry keys is 13 s, a 16×16 book is 33 s. There is
no tuning that closes a 10^4–10^6 gap. Python keeps the data.

**Into Tau — the admission and policy plane, bounded.** Per-trade policy checks
over a **fixed schema**, conservation and monotonicity theorems, epoch guards,
reject-code precedence. This is where Tau is both cheap and uniquely valuable:
ADT schema width is free, bv width is free, and the answers are proofs over
*all* values rather than over sampled cases — the Kind 2 registry theorem
quantifies over every specification an adversary can write, which no test suite
can do. Budget: **≤ ~24 policy clauses in a running kernel, ≤ ~200 in a direct
one-off**, and state the check as `valid always (spend -> policy)`.

**Into Tau — the audit plane, offline, unreservedly.** Consistency, entailment,
redundancy and constitutionality questions over rule sets, run off the hot path.
Direct form handles 400 clauses in 15 s, negative answers are proofs, and
nothing here is latency-critical. This is the strongest fit in the whole study.

**Out of Tau — the governance plane.** Not for efficiency but for F4: pointwise
revision resets accumulated state, so an amendable running machine cannot hold a
ledger or a spent set. Policy changes must be recompiled and re-pinned offline,
never applied to a live run.

A concrete shape: Python computes and holds state; for each trade it emits a
fixed-schema tuple; Tau answers one direct-form admission question against a
pinned policy constant of a couple of dozen clauses; a nightly offline Tau job
runs the audit-plane entailment checks over the full rule set. That partition
uses Tau exactly where its cost curve is flat and its guarantees are
irreplaceable, and nowhere else.

### 5.7 Top three efficiency rules for whatever stays in Tau

1. **Ask directly; reserve `{ }` for small meta-questions about specs.**
   `valid always (spend -> policy)` rather than `n (spend & policy') = 0`:
   identical question, identical answer, **66x faster at 64 clauses** and the
   only one that survives 128. The `{ }` path is the meta-tool the map says it
   is — specs as objects, at small scale — and it is not the hot path.

2. **Put the schema in the formula and the data outside it.** Cost tracks
   disjuncts and clauses, not value widths or tuple members:
   `bv[8] → bv[64]` is free (0.183 → 0.216 s), 2 → 8 ADT cells is free
   (0.125 → 0.213 s), but 2 → 64 table rows is 0.18 → 21 s. Encode a trade as a
   fixed-width tuple over a fixed schema; never enumerate rows as disjuncts.

3. **Never grow law by meet inside a running machine.** The meet-accumulated
   shape is the worst measured (~n^2.4, wall at 200–300 clauses one-off) and it
   is worse inside a run, where the test fires every step — my repaired kernel
   goes from 1.5 s at 16 policy clauses to 43.7 s at 32. Pin the policy as one
   pre-normalized constant, recompiled offline when it changes; do not let a
   `run` accumulate it.

**Honest caveat on all of the above.** These are single-run numbers on one
machine against an alpha build whose `{ }` scaling issue is acknowledged
upstream and being worked on. If that work lands, 5.2 and 5.3 must be re-run
before any of the `{ }`-path conclusions are trusted — the partition in 5.6
would loosen, though the data-plane exclusion in the first bullet rests on row
count and would not move.

---

## 6. Reproduction

```bash
S=<scratchpad>
TAU=$S/tau-lang-upstream/build-Release/tau

# the lead's suite (6/6)
cd $S/tau_experiments && TAU_BIN=$TAU TAU_TIMEOUT=900 ./run_experiments.sh

# my corpus under fail-closed gates (15/15)
cd $S/opus_tau && TAU_BIN=$TAU TAU_TIMEOUT=900 ./opus_run_all.sh

# a single query in a fresh process (no session name binding)
$S/opus_tau/opus_q.sh 'n { oz[t] = oz[t] }'"'"' = 0'

# the benches (§5). Run one at a time - concurrent runs contaminate timings.
cd $S/opus_tau
BENCH_TIMEOUT=300 BENCH_SIZES=17,40,80,120,200,300,400 python3 opus_bench_forms.py $TAU
BENCH_TIMEOUT=200 python3 opus_bench_kinds.py $TAU
BENCH_TIMEOUT=200 python3 opus_bench_kernel_policy.py $TAU
python3 opus_bench_corpus.py $TAU $S/opus_tau $S/tau_experiments
```

Total corpus cost, for a CI budget: **21 files, 10.6 s**. The benches are much
heavier — `opus_bench_forms.py` alone is ~20 minutes because of the two
`{ }`-meet timeouts at 300 and 400 clauses.

### File inventory — `scratchpad/opus_tau/`

| file | contract | finding |
|---|---|---|
| `opus_run_all.sh` | — | fail-closed runner (F8) |
| `opus_q.sh` | — | single-query harness |
| `opus_cvc5_faildopen.md` | — | F8 note + minimal repro |
| `opus_attack_exp1_difference.tau` | `T T T T T T T F` | F5 |
| `opus_attack_exp2_wraparound.tau` | `T T T T T F` | F6 |
| `opus_exp3_control_noamend.tau` | `OB: F R R R` | F4 control |
| `opus_attack_exp3_benign_amend.tau` | `OB: F R R F F` | **F4** |
| `opus_attack_exp3_wipe.tau` | `OB: F R F F F` | F4 (law rewrite) |
| `opus_attack_exp4_doublespend.tau` | `CODES: 0,9,9` | F1 |
| `opus_attack_exp4_policy.tau` | `CODES: 0,9` | F2 |
| `opus_attack_exp4_poison.tau` | `CODES: 0,9,7,7` | F3 |
| `opus_attack_exp4_gov_replay2.tau` | `CODES: 0,9,7,7,0,8×12` | **F4** on the kernel |
| `opus_attack_exp4_gov_replay.tau` | `CODES: 0,9,7,7,0,8,0,8` | F4, console variant |
| `opus_refuted_exp4_branch_exclusivity.tau` | `T F F T T T` | F10 (refuted) |
| `opus_new1_crossing_table.tau` | `T T T T T F` | Kind 1 |
| `opus_new2_key_registry_table.tau` | `T T T T T T` | Kind 2 |
| `opus_new3_guarded_escrow_table.tau` | `T F T T` | Kind 3 |
| `opus_new_admission_kernel_v2.tau` | `CODES: 0,9,7,8,6` | repaired kernel |
| `io/spends.in` | — | file-driven spend channel |
| `opus_bench_forms.py` | — | §5.2 direct vs `{ }`, rule-set size |
| `opus_bench_kinds.py` | — | §5.3–5.5 admission encodings, kinds at scale, query form |
| `opus_bench_corpus.py` | — | §5.1 wall clock for every corpus file |
| `opus_bench_kernel_policy.py` | — | §5.3 policy size inside the running kernel |
| `bench_forms.md` / `.json` | — | §5.2 raw results |
| `bench_kinds.md` / `.json` | — | §5.3–5.5 raw results |
| `bench_corpus.md` / `.json` | — | §5.1 raw results |
| `bench_kernel_policy.md` / `.json` | — | §5.3 raw results |
| `bench/` | — | every generated `.tau` the benches timed |

One file outside my workspace was edited, as the brief directed:
`scratchpad/tau_experiments/exp5_time_indexed_tables.tau` — repaired
construction and honest contract `T T T T F T T T T`, with both repairs
explained in its header.
