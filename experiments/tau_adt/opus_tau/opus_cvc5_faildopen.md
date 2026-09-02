# Engine note: cvc5 translation failures are fail-OPEN

**Binary:** Tau 0.7.0-alpha, build `0ac2756f`.

**What cvc5 is here.** Per the upstream README: "CVC5 is used only in order to
support the theory of bitvectors within the language. The core language and its
algorithms are independent of CVC5." So cvc5 is the **bitvector backend**, not a
second opinion — there is no dual-solver cross-check to lose. A pure-`sbf`
formula never involves cvc5 at all, time constraints included (verified: the
`sbf` time-guarded entailment in `opus_attack_exp1_difference.tau` query 3 emits
no error line). The failure below is therefore narrow and specific: a
**time-constrained bitvector** formula fails to reach the only procedure that
can decide its bitvector content, and the engine answers regardless.

Mixing constant time constraints (`[t < N]`, `[t >= N]`) with bitvector
columns inside a `{ }` tau constant makes the engine emit

```
(Error) Failed to translate the formula to cvc5: ex b1 ([t >= 3] || b1 = { 1 }:bv[8]) && ([t < 3] || b1 = { 2 }:bv[8]) && b1 != { 1 }:bv[8]
```

and then **print a definite verdict anyway**. Measured properties of this
behaviour:

| property | measured value |
|---|---|
| stream the `(Error)` lines go to | **stdout**, not stderr |
| process exit code | **0** |
| verdict still printed | yes (`%1: F`) |
| verdict correctness, in the 6 cases hand-checked here | correct in all 6 |

Minimal reproduction:

```bash
printf 'set charvar off\nset maxsplits 1\nn ({ ([t < 3] -> ox[t]:bv[8] = { #x01 }:bv[8]) && ([t >= 3] -> ox[t]:bv[8] = { #x02 }:bv[8]) } & { ox[t]:bv[8] = { #x01 }:bv[8] }'"'"') = 0\n' \
  | TAU_BA_COMPONENT_FACTORING=1 tau -q
```

## Why this matters more than the messages themselves

`nomic_run_all.sh` and `run_experiments.sh` both score a file by grepping
`^%[0-9]+:` out of the combined output. Neither looks at the exit code, and
neither looks for `(Error)`. So a file whose bitvector decision procedure
**failed to run at all** is scored `PASS` exactly like one that was fully
decided. The contract harness cannot tell a sound verdict from a degraded
one, which is the opposite of the fail-closed discipline these contracts
exist to provide.

I did **not** observe a wrong answer — every verdict I could check by hand
was correct, and this note claims no soundness bug. The finding is about the
harness: an engine that reports a decision-procedure failure and still
answers must be treated as `REJECT`, not as data, and today nothing does that.

## Mitigation used here

`opus_run_all.sh` adds three gates: any `(Error)` line emitted by the engine
fails the file; a non-zero exit fails the file; and a contract that expects
output but matches none fails rather than comparing two empty strings. The
error gate excludes lines beginning `tau> `, because the REPL echoes every
input line and a comment that merely quotes an error string would otherwise
trip it (this happened once while writing `exp5`).

Avoiding the trigger is also possible and is what `exp5` does: state the
claim as a **meet** (`A & B = 0`) rather than an entailment
(`A & B' = 0`) when time guards and bitvector columns appear together, or
keep the guarded columns in `sbf`. Both forms were checked to leave the
translator uninvolved.
