# Tau Language Notes (TauSwap)

This file captures actionable observations about Tau Language syntax and semantics, based on:
- `external/tau-lang/parser/tau.tgf` (grammar)
- `external/tau-lang/README.md` (language reference)
- `external/tau-lang/docs/Theories-and-Applications-of-Boolean-Algebras-0.25.pdf` (Ohad Asor, draft)

## Core Syntax & Types
- A Tau spec is a `wff` ending with `.`; input/output streams are declared via `name : type = in/out console.`
- Boolean connectives: `&&`, `||`, `!`, `->`, `<->`, plus `always` / `sometimes` temporal operators.
- Base types include `sbf` (simple Boolean functions), `tau` (specs as constants), and bitvectors `bv[N]`.
- Typed constants: `{ #x1f }:bv[8]`, `{ #b0001 }:bv[4]`, `{ (x & y) }:sbf`.
- References can now be typed directly in the grammar, e.g. `f(x):bv[16]` (parser change in tau-lang `main` as of Dec 19, 2025).
- Typed elements use `:` (e.g., `x:sbf`, `o1[t]:bv[16]`). If no type is provided, `tau` is assumed.
- `bv` defaults to width 16 when not explicitly specified or inferred otherwise.

## Streams & Temporal Model
- Streams are indexed by time (`[t]`, `[t-1]`, `[k]`), enabling temporal constraints and state-machine style specs.
- Input and output streams are time-compatible sequences; specs constrain relationships across time steps.

## Bitvectors & Arithmetic
- Bitvector arithmetic is *modular* (`+`, `-`, `*`, `/`, `%`) with bitwise ops (`!&`, `!|`, `!^`, `<<`, `>>`).
- Precedence: `*` > `/` > `%` > `+` > `-` > `!&` > `!|` > `!^` > `<<` > `>>`.
- Current TauSwap constraints assume a 32-bit ceiling; amounts are represented as `(hi, lo)` 16-bit limbs.

## Recurrence Relations
- Functions/predicates can be defined by recurrence with indexed calls (e.g., `f[n] := f[n-1](...)`).
- The index on the RHS cannot exceed the LHS; no circular dependency across definitions.
- Fixpoints are supported by omitting the index during a call, yielding a normalization-time fixpoint.

## Tables & Pointwise Revision (From Asor’s Monograph)
- The monograph introduces *tables* as functions `2^n -> B` with operations like `set`, `select`, and `common`.
- It also describes *pointwise revision* for updates: new specs prefer prior behavior when compatible.
- These constructs are not visible in the current parser grammar, so treat them as conceptual/future features.

## Recent Grammar Updates (tau-lang `main`, Dec 19, 2025)
- `ref` now accepts an optional type annotation (`ref_args [typed]`), enabling `sym(args):bv[16]` style uses.
- Binary bitvector operators restrict the right operand to avoid ambiguity (left-associative parsing for `<<`, `>>`, `-`, `%`, `/`, `!&`, `!|`, `!^`).
- REPL history store accepts `ref` entries, not only `wff`/`bf`.

## Type Inference (Recent README Emphasis)
- Types are inferred via scoped unification; types inferred inside a scope do not leak outside it.
- Recurrence relations can be typed as functions (`f(x):tau := ...`) or predicates with per-arg types (`p(x:sbf, y:tau) := ...`).
- Quantified variables inherit types from their surrounding formulas if not explicitly typed.

## Tau Net Alpha Notes (tau.net)
- Testnet Alpha uses **extralogical APIs** to cover functionality not yet expressible in Tau; user rules still remain in Tau.
- Transactions are logical tuples of Boolean algebra elements, and blocks aggregate them into tables.
- Coin transfers are modeled as **local deltas**, summed into a **global delta**, then applied to a balances table; blocks are rejected if any balance becomes negative.

**Implication:** model DEX changes as local deltas aggregated into a global delta, and provide external witnesses for hashing, crypto, 256-bit math, and sorting.

## Implications for TauSwap Specs
- Prefer small, monotone constraints with helper predicates to avoid BDD blow-ups.
- Encode 256-bit arithmetic in Python and validate *relationships* in Tau (bounds, non-negativity, ordering, one-hot).
- Use fixed, explicit witnesses (e.g., `balance_mid`) to validate multi-step arithmetic under 32-bit limbs.
- Keep Tau validation narrow and deterministic; move hashing, signatures, division, and sqrt outside Tau.
