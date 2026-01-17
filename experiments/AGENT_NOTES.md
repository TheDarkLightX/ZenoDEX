# Tau Language: Agent Notes

A guide for AI agents working with Tau Language specs. This documents quirks, gotchas, and patterns that work.

---

## Critical Syntax Rules

### 1. Single-Line Definitions Only

Tau **cannot** parse multi-line predicate definitions. This will fail:

```tau
# BROKEN - multi-line
my_predicate(a : bv[16], b : bv[16]) := 
    (a > b) || (a = b).
```

This works:

```tau
# CORRECT - single line
my_predicate(a : bv[16], b : bv[16]) := (a > b) || (a = b).
```

### 2. Typed Parameters Are Mandatory

Predicates **must** have typed parameters. Untyped params cause "Unresolved function or predicate symbol" errors.

```tau
# BROKEN - untyped params
is_less(a, b) := a < b.

# CORRECT - typed params  
is_less(a : bv[16], b : bv[16]) := a < b.
```

### 3. Hex Constants Require Type Annotations

Bitvector constants need explicit type:

```tau
# BROKEN
x > #x0000

# CORRECT
x > { #x0000 }:bv[16]
```

### 4. Boolean Output Uses sbf Type

For true/false outputs, use `sbf` (Simple Boolean Function):

```tau
always (o1[t]:sbf = 1:sbf <-> some_predicate(...)).
```

- `1:sbf` = true
- `0:sbf` = false

### 5. Stream Variables Need Type Annotations in `always`

```tau
# Input streams: i1, i2, i3, ...
# Output streams: o1, o2, o3, ...

always (o1[t]:sbf = 1:sbf <-> i1[t]:bv[16] > { #x0000 }:bv[16]).
```

---

## Common Patterns

### Conditional Operators (Ternary)

Ternary `? :` is reliable inside `always` expressions, but can fail inside predicate definitions in this build. Prefer expanding to boolean cases instead of defining `max/min` helpers with ternaries.

### REPL Predicate Parameters

In REPL, predicate parameter names that include digits can trigger unresolved symbol errors. Stick to simple names (`a`, `b`, `x`, `y`, `z`) for predicate parameters.

### Temporal Warmup and File Inputs

When `t-1` is used, REPL often consumes the **first input line at step 1**, leaving step 0 as warmup with no input. Align test traces so the first meaningful value is on line 1 of the input file.

### Bitvector Comparison

```tau
is_positive(x : bv[16]) := x > { #x0000 }:bv[16].
is_gte(a : bv[16], b : bv[16]) := a >= b.
```

### 32-bit Values Using Hi/Lo Pairs

Tau's default bv width is 16 bits. For larger integers, use pairs:

```tau
# 32-bit positive check
is_positive_32(hi : bv[16], lo : bv[16]) := (hi > { #x0000 }:bv[16]) || (hi = { #x0000 }:bv[16] && lo > { #x0000 }:bv[16]).

# 32-bit comparison: (hi1:lo1) >= (hi2:lo2)
gte_32(hi1 : bv[16], lo1 : bv[16], hi2 : bv[16], lo2 : bv[16]) := (hi1 > hi2) || (hi1 = hi2 && lo1 >= lo2).
```

### 64-bit Bitvectors

For IDs and hashes, use `bv[64]`:

```tau
is_less_64(a : bv[64], b : bv[64]) := a < b.
```

### Canonical Batching (DEX Pattern)

```tau
is_canonical_order(a_id : bv[64], b_id : bv[64], first : bv[64], second : bv[64]) := (a_id <= b_id && first = a_id && second = b_id) || (b_id < a_id && first = b_id && second = a_id).
```

---

## CLI Flags That Matter

```bash
./tau spec.tau --severity error --charvar false -x </dev/null
```

| Flag | Purpose |
|------|---------|
| `--severity error` | Only show errors, suppress info/debug |
| `--charvar false` | Allow descriptive variable names (not just single chars) |
| `-x` | Enable experimental features (needed for specs) |
| `</dev/null` | Don't wait for interactive input |

---

## Debugging Failed Specs

### "Unresolved function or predicate symbol"

**Cause**: Predicate called with untyped parameters or predicate not defined.

**Fix**: Ensure all predicates have typed params in definition:
```tau
# Definition
foo(x : bv[16]) := x > { #x0000 }:bv[16].

# Usage in always
always (o1[t]:sbf = 1:sbf <-> foo(i1[t]:bv[16])).
```

### "Tau specification is unsat"

**Cause**: The spec is logically unsatisfiable or has syntax issues that cascade.

**Fix**: Check for:
1. Unresolved predicates (see above)
2. Type mismatches
3. Contradictory constraints

### "Syntax Error: Unexpected end of file"

**Cause**: Multi-line definition or missing closing paren/period.

**Fix**: Put entire definition on one line, ensure `.` at end.

### Spec Runs Forever

**Not an error!** If your spec compiles and starts producing output like:
```
o1[0]:sbf := 1
o1[1]:sbf := 1
...
```
It's working - the interpreter is executing. Use `timeout 3` to test compilation.

---

## Template: Minimal Working Spec

```tau
# Predicate with typed params (SINGLE LINE)
my_check(value : bv[16]) := value > { #x0000 }:bv[16].

# Main constraint
always (o1[t]:sbf = 1:sbf <-> my_check(i1[t]:bv[16])).
```

## Template: Multi-Input Spec

```tau
# Multiple predicates
fee_valid(fee : bv[16]) := (fee >= { #x0000 }:bv[16]) && (fee <= { #x2710 }:bv[16]).
amount_positive(hi : bv[16], lo : bv[16]) := (hi > { #x0000 }:bv[16]) || (hi = { #x0000 }:bv[16] && lo > { #x0000 }:bv[16]).

# Combine predicates
swap_ok(fee : bv[16], amt_hi : bv[16], amt_lo : bv[16]) := fee_valid(fee) && amount_positive(amt_hi, amt_lo).

# Main constraint with multiple inputs
always (o1[t]:sbf = 1:sbf <-> swap_ok(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16])).
```

---

## What NOT to Do

1. **Don't use `in console` / `out console` declarations** - They're for interactive mode, not spec validation
2. **Don't end spec with just `T.`** - Must have proper `always` statement
3. **Don't use multi-line definitions** - Tau parser doesn't handle them
4. **Don't omit types on predicate params** - Causes unresolved symbol errors
5. **Don't mix bv widths without explicit casts** - `bv[16]` and `bv[64]` are different types

---

## Operators Reference

| Operator | Meaning |
|----------|---------|
| `&&` | Logical AND |
| `\|\|` | Logical OR |
| `!` | Logical NOT |
| `<->` | Biconditional (iff) |
| `->` | Implication |
| `=` | Equality |
| `!=` | Inequality |
| `>`, `>=`, `<`, `<=` | Comparisons (unsigned for bv) |
| `:=` | Definition |
| `always` | Temporal: true at all times |
| `[t]` | Current time step |
| `[t-1]` | Previous time step |

---

## Testing Workflow

```bash
# 1. Quick syntax check
timeout 3 ./external/tau-lang/build-Release/tau my_spec.tau --severity error --charvar false -x </dev/null

# 2. Check all specs in a folder
for spec in folder/*.tau; do
  echo -n "$(basename $spec)... "
  if timeout 3 ./external/tau-lang/build-Release/tau "$spec" --severity error --charvar false -x </dev/null >/dev/null 2>&1; then
    echo "OK"
  else
    echo "FAIL"
  fi
done
```

---

## Resources

- **Demos**: `external/tau-lang/demos/` has working examples
- **Grammar**: `external/tau-lang/parser/tau.tgf` is the formal grammar
- **Working specs**: `experiments/*.tau` in this folder

---

---

## Advanced Patterns (from Memory Management Tutorial)

### `set charvar off` Directive

Use at file start instead of CLI flag:

```tau
set charvar off

# Now you can use descriptive variable names
```

### `run always` vs `always`

- **`always (...).`** - Spec mode (validation, exits after check)
- **`run always (...)`** - Interactive mode (continuous execution, accepts inputs)

```tau
# Spec mode (what we used in experiments)
always (o1[t]:sbf = 1:sbf <-> condition).

# Interactive mode (runs continuously)
run always (
  o1[t] = i1[t] &&
  o2[t] = i2[t]
)
```

**CRITICAL**: Multi-line `run always` with embedded `#` comments can fail parsing!
The tutorial example works because comments are OUTSIDE the `run always (...)` block.
For safety, put complex `run always` on a single line or keep comments outside.

### Temporal State - Previous Values

Access values from previous timestep with `[t-1]`:

```tau
# Store previous value
(o0old[t] : bv[16] = i0total[t-1]) &&

# Calculate trend (current - previous)
(o1trend[t] : bv[16] = i0total[t] - o0old[t])
```

### Ternary Conditionals

For multi-tier decision logic:

```tau
# Simple ternary
(condition) ? (true_result) : (false_result)

# Nested ternary (3 tiers)
((i0total[t] > { #x2C00 } : bv[16])     # Crisis > 11GB
 ? (o2limit[t] = { #x00 } : bv[8])       # → limit=0
 
 : (i0total[t] > { #x2400 } : bv[16])   # Warning > 9GB
 ? (o2limit[t] = { #x32 } : bv[8])       # → limit=50
 
 : (o2limit[t] = { #x64 } : bv[8]))      # Normal → limit=100
```

### Inline Type Declarations

Declare types inline within formulas:

```tau
# Type declaration + constraint together
(i0total[t] : bv[16] & { #xFFFF } : bv[16] = i0total[t]) &&
(o0old[t] : bv[16] = i0total[t-1])
```

### Named Input/Output Streams

Use descriptive names instead of just numbers:

```tau
# Instead of i1, i2, i3...
i0total[t]    # Total memory
i1rooms[t]    # Room count
i2rate[t]     # Request rate

# Instead of o1, o2, o3...
o0old[t]      # Previous memory
o1trend[t]    # Memory trend
o2limit[t]    # Room limit
o3throttle[t] # Throttle flag
```

### Multi-Output Specifications

Combine multiple outputs with `&&`:

```tau
run always (
  (o0old[t] : bv[16] = i0total[t-1]) &&
  (o1trend[t] : bv[16] = i0total[t] - o0old[t]) &&
  (o2limit[t] : bv[8] = some_logic) &&
  (o3throttle[t] : bv[8] = other_logic)
)
```

### Bitvector Arithmetic

Tau supports arithmetic on bitvectors:

```tau
# Subtraction (unsigned, wraps on underflow)
o1trend[t] = i0total[t] - o0old[t]

# Comparison
i0total[t] > { #x2C00 } : bv[16]
```

### Pattern: Three-Tier Protection

For resource management with pre-emptive action:

```tau
# CRISIS:  > threshold_high → emergency action
# WARNING: > threshold_low  → limited action  
# NORMAL:  otherwise        → full capacity

((value > HIGH_THRESHOLD)
 ? (crisis_response)
 : (value > LOW_THRESHOLD)
 ? (warning_response)
 : (normal_response))
```

---

## Interactive Testing

For specs with `run always`, provide inputs interactively:

```bash
# Run in interactive mode
./external/tau-lang/build-Release/tau my_spec.tau --charvar false

# Then enter values when prompted:
# i0total[0]:bv[16] := 5120
# i0total[1]:bv[16] := 6144
# etc.
```

---

*Created by Cascade while debugging DEX specs. Last updated: 2024-12*
