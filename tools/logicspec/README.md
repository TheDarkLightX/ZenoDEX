# LogicSpec: Standard Logic Notation to Tau-Style Output

LogicSpec is an intermediate language that uses standard mathematical logic notation and generates Tau-style output. This makes formal specifications accessible to:

- **LLMs** that are trained on standard logic notation (∧, ∨, →, □)
- **Mathematicians** familiar with formal logic symbols
- **Developers** who want to write specs without learning Tau syntax
- **Auditors** who can read standard logic but not DSL-specific formats

## Important Limitation

**This transpiler generates Tau-style output based on pattern-matching existing `.tau` files.**
It does NOT have access to the official Tau grammar (`tau.tgf`) and therefore:

- Output is **best-effort** based on observed patterns
- **No guarantee of syntactic validity** without validation by actual Tau tooling
- Users must validate output with `tau` compiler after generation

To properly validate generated output, you need:
1. Tau Language from https://github.com/IDNI/tau-lang
2. The `tau.tgf` grammar file (not distributed here due to licensing)
3. Run: `tau <generated.tau>` to check for syntax errors

## Motivation (SPEAC Approach)

Based on ["Synthetic Programming Elicitation for Text-to-Code"](https://arxiv.org/abs/2406.03636), this transpiler implements the SPEAC pattern:

1. **Elicitation**: Use a language LLMs already understand (standard logic notation)
2. **Compilation**: Generate output targeting the low-resource language syntax

This reduces syntax errors when AI systems write formal specifications, but **final validation requires the actual Tau toolchain**.

## Quick Example

**LogicSpec input** (`swap.lspec`):
```
spec SwapValidity {
  inputs {
    reserve_in: u32
    reserve_out: u32
    amount_out: u32
  }

  outputs {
    swap_valid: bool
  }

  define positive(x: u32) := x > 0

  invariant main {
    □ (swap_valid ↔
        positive(reserve_in) ∧
        positive(reserve_out) ∧
        amount_out ≤ reserve_out)
  }
}
```

**Tau output** (`swap.tau`):
```tau
set charvar off

positive(x : bv[32]) := (x > { #x00000000 }:bv[32]).

always
  (o1[t]:sbf <-> positive(i1[t]:bv[32]) && positive(i2[t]:bv[32]) && (i3[t]:bv[32] <= i2[t]:bv[32]))
```

## Installation & Usage

```bash
# No installation needed - just Python 3.8+
cd tools/logicspec

# Compile a spec
python3 -m logicspec compile input.lspec -o output.tau

# Check syntax only
python3 -m logicspec check input.lspec

# Show symbol reference
python3 -m logicspec symbols

# Print version
python3 -m logicspec version
```

## Symbol Reference

| LogicSpec | Meaning | Tau Output |
|-----------|---------|------------|
| `∧` or `and` | Conjunction | `&&` |
| `∨` or `or` | Disjunction | `\|\|` |
| `¬` or `not` | Negation | `!` |
| `→` or `implies` | Implication | `->` |
| `↔` or `iff` | Biconditional | `<->` |
| `□` or `always` | Temporal always | `always` |
| `◇` or `eventually` | Temporal eventually | `eventually` |
| `∀` or `forall` | Universal quantifier | (expanded) |
| `∃` or `exists` | Existential quantifier | (expanded) |
| `≤` or `<=` | Less or equal | `<=` |
| `≥` or `>=` | Greater or equal | `>=` |
| `≠` or `!=` | Not equal | `!=` |
| `·` or `*` | Multiplication | `*` |

## Type System

| LogicSpec Type | Meaning | Tau Type |
|----------------|---------|----------|
| `bool` | Boolean flag | `sbf` |
| `u16` | 16-bit unsigned | `bv[16]` |
| `u32` | 32-bit unsigned | `bv[32]` |
| `u64` | 64-bit unsigned | `bv[64]` |

## Language Grammar

```
spec       := 'spec' IDENT '{' sections '}'
sections   := (inputs | outputs | define | invariant)*
inputs     := 'inputs' '{' param* '}'
outputs    := 'outputs' '{' param* '}'
param      := IDENT ':' type
type       := 'bool' | 'u16' | 'u32' | 'u64'
define     := 'define' IDENT '(' params ')' ':=' expr
invariant  := 'invariant' IDENT '{' expr '}'
expr       := temporal | quantifier | binary | unary | primary
temporal   := ('□' | '◇' | '○') expr
quantifier := ('∀' | '∃') IDENT ':' type expr
binary     := expr op expr
unary      := ('¬' | '-') expr
primary    := IDENT | literal | call | '(' expr ')'
```

## Examples

See `examples/` directory:
- `cpmm_v1.lspec` - CPMM swap validity
- `flash_loan_guard_v1.lspec` - Flash loan attack prevention
- `rate_limiter_v1.lspec` - Transaction rate limiting

## Running Tests

```bash
python3 -m pytest tools/logicspec/tests/ -v
# Or standalone:
python3 tools/logicspec/tests/test_transpiler.py
```

## License

This transpiler is MIT licensed (see LICENSE file).

**IMPORTANT**: This tool only generates Tau Language syntax as text.
To execute the generated `.tau` files, you must obtain Tau Language
separately from https://github.com/IDNI/tau-lang and accept their license terms.

This transpiler does not include or distribute any Tau Language source code,
binaries, grammar files, or other copyrighted materials.
