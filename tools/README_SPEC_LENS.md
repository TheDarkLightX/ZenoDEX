# Spec Lens (Readable Tau Specs)

Spec Lens is a small tool that makes Tau specs easier to read **line-by-line**. It:
- Splits the `always` block into individual clauses
- Shows per-clause inputs/outputs
- Displays nearby comments
- Supports optional metadata tags in comments

## Usage

List all clauses:

```bash
python tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau
```

Focus on a single clause:

```bash
python3 tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau --focus 12
```

Explain a clause in controlled English:

```bash
python3 tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau --focus 12 --explain
```

List section tags:

```bash
python3 tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau --sections
```

Emit JSON (for UI tooling):

```bash
python3 tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau --json
```

List clauses with one-line explanations:

```bash
python3 tools/spec_lens.py src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau --explain
```

## Comment Metadata Tags (Optional)

Use these in `#` comments to give the reader richer context:

```
# @section: Canonical + Anti-Sandwich + Stability
# @input i1: order_id_a
# @output o1: canonical_ok
# @rule o1: true iff order ids strictly increasing
# @note: o1/o2/o3 should be treated as gate signals
```

Spec Lens will attach these to the relevant clause when possible.

## Notes
- The tool keeps compatibility with the formal completeness checker, which expects `iN`/`oN` stream names.
- Use comments + tags for readability, not renaming streams.
