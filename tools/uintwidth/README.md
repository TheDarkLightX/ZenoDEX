# uintwidth Tools (Internal)

This folder contains **analysis-only** tools for exploring fixed-width arithmetic
assumptions (u256/bvW) against the repo's bigint reference math.

Use cases:
- Representation intractability detection (where overflow/underflow becomes likely).
- Generating boundary test suggestions (feed into `tools/bva/`).
- Bridging proofs that assume mathematical integers into environments that do not.

This is not consensus-critical code.

## Scan Helper

Budgeted sampler that records "small-ish" overflow witnesses:

```bash
python3 tools/uintwidth/scan_cpmm_u256.py --n 20000 --seed 0 --out internal/uintwidth/cpmm_u256_scan.json
```

This output can be fed back into:
- `tools/bva/` scenarios (as specials) for systematic boundary coverage
- regression tests (when witnesses are stable and minimal enough)
