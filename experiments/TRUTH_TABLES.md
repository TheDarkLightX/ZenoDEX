# Truth Table Verification for Novel DEX Specs

## Spec 39: Triangular Arbitrage Detector

### Logic Analysis
```
arbexists(pab, pbc, pac) := (pab * pbc > pac * 1000 + pac * 10) || 
                            (pab * pbc + pac * 10 < pac * 1000)
arbdir(pab, pbc, pac) := pab * pbc > pac * 1000
largearb(pab, pbc, pac) := |pab * pbc - pac * 1000| > pac * 20
```

**Meaning:**
- `o1` = arb_exists: True if indirect path (via B) differs from direct path by > 1%
- `o2` = arb_direction: True if indirect path more expensive (sell via B profitable)
- `o3` = large_arb: True if arbitrage opportunity > 2%

### Truth Table (Verified via Tau)

| Step | i1 (pAB) | i2 (pBC) | i3 (pAC) | i1*i2 | i3*1000 | Diff | o1 (arb) | o2 (dir) | o3 (large) | Expected | Match |
|------|----------|----------|----------|-------|---------|------|----------|----------|------------|----------|-------|
| 0 | 1000 | 1000 | 1000 | 1000000 | 1000000 | 0 | 0 | 0 | 0 | No arb | ✓ |
| 1 | 1000 | 1100 | 1000 | 1100000 | 1000000 | 100000 | 1 | 1 | 1 | Arb exists, indirect>direct | ✓ |
| 2 | 1000 | 1000 | 1100 | 1000000 | 1100000 | 100000 | 1 | 0 | 1 | Arb exists, direct>indirect | ✓ |

**Verification:** All outputs match expected behavior. Spec correctly detects triangular arbitrage.

---

## Spec 40: Flash Loan Attack Fingerprint

### Logic Analysis
```
liqspike(curr, prev) := curr * 2 > prev * 3       // >50% increase
liqdrain(curr, prev) := curr * 3 < prev * 2       // >33% decrease  
pricemanip(curr, prev) := |curr - prev| * 20 > prev  // >5% change
flashpattern := liqspike[t-1 vs t-2] && pricemanip[t-1 vs t-2] && liqdrain[t vs t-1]
```

**Meaning:**
- `o1` = liquidity_spike: Current liquidity >> previous
- `o2` = price_manipulation: Large price change
- `o3` = liquidity_drain: Current liquidity << previous
- `o4` = flash_attack_detected: Full 3-step pattern detected
- `o5` = reverse_flash: Reverse attack pattern

### Truth Table Test Cases

| Step | i1 (liq) | i2 (price) | o1 (spike) | o2 (manip) | o3 (drain) | o4 (flash) | Expected |
|------|----------|------------|------------|------------|------------|------------|----------|
| 0 | 1000 | 100 | - | - | - | - | Warmup |
| 1 | 2000 | 100 | 1 | 0 | 0 | - | Spike only |
| 2 | 3000 | 120 | 0 | 1 | 0 | 0 | Manip only |
| 3 | 1500 | 100 | 0 | 1 | 1 | 1 | Full pattern! |

---

## Spec 50: Intent Solver Proof

### Logic Analysis
```
intent1sat(min, actual) := actual >= min
solvervalid := intent1sat(min1, actual1) && intent2sat(min2, actual2)
paretocheck := (u1out + u2out) * 2 >= (u1in + u2in)
noextraction := (u1in + u2in) >= (u1out + u2out) && 
                surplus * 100 < (u1in + u2in)
```

**Meaning:**
- `o1` = intent1_satisfied: User1 gets >= minimum
- `o2` = intent2_satisfied: User2 gets >= minimum
- `o3` = solver_valid: Both intents satisfied
- `o4` = pareto_optimal: Total output >= half of input (efficiency)
- `o5` = no_extraction: Solver surplus < 1%

