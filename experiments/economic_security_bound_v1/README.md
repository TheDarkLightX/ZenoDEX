# Application economic-security bound (resilience gap #2)

Turns the resilience report's **"fees-in-pool are recapturable"** insight from an
intuition into an exact, integer, falsifiable bound. (`experiments/economic_security_bound_v1/`,
7 tests, gitignored prototype.)

## The model

An attacker extracts value `V`. They pay a protocol fee `F` on the notional they
route, plus non-recapturable `gas` and locked-`collateral`/slashing cost. But an
attacker who also holds LP share `alpha` of the pool the fee accrues to **recaptures
`alpha·F`** — so the fee's real deterrence is only the non-recapturable remainder
`F·(1 - alpha)`. The attack is profitable iff

    V  >  F·(1 - alpha)  +  gas  +  collateral

## The results (numbers, not intuitions)

1. **Fee-deterrence efficiency = `1 - alpha`.** A nominal fee deters only `(1-alpha)`
   of its face value: 100% at `alpha=0`, **10% at `alpha=0.9`, 0% at `alpha=1`** (full
   recapture). `fee_deterrence_efficiency_bps`.

2. **The recapture counterexample.** A fee *larger than V* can still fail: fee `1000`
   vs `V=500` looks safe, but a 90%-LP whale recaptures `900`, leaving `100` of real
   deterrence → the attack nets `+400`. So "the fee exceeds the prize" is **not** a
   safety argument. (`test_whale_recaptures_fee_so_high_fee_still_fails`.)

3. **Robust-deterrence theorem (tight).** An attack of value `V` is deterred for
   **every** LP share `alpha ∈ [0,1]`  **iff**  `gas + collateral ≥ V`. Proof: the
   fee contributes `F·(1-alpha) ≥ 0`, which is `0` at `alpha=1`, so the worst case
   forces `gas+collateral ≥ V`; and that suffices for all `alpha`. The bound is
   **tight** (the `alpha=1` witness recaptures the fee entirely). Verified
   **exhaustively** in `test_robust_theorem_exactly_characterizes_bruteforce_over_alpha`:
   closed form `==` enumeration over **every** `alpha` in `[0, 10000]` (not sampled).

4. **ZenoDEX 30-bps number.** At the 30-bps swap fee, a 90%-LP whale routing a
   `1_000_000`-unit manipulation pays a nominal fee of `3000` but eats only **`300`**
   of real deterrence (3 bps effective). Any `V > 300` (net of gas/collateral) pays
   off, despite the `3000` fee *looking* 10× larger. (`test_zenodex_30bps_concrete_number`.)

## Implication for ZenoDEX

**Do not price deterrence in protocol fees** — they are recapturable down to zero by
a large LP. Size **non-recapturable** cost (gas + locked collateral + slashing) at
`≥ V_attack`, treating the fee as zero deterrence in the worst case. This is the
consensus-grade form of the perp-incentives insight (#2: "fees in pool are
recapturable") and the economic (Level-3) version of the security hierarchy.

`V_attack` sources to instantiate per surface: settlement-ordering manipulation
(**now de-grinded** by the neutral tie-break — `b02adbda`), oracle/TWAP push,
CoW-netting LP fee+spread capture (a known mechanism-design deviation), perps
funding/ADL timing. Consensus-corruption `V`/cost itself is **Tau's** (this bound is
the *application* layer).

## Honest scope

This is the **framework + the tight bound**, not a full audit: it does not by itself
enumerate every surface's concrete `V_attack` or ZenoDEX's exact gas/collateral
schedule (gas economics under Tau settlement in particular need their own grounding).
It gives the law every surface must satisfy and a checkable predicate
(`deters_for_all_alpha`) to test each one against once its `V_attack` is quantified.
