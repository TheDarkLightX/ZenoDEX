# ZenoProof Auction and Capacity Calibration V1

Status: `RESEARCH_ONLY_UNMOUNTED_UNSELECTED`

This packet calibrates a falsifiable research envelope for proof-procurement
prices, lock deadlines, default bonds, and paid-priority capacity. It does not
activate a market parameter or grant proof, scheduling, payment, slashing, or
settlement authority.

Replay:

```bash
python3 tools/check_proof_market_calibration_v1.py --write --json
python3 tools/check_proof_market_calibration_v1.py --json
```

## Game Surface

Players are proof buyers, independent provers, proving clusters, paid-priority
buyers, permissionless proof miners, beneficial-owner coalitions, and
ZenoLedger. A prover may bid, wait, lock, prove, default, or decline. Buyers may
prefund jobs or reserve a bounded capacity partition. Work size, price band,
deadline, bond, verifier profile, and policy are visible before lock. Actual
cost, congestion, failure correlation, and beneficial ownership require
authenticated observations.

ZenoLedger remains the sole payment and settlement authority. The calibration
tool only evaluates immutable values.

## Attack Query

The exact sweep searches for these failure shapes:

- a lock is admitted after too much of the advertised window has elapsed;
- a static collateral multiple excludes honest smaller provers without covering
  a named additional loss;
- colluding provers wait for the maximum price;
- a priority buyer splits wallets to multiply its reservation cap;
- paid priority starves permissionless proof mining;
- an illustrative benchmark is reported as a live clearing-price forecast.

## Bounded Model

All money uses integer micro-USD atoms. Work uses million RISC-V cycles,
throughput uses kilocycles per second, and probabilities use basis points.

```text
proving_seconds
  = ceil(mcycles * 1000 / shocked_throughput_khz)

reservation_price
  = ceil((cost_plus_margin * 10000 + failure_bps * bond) / success_bps)

required_bond
  = max(maximum_payment,
        1.25 * maximum_payment + named_delay_damage)

LockAdmitted
  -> remaining_window >= proving_seconds + publication_buffer
```

The sweep crosses four workload sizes, three exact cost/throughput shocks,
three bond rules, three maximum-price factors, three primary-window factors,
three permissionless floors, and three beneficial-owner priority caps. The
generated JSON contains every evaluated row and the exact ranking rule.

The loss-based bond funds buyer restitution and replacement procurement before
any residual penalty disposition. A collateral ceiling cannot silently reduce
the required bond. An unaffordable lock remains unavailable and uses another
prover or direct execution.

Capacity demand is aggregated by beneficial owner before applying the priority
cap. The permissionless floor is allocated first. Unused priority capacity may
spill into permissionless work after the priority reservation window.

## Source-Informed Priors

The inputs were refreshed on 2026-08-17 from primary sources:

- [Boundless performance guidance](https://docs.boundless.network/provers/performance-optimization)
  reports example system throughput near 400 kHz and a single-GPU example near
  264 kHz, while requiring representative local benchmarking.
- [Boundless prover setup](https://docs.boundless.network/provers/quick-start)
  identifies the 4090 and L4 as strong tested GPUs and recommends at least ten
  GPUs for a competitive prover.
- [Boundless auction guidance](https://docs.boundless.network/developers/tutorials/auction)
  discusses a 1.25-times lock window and five-to-ten-times collateral. It warns
  that larger requests can fail to lock when collateral is high.
- [Boundless broker configuration](https://docs.boundless.network/provers/broker)
  uses measured proving throughput, minimum deadline, maximum collateral, and
  minimum price per MCycle as admission inputs.
- [Google Cloud GPU pricing](https://cloud.google.com/products/compute/gpus-pricing)
  lists the L4 GPU component, and [Lambda pricing](https://lambda.ai/instances)
  provides additional A6000 and H100 list-price bounds.

These values bound sensitivity scenarios. They are examples and list prices.
They do not measure ZenoProof demand, the production ZRPF guest, or current
Boundless clearing prices.

## Evidence Lane

The checker performs deterministic exact enumeration and emits a canonical,
source-pinned JSON artifact. Focused tests cover arithmetic boundaries,
rejection precedence, wallet splitting, zero permissionless capacity, late
locks, static-collateral exclusion, deterministic replay, and artifact tamper.

## Promotion Boundary

The generated recommendation is an unselected research envelope. Production
selection requires signed live observations of workload cycles, bids, proving
latency, failure, reprocurement expense, utilization, and concentration. It
also requires a Rust transition, canonical codec, mounted ZenoLedger port,
runtime crash and retry evidence, and the applicable ESSO/Lean refinement
obligations.
