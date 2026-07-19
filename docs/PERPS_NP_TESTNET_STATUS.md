# N-Party Perps — Retired Production Surface

> **Status: research-only and excluded from every production deployment.**
> This document records a retired fake-value experiment; it is not a testnet or
> production capability claim.

The open N-party clearinghouse experiment is not recognized by the production
perpetuals engine. In particular, production has no operation version, market
prefix, initialization action, transition dispatch, configuration switch, or
import of the research implementation.

## Enforced boundary

- `src/integration/perp_engine.py` admits only the isolated, fixed two-party,
  and fixed three-party production versions. Retired operation payloads are
  rejected as an invalid version before dispatch.
- `src/integration/dex_snapshot.py` neither encodes nor decodes the retired
  market representation. A persisted retired market fails closed as an
  unsupported market kind.
- `src/integration/perps_wallet_api.py` raises an unsupported-state error rather
  than returning a sparse market summary.
- The production UI accepts only `clearinghouse_2p_v1` and `isolated_v2` wallet
  summaries. Source and emitted-bundle gates reject retired N-party markers.
- Production container assembly removes `src/nonproduction` before source is
  copied into the final image, and the artifact checker rejects the directory,
  imports from it, and all retired adapter symbols.

Historical frozen state types and validation code remain in `src/core` only so
old research evidence can still be inspected offline. They provide no
production transition path. The standalone matching and clearinghouse research
implementation lives under `src/nonproduction` and its tests under
`tests/nonproduction`.

## Research evidence

The RISC0 experiment under `zk/state_proof_risc0/` and its offline proof tools
remain research artifacts. Their existence does not authorize runtime
admission, custody, settlement, or a production security claim.

Any future promotion requires a new versioned design and an explicit review of
authorization, Oracle authority, conservation, insolvency/loss allocation,
state refinement, deployment-profile inclusion, and same-commit release
evidence. It must not re-enable this retired adapter.
