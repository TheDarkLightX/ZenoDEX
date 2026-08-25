# Perps Margin Structural Route Composer (SHADOW)

This workspace adds a structural recursion seam between the existing perps
margin lane coordinator and the bounded global economic epoch aggregator.

The route guest:

1. decodes one canonical disclosed perps lane input;
2. deterministically re-executes that lane transition;
3. verifies one exact `Succinct` lane-coordinator receipt using the pinned child
   image ID and exact canonical journal bytes;
4. commits one canonical `RouteCompositionJournalV1` for the same command
   occurrence, profile, writer epoch, effect root, and terminal-obligation root.

The proving shell rejects `RISC0_DEV_MODE`. The receipt verifier is independent
of process environment and rejects fake, conditional, placeholder-image,
wrong-kind, wrong-journal, oversized, and noncanonical receipts before they can
be presented to the ABI verifier port.

## Exact claim

Successful real replay demonstrates this structural chain:

```text
perps module receipt
  -> perps lane receipt
  -> perps structural route receipt
  -> one-command global epoch receipt
```

Each edge resolves an exact RISC0 assumption and every emitted receipt is
`Succinct`.

## Nonclaims

- The caller currently declares the whole-economic pre-state and post-state
  roots. This guest commits those roots; it does not prove their refinement from
  a complete global state witness.
- The caller currently supplies the route release ID. A release-selected route
  registry and verifier must bind it before this receipt can carry authority.
- `RouteCompositionJournalV1` does not yet carry the CBC recursive-journal
  fields such as `verifier_set_root`, `child_verification_claims_root`, and a
  child image commitment. The child image is fixed by this guest image and
  checked by the host, which is narrower than a complete public CBC binding.
- The lane effect root is carried into the route journal. This guest does not
  prove a complete cross-lane `GlobalEconomicEffectPlanV1` projection.
- This route supports one perps deposit shape. It is not a complete perps
  lifecycle, governed route registry, or whole-economy route family.
- The workspace is `SHADOW`, unmounted, and grants no settlement, publication,
  migration, writer, or value-moving authority.
- Static tests with `RISC0_SKIP_BUILD=1` use placeholder method constants and do
  not constitute cryptographic proof evidence.

## Replay

Cheap fail-closed and deterministic checks:

```bash
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
```

Real four-receipt composition, intended for the proof benchmark host:

```bash
cargo test --locked -p zenodex-perps-margin-route-composer-risc0-host \
  --test real_composition -- --ignored --nocapture
```

Record wall time, peak resident memory, accelerator utilization, machine type,
price, source revision, toolchain, image IDs, and receipt hashes before using a
run as fee or capacity evidence.
