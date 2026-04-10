# Confidential Features Beta Runbook

This runbook is the minimum operator surface for running the confidential feature set as a beta on `main`.

## Scope

This beta covers:
- TEE-backed confidential execution receipts
- sealed-bid commit/reveal auction flow
- non-reveal bond accounting
- public status reporting for the feature posture

It does not claim:
- fully encrypted on-chain state
- GA support guarantees
- perfect economic tuning for every market

## Recommended beta posture

- Feature stage: `beta`
- TEE enabled: `true`
- Sealed bids enabled: `true`
- Sealed bids default: `false`
- Public path remains the default for ordinary swaps

## Environment

- `CONFIDENTIAL_FEATURE_STAGE=beta`
- `CONFIDENTIAL_TEE_ENABLED=true`
- `CONFIDENTIAL_SEALED_BID_ENABLED=true`
- `CONFIDENTIAL_SEALED_BID_DEFAULT=false`
- `CONFIDENTIAL_ATTESTATION_EPOCH_LENGTH_S=60`
- `CONFIDENTIAL_MAX_ATTESTATION_AGE_EPOCHS=2`
- `CONFIDENTIAL_APPROVED_MEASUREMENTS=<csv>`
- `CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE=<json or newline file>`
- `CONFIDENTIAL_OPERATOR_CONTACT=confidential@your-domain`

## Public status endpoint

The API exposes:
- `GET /api/confidential/status`

Use it to confirm:
- feature stage
- whether TEE and sealed bids are enabled
- whether sealed bids are default-on
- approved measurement count
- provider families present in the allowlist

## Launch checklist

1. Confirm measurement allowlist is loaded and non-empty for live TEE providers.
2. Confirm stale-attestation window matches operator policy.
3. Confirm sealed bids are opt-in and clearly labeled beta in UI/docs.
4. Confirm operator contact is set to a real monitored address or alias.
5. Run:
   - `python3 tools/sealed_bid_disaster_catalog.py`
   - run the non-public sealed-bid evaluation workflow for:
     - private-state execution
     - non-reveal bond accounting
   - `bash tools/prod_gate.sh`

## Alerts

Alert on:
- unapproved TEE measurement attempts
- stale attestation spikes
- accounting guard failures for confidential receipts
- slash-rate spikes in sealed-bid auctions
- repeated no-reveal auctions for the same market cohort

## User support policy

Support response should tell users:
- when the confidential path is appropriate
- when the public path is better
- that the feature is beta and opt-in
- that sealed-bid auctions may slash non-reveal participants

Fallback:
- if confidential execution is degraded, route users to the public path rather than partially executing a broken private path
