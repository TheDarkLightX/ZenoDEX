# M6 managed-zUSD issuance closure V1

## Exact identity

```text
implementation_commit: 6994861dfd7dc68c8ee92bd8e69e7aa20f4b730b
implementation_tree:   e046bb7ee0a5ee8de8741186b99fd67d79c07b15
implementation_parent: 30be10902bca208fa9436a3e4f6b9c7b21f68819
posture:                IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint closes one stop-the-line M6/R13 counterexample. It does not
complete L01, R12, R13, or M6.

## Counterexample

The shared Tau and sovereign ZenoLedger app transition previously accepted the
derived or configured zUSD asset through generic token `mint`, generic token
`burn`, and the testnet faucet. An authorized generic token operator could mint
zUSD without creating debt, then consume that balance through a zUSD monetary
operation in the same app transaction.

## Closed invariant

For the exact configured zUSD asset, the generic token and faucet surfaces now
enforce:

```text
GenericOperation(zUSD) is permitted only for TRANSFER.

GENERIC_MINT(zUSD) -> Reject(PROTOCOL_AUTHORITY_REQUIRED)
GENERIC_BURN(zUSD) -> Reject(PROTOCOL_AUTHORITY_REQUIRED)
FAUCET_MINT(zUSD)  -> Reject(PROTOCOL_AUTHORITY_REQUIRED)
```

The required protocol authority is the constant:

```text
zenodex/zusd-monetary-kernel/v1
```

Collateral-backed `mint_zusd`, repayment, redemption, liquidation, and
stability-pool transitions remain owned by the zUSD monetary kernel. Ordinary
zUSD transfer remains available.

## Construction

`ManagedAssetPolicyV1` is immutable typed data built from the same
`ZUSDMonetaryConfig.zusd_asset` used by monetary execution. The shared
`apply_app_tx` boundary supplies this policy to both generic token processing
and faucet processing. Each forbidden operation returns the original app-state
blob, an empty app hash, no native-balance patch, and a deterministic typed
reject message.

The same `apply_app_tx` function is consumed by the Tau app bridge and the
sovereign ZenoLedger runner. A focused ZenoLedger regression proves that a
generic zUSD mint produces a canonical rejected receipt with identical pre and
post app roots.

Two perps fixtures that had manufactured zUSD through the generic token
operator were corrected. They now obtain zUSD through collateral deposit and
monetary issuance, transfer it between traders, and retain their original perps
behavior checks.

## Evidence

The final focused gate reported:

```text
75 tests passed
Ruff passed on all seven changed files
strict mypy passed on both changed source modules
py_compile passed on all seven changed files
git diff --check passed
security red-flag scan: 0 findings in seven files
```

The retained negative scenarios include:

- generic zUSD mint from the authorized generic token operator;
- generic zUSD burn from a valid collateral-backed monetary state;
- testnet-faucet zUSD mint;
- foreign-token mint followed by forbidden zUSD mint in one token batch;
- foreign-token faucet mint followed by forbidden zUSD mint in one faucet batch;
- generic zUSD mint followed by zUSD repayment in one app transaction;
- configured, non-derived zUSD identity;
- malformed managed-zUSD identity;
- sovereign ZenoLedger rejection with exact PRE equals POST roots.

## Commands not run

- the complete repository test suite;
- hosted CI;
- ESSO dual-solver replay;
- Lean or Tau composition proof;
- production Tau or ZenoLedger deployment tests;
- crash, concurrent publication, migration, and destination tests;
- mounted no-bypass audit.

The broader ZenoLedger-node test file was sampled. Its first unrelated failure
at the implementation parent remains an `OracleState.__dict__` use against a
slots-based value in the public testnet feature-suite builder. This checkpoint
does not repair or claim that inherited failure.

## Residual risks and nonclaims

- The legacy zUSD token-wallet helper can still prepare generic mint and burn
  requests. The shared runtime rejects them, but that client surface should be
  removed or redirected to the monetary wallet API.
- Managed-asset identity still comes from ambient runtime configuration rather
  than an authenticated execution context committed by current state.
- The borrowing-fee debt/supply/protocol-claim identity remains open.
- Other protocol-managed asset families still need a closed, versioned asset
  policy and complete runtime inventory.
- No forward-simulation theorem connects this Python transition to the formal
  managed-issuance model yet.
- No production deployment, publication capability, or no-bypass result is
  established.

## Next safest step

Remove generic mint and burn from the zUSD token-wallet API and CLI, route all
zUSD supply changes through the monetary command family, and bind the complete
managed-asset policy into the authenticated execution context and promotion
subject. Then connect these retained tests to the formal/runtime refinement
matrix for managed issuance.
