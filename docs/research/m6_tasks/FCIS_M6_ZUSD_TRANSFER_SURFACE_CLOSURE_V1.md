# M6 zUSD transfer-surface closure V1

## Exact identity

```text
implementation_commit: 80b0779138d44b9161a604767480db99f5659704
implementation_tree:   195a69d6303562d4b63955b9dde3ebb5788eaab4
implementation_parent: a398c35f3f1c6c0741536bf6431f16d4e3dd630a
posture:                IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint closes the legacy zUSD token-wallet supply-action surface. It
does not complete R12, R13, or M6.

## Closed invariant

The TauToken zUSD wallet is a transfer client:

```text
zUSD token wallet action = TRANSFER

generic mint(zUSD) -> Reject(PROTOCOL_AUTHORITY_REQUIRED)
generic burn(zUSD) -> Reject(PROTOCOL_AUTHORITY_REQUIRED)
```

Collateral-backed issuance, repayment, redemption, liquidation, and their
protocol-owned supply changes remain in the zUSD monetary command family under:

```text
zenodex/zusd-monetary-kernel/v1
```

The generic TauToken constructor still supports mint and burn for non-managed
assets. The shared runtime managed-asset policy from the parent checkpoint
rejects those operations when their asset is the exact configured zUSD asset.

## Construction

- `prepare_zusd_tau_token_operation` accepts only transfer for zUSD.
- The API rejects zUSD mint and burn before Tau-node I/O.
- API action parsing rejects Boolean, whitespace, and case aliases.
- The CLI advertises only `transfer`; legacy `mint` and `burn` invocations
  receive the deterministic managed-authority rejection.
- The browser renders no mint, burn, or generic operator control.
- The browser payload hard-codes `transfer` and ignores `zusdAction` and
  `operatorPubkey` URL inputs.
- The former mint/burn browser smoke was replaced by an adversarial smoke that
  supplies `zusdAction=mint` and requires a transfer result with unchanged
  total supply.

## Evidence

The exact implementation commit passed:

```text
89 focused core/runtime/client tests passed
1 loopback browser/API/Tau adversarial smoke passed
90 total Python tests passed
focused zUSD UI source-contract test passed
ESLint passed
Vite production build passed (156 modules transformed)
Ruff check passed on seven Python files
strict mypy passed on three changed source/tool modules
py_compile passed on seven Python files
git diff --check passed
```

The retained negative cases include:

- direct zUSD mint and burn preparation;
- API mint and burn rejection before any Tau client construction;
- non-canonical action aliases;
- CLI mint compatibility rejection and transfer-only help output;
- browser removal of supply-changing controls;
- crafted `zusdAction=mint` browser input producing a transfer;
- generic runtime mint, burn, faucet, partial-batch, same-transaction repay,
  configured-asset, and sovereign-ZenoLedger cases inherited from the parent
  managed-issuance checkpoint.

The security red-flag scanner reported no high findings. It reported three
existing broad-exception sites and five existing raw-dictionary boundaries.
The implementation diff adds none of those patterns. Their boundary-hardening
debt remains explicit.

## Commands not completed

- The repository-wide Python suite was not run.
- The full UI SDK suite was stopped after it failed to terminate within the
  bounded review window; the changed focused contract, ESLint, and production
  build completed.
- `ruff format --check` reports inherited formatting debt in six touched legacy
  files; the lint gate itself passes and unrelated reformatting was excluded.
- Hosted CI, ESSO, Lean/Tau composition, deployment, crash/concurrency,
  migration, external-destination, and mounted no-bypass gates were not run.

## Residual risks and nonclaims

- Managed-asset identity and authority policy still come from ambient runtime
  configuration rather than an authenticated execution context committed by
  current state.
- The borrowing-fee debt/supply/protocol-claim identity remains open.
- Other managed asset families need closed policies and complete inventories.
- No runtime-to-formal forward simulation or deployment-complete mediation
  theorem is established.
- This checkpoint is unmounted and does not establish production authority.

## Next safest step

Move the managed-asset policy, deployment identity, and authority epoch into the
authenticated execution context and promotion subject. Then freeze and test the
current zUSD borrowing-fee accounting identity before attempting a global R13
preservation theorem.
