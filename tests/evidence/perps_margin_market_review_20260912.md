# Full perps market: scoped review

Implementation subject: `7386fa2ea2488999aa453b701e3b666e32ee2d85`. [Evidence and commands](perps_margin_market_v1_20260912.json).

Astra independently reviewed the complete model against both runtime admission
contracts and accepted Lean SHA-256
`1598aa39d0a27e514d88595f7b06b072722c512aab3caf135d9e9a3282a1c743`.
Root implemented the proof and final theorem consumers; Luna implemented the
bounded test extension. A Daybreak follow-up hit the harness thread limit and
produced no verdict. No external Claude/Fable job ran.

The reviewed theorem derives its selected account, count and successor list.
Strict order, all-key sibling identity, capacity, asymmetric i128 limits,
separate gross bounds/equality, account shape and market envelope are preserved.
The standalone post-account lemma requires an open account; the public theorem
derives this from the actual prepare guard. It assumes only pre-admission.
The history theorem permits commands targeting other accounts after closure.

Final fresh gate: **10 passed in 61.52 seconds**, covering 43 static cases,
19 history attempts, seven executable single-site mutants, 12 exact theorem
consumer types/axiom audits and concrete empty/64-row/i128-min admission proofs.
The harness SHA-256 is
`de6dd16554ec9994d87b6d440849f359336d1fa25c85656ccb6240b7f60021d5`.
Astra reviewed source and parent results; it did not independently build.

Conditional scoring requirements are satisfied. Only margin deposit/withdraw
preservation .35→.45 and refinement .40→.45, plus W09 .24/.32/.42→.25/.33/.43,
change. Semantics .50, uncertainty H and all other rows remain inherited.
The unchanged calculator gives formal **21.219%→21.297%** (+.078 points),
V3 **24.069%→24.169%** (+.100 points). The review's provisional 21.298%
used rounded aggregate arithmetic; 21.297% is the validated stored-row result.
These are planning estimates, not safety qualification or time estimates.

String/root syntax, schema decoding, canonical bytes, effects/journals,
authentication and universal Python/Rust refinement remain outside the universal
proof. Admission does not establish initial solvency. No lane, route or release
closes; value-safety qualification remains 0/12.
