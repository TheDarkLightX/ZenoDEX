# SEC Crypto Interface Controls

Date added: 2026-04-27

Source: SEC Division of Trading and Markets, "Staff Statement Regarding Broker-Dealer Registration of Certain User Interfaces Utilized to Prepare Transactions in Crypto Asset Securities," published 2026-04-13, retrieved 2026-04-27: https://www.sec.gov/newsroom/speeches-statements/staff-statement-regarding-broker-dealer-registration-certain-user-interfaces-utilized-prepare-staff-statement-regarding-broker-dealer-registration-certain-user-interfaces-utilized

Scope note: this is an engineering launch checklist, not legal advice. The SEC source is a staff statement, not a Commission rule. The statement says it will be considered withdrawn five years from 2026-04-13 absent intervening Commission action.

## Release Gate

`SelfCustody and UserSpecifiedParams and ObjectiveUI and NoDiscretion and NoCustody -> lower broker-dealer interface risk`

Plain English: if users keep custody, specify transaction parameters, and the interface stays objective, non-discretionary, and non-custodial, broker-dealer interface risk is lower under the current SEC staff posture.

Practical consequence: a ZenoDEX UI release is blocked unless product, engineering, and legal review confirm every P0 row below.

## P0 Boundary Controls

| Control | Required ZenoDEX posture | Repo / ops evidence | Verify |
| --- | --- | --- | --- |
| Self-custodial wallet only | UI prepares transaction data for user signature; it must not custody keys, funds, securities, or stablecoins. | Wallet integrations must keep signing in the user's wallet. Backend services must not receive private keys or custody credentials. | Code review wallet paths; secret scan; test that no API accepts private keys or seed phrases. |
| User-initiated transactions | User chooses asset, side, amount, venue/pool if exposed, slippage, and submission. | UI state should expose editable transaction parameters before signing. | UI test confirms defaults can be changed before signing. |
| No investment recommendations | UI must not solicit a specific crypto asset security transaction or present personalized advice. | Static UI text gate blocks phrases such as "recommended route", "best route", "safest route", "execute trade", and "investment advice". | `python3 tools/covered_ui_lint.py --strict` and `pytest -q tests/integration/test_sec_crypto_interface_controls.py` |
| No discretionary routing | UI may display objective route data, but must not take or route orders or choose execution with operator discretion. | Route ranking must be deterministic, parameterized, and explainable as objective data. | Review route labels, route receipts, and API payloads. |
| No execution or settlement by UI provider | UI/backend must not execute or settle transactions for the user. | User wallet signs and transmits, or the chain protocol executes deterministic settlement. | End-to-end transaction flow review. |
| No financing, valuation, or trade-document processing | Do not add margin financing, independent securities valuations, negotiated terms, or off-chain trade-document handling without legal review. | Product requirements and API surface exclude these functions. | PR checklist before launch. |

## P1 Disclosure Controls

| Disclosure | Required content | Evidence to maintain | Verify |
| --- | --- | --- | --- |
| Provider role | State that the interface prepares user-specified blockchain transaction data and is not registered with or regulated by the SEC for operating the interface. | Versioned disclosure copy and release hash. | UI/legal review before release. |
| Fees | Explain fee amount, formula, payer, recipient, and whether fees vary by asset, venue, or route. | Fee config and UI copy. | Fee config diff review. |
| Conflicts | Disclose affiliate venues, token holdings, rebates, routing incentives, and use of user trading information. | Conflicts register. | Quarterly review. |
| Limitations | Disclose supported assets, venues, market data limits, unsupported jurisdictions/features, and protocol risks. | Supported-surface matrix. | Release checklist. |
| Parameters and defaults | Explain route ranking inputs, slippage, gas, deadline, and other default transaction parameters. | UI parameter copy and route-rank docs. | UI snapshot review. |
| Cybersecurity controls | Summarize controls for minimizing errors, preventing unauthorized access, and protecting against internal/external threats. | Security posture docs and CI results. | Security gate. |
| MEV / trading-info controls | Explain protections for user trading information and MEV/manipulation risk. | MEV and privacy control notes. | Security/legal review. |
| Venue integration | Name integrated venues/protocols and describe onboarding/audit criteria. | Venue registry and onboarding checklist. | Venue-list diff review. |

## Implementation Rules

- Prefer labels such as `lowest displayed fee`, `highest displayed output`, `lowest estimated slippage`, and `deterministic route by objective key`.
- Avoid labels such as `best`, `recommended`, `safest`, `guaranteed`, `approved`, or `advice` for value-moving actions.
- Route ranking must be derived from disclosed, objective parameters.
- Defaults must be editable and accompanied by plain-English risk text.
- Any affiliate fee, rebate, or routing incentive requires explicit disclosure and legal review.
- Keep records of disclosure text, fee settings, venue lists, route-ranking code version, and release hashes.

## Text Gate

Run the covered-interface wording scanner before securities-capable UI releases:

```bash
python3 tools/covered_ui_lint.py --strict
pytest -q tests/integration/test_sec_crypto_interface_controls.py
```

Current checked result:

```text
scanned_file_count = 79
finding_count = 0
```

Plain English: this scanner is not a legal conclusion. It is a regression guard
for obvious UI text that could make the interface look like it recommends,
routes, executes, settles, custodies, or receives biased order-flow economics.

## Backlog

| Priority | Item | Owner |
| --- | --- | --- |
| P0 | Add final UI disclosure panel before US-facing launch. | App / Legal |
| P0 | Add wallet-flow test proving private keys are never accepted by API routes. | App / Sec |
| P1 | Add venue onboarding/audit registry. | App / Legal |
| P1 | Add route-parameter disclosure generated from the same config used by the UI. | App |
| P2 | Add quarterly review job for source-date freshness and withdrawal date tracking. | Legal / Sec |
