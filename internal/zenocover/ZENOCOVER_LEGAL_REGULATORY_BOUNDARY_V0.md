# ZenoCover Legal and Regulatory Boundary V0

Status: internal research/spec artifact. This is not legal advice, a product
approval memo, an insurance filing, or a launch authorization.

## Position

ZenoCover stays internal-only until counsel clears a specific operating model
and jurisdiction list. The current artifacts can model capped payouts, reserve
floors, claim-verifier incentives, and proof-triggered settlement failures. They
do not authorize public sale, premium collection, insurance-language marketing,
or user-facing underwriting.

The public wording should use `cover`, `risk transfer`, or `LP loss-cover replay`
only in the narrow technical sense already backed by deterministic artifacts.
Avoid public statements that ZenoCover is insurance, sells policies, underwrites
risk, charges premiums, or processes policyholder claims.

## Lowest-Risk Shape Found In The Literature

The lowest-risk shape is software-only, self-custodial, non-advisory, and
research-scoped:

- users run, compile, or interpret the software themselves;
- users directly sign their own transactions;
- the project never takes custody, controls keys, or can unilaterally move user
  value;
- the project never accepts or transmits user value and does not act as a
  broker, agent, arranger, marketplace operator, or other intermediary;
- the project does not operate or control a pooled reserve;
- the project does not collect or set premiums;
- the project does not select, recommend, route, arrange, or administer cover
  terms for a user;
- the project does not make coverage, trading, allocation, or transaction
  recommendations and does not tell users what to do with funds;
- the project does not promise a payout, adjudicate claims, or market a
  regulated risk product.

This shape is still not a legal safe harbor. It is the minimum boundary for
research artifacts while counsel evaluates whether any future production path
requires a licensed carrier, approved cover marketplace, mutual/member model,
captive, sandbox, or another regulated structure.

## Why This Is a Release Stop

The referenced market material is a useful warning. Hedera describes DeFi
insurance as including blockchain replacements for traditional policies and
insurance for blockchain-related activity, with smart-contract and parametric
payment designs. OpenCover explicitly says it avoids offering decentralized or
crypto products as "insurance" and calls the category onchain cover or onchain
risk transfer. NAIC material treats parametric disaster products as insurance
contracts and notes that, where specific parametric rules are absent, these
products generally sit in the same regulatory framework as traditional policies.
NAIC McCarran-Ferguson material also emphasizes state primacy in U.S. insurance
regulation.

Academic and supervisory sources point in the same direction. DeFi risk-transfer
papers model decentralized collateral pools, parametric triggers, basis risk,
and pooled liquidity shortfalls. Smart-contract insurance papers highlight the
oracle problem and the challenge of defining the triggering event precisely.
Parametric-supervision material reports wide jurisdictional variation, with many
authorities applying existing insurance-contract principles or existing
insurance regulations.

FinCEN's CVC guidance is useful for the custody boundary. It distinguishes
hosted wallets, where a host has independent control, from unhosted wallets,
where users control the funds. ZenoCover research artifacts must stay on the
unhosted/self-run side of that line.

Classification is a first-order design constraint. For ZenoCover, the legal
shape must be chosen before product shape.

## Research Basis

Sources reviewed for this boundary include academic, supervisory, and industry
materials:

- Felix Bekemeier, "A primer on the insurability of decentralized finance
  (DeFi)," Digital Finance, 2023:
  https://link.springer.com/article/10.1007/s42521-023-00093-x
- Matthias Nadler, Felix Bekemeier, and Fabian Schar, "DeFi Risk Transfer:
  Towards A Fully Decentralized Insurance Protocol," arXiv, 2022:
  https://arxiv.org/abs/2212.10308
- P. Zhou and Y. Zhang, "Major conundrums and possible solutions in DeFi
  insurance," International Journal of Finance & Economics, online 2025, print
  2026: https://doi.org/10.1002/ijfe.3154
- Eliza Mik, "Smart Contracts and the 'Oracle Problem' in the Context of
  InsurTech," SSRN, 2023:
  https://papers.ssrn.com/sol3/papers.cfm?abstract_id=4390271
- IAIS, "Report on FinTech Developments in the Insurance Sector," 2022:
  https://www.iais.org/uploads/2022/12/IAIS-Report-on-FinTech-developments-in-the-insurance-sector.pdf
- EIOPA, "Feedback Statement, Discussion Paper on Blockchain and Smart
  Contracts in Insurance," 2022:
  https://www.eiopa.europa.eu/system/files/2022-05/feedback_statement_-_discussion_paper_on_blockchain_and_smart_contracts_in_insurance.pdf
- NAIC, "Parametric Disaster Insurance":
  https://content.naic.org/insurance-topics/parametric-disaster-insurance
- NAIC, "McCarran-Ferguson Act":
  https://content.naic.org/insurance-topics/mccarran-ferguson-act
- FinCEN, "Application of FinCEN's Regulations to Certain Business Models
  Involving Convertible Virtual Currencies," FIN-2019-G001:
  https://www.fincen.gov/system/files/2019-05/FinCEN%20Guidance%20CVC%20FINAL%20508.pdf
- OpenCover, "Understanding Decentralized Insurance":
  https://opencover.com/learn-and-resources/understanding-decentralized-insurance/

The shared pattern is practical rather than formally safe: technical papers
explore risk-transfer protocols, but they surface actuarial, verification,
liquidity, oracle, governance, and regulation problems. Supervisory sources
treat insurance classification, solvency, market conduct, money transmission,
consumer protection, and jurisdiction as live questions. Industry wording has
also shifted toward `onchain cover` or `risk transfer` because insurance is a
regulated category.

The current ZenoCover shape therefore stays on the software-only side:

```text
self-run software
∧ self-custody
∧ direct user signature
∧ no project custody
∧ no operator pool
∧ no premium collection
∧ no broker/intermediary role
∧ no personalized recommendation
-> internal research artifact only
```

That implication is an internal release boundary. It does not prove that a
future public product is unregulated.

## Required Launch Dossier

No public or production ZenoCover offering can move past research without:

- written insurance-regulatory counsel memo;
- jurisdiction-by-jurisdiction classification and licensing map;
- approved operating model, such as licensed-carrier partnership, approved cover
  marketplace structure, mutual/member model, captive, or another counsel-cleared
  lane;
- reserve, capital, solvency, accounting, and tax treatment;
- consumer disclosure and market-conduct review;
- sanctions, AML, KYC, and wallet-screening review;
- oracle, trigger, and basis-risk disclosure;
- claims or payout dispute process;
- governance and upgrade controls;
- written go/no-go record naming the responsible reviewer and date.

If any public marketing, user sale, premium collection, or external policy
language is enabled, the machine-readable gate requires every regulated term
(`insurance`, `underwriting`, `policy`, `premium`, `policyholder`, and
`claims_adjustment`) to be marked
`approved_for_counsel_cleared_jurisdiction`. The launch candidate also has to
name an allowed operating model, currently one of: licensed-carrier partnership,
approved cover marketplace, mutual/member model, captive or sandbox, or a
regulated-entity-operated pool.

## Current Gate

The machine-readable gate is:

```bash
python3 tools/check_zenocover_regulatory_boundary.py internal/zenocover/REGULATORY_BOUNDARY_MANIFEST_V0.json --pretty
```

The manifest also machine-checks the required user-disclosure set:

- you run, compile, or interpret the software yourself;
- you directly sign transactions;
- the project never takes custody, controls keys, or tells users what to do
  with money;
- the project is not an insurance company;
- there is no policy, premium, claim adjustment, or guaranteed payout;
- the artifact is not legal, tax, or financial advice.

The report exposes a `required_boundary_fields` map. A clean internal research
manifest has every field set to `true`, including the self-run software flags,
no-custody/no-advice project flags, required source citations, required user
disclosures, and blocked regulated terms.

The public-claim scope gate also scans the ZenoCover public replay doc:

```bash
python3 tools/check_public_claim_scope.py --json
```

Current decision: internal research may continue. Public launch, user sale,
premium collection, insurance-language marketing, and underwriting claims remain
blocked. Custody, user-specific recommendations, operator-run pools, and
project-controlled claim handling are also blocked.
