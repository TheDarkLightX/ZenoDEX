# PulseX Buy-and-Burn Comparative Audit

Date: 2026-08-28

Status: research-only comparative review. This note grants no production,
settlement, release, migration, writer, or value-moving authority.

## Question

Which PulseX buy-and-burn design choices should ZenoDEX retain, and which
failure modes should ZenoDEX make unrepresentable?

## Source boundary

The strongest primary artifact located for this review is the verified PulseX
contract source served by the PulseChain explorer. No official PulseX smart
contract source repository was located. Explorer labels and verified source are
useful contract evidence. They do not prove that a reported exploit succeeded,
identify every deployed proxy, or quantify any loss.

Reviewed artifacts:

- [PulseChainStats report](https://x.com/PulseChainStats/status/2093382255515427256)
- [PulseX official site](https://pulsex.com/)
- [verified shared buy-and-burn implementation](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x5F02FbB0f8D924E9b67c7DAae523FF51175699f9)
- [verified PulseX V2 factory](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x29eA7545DEf87022BAdc76323F373EA1e707C523)
- [V1 authorization-policy transaction](https://api.scan.pulsechain.com/api/v2/transactions/0xe6f072b485089d2a0d55c6743cbe1ab6b632c601f29e9608a1aefdce7e89a093)
- [V2 authorization-policy transaction](https://api.scan.pulsechain.com/api/v2/transactions/0x5073c4186a139c05375d9aefe3afc937c41e530e077ca1590251a4da92f53d86)

## Verified behavior

The reviewed implementation accepts caller-supplied `tokens0[]` and
`tokens1[]` in `convertLps`. Its `_getValidPair` check derives the pair from the
configured factory, which prevents a caller from supplying an arbitrary pair
contract. Pair creation through an AMM factory is permissionless, so factory
membership alone does not establish that a pair is an approved protocol
inventory source.

The 2026-08-28 transactions changed the authorization policy from broad caller
access to an authorized-caller policy. The reviewed implementation bytecode did
not need to change for that configuration update. The selected authorized
caller still chooses the token arrays. The selection hazard therefore remains
behind the authorization boundary and would return if broad caller access were
restored.

The reviewed path sends pair assets directly to the buy-and-burn contract,
keeps purchased output under contract control, uses checked arithmetic and a
reentrancy guard, and accounts for transfer-tax behavior. These choices reduce
router-allowance, recipient-substitution, and partial-execution surfaces.

The reviewed conversion path does not bind a minimum output, finalized Oracle
or TWAP occurrence, maximum price deviation, or maximum execution impact. Its
reserve-ratio slippage setting bounds input relative to reserves. It does not
provide an output-price guarantee.

The reviewed code also permits a zero bounty setting. In the inspected control
flow, the amount selected for burning is assigned inside the positive-bounty
branch. A zero bounty can therefore leave purchased PLSX unburned. This is a
dormant configuration-dependent code defect in the reviewed implementation,
not evidence that the current deployed configuration selected zero.

## What PulseX did well

1. Pair addresses are derived from a configured factory rather than accepted as
   arbitrary contracts.
2. Assets move directly from the pair into the conversion contract without a
   broad external-router allowance.
3. Purchased output remains contract-controlled until the burn step.
4. Conversion and burn execute atomically with reentrancy protection and
   checked arithmetic.
5. Transfer-tax behavior is handled from observed balances instead of trusting
   nominal transfer amounts.
6. Burning reduces token supply rather than transferring tokens to an ordinary
   externally controlled address.

## Failure families ZenoDEX must close

### PBAB-RI-01: caller-selected inventory execution

Attack query:

```text
Can a trigger caller, operator, relayer, or compromised client select a pool,
pair, inventory object, route, bridge, recipient, or burn destination that the
active economic profile did not select?
```

Required closure:

- the active profile commits one closed buyback execution policy;
- the policy binds pool identity, complete pool definition, quote asset, ZDEX
  asset, route release, module releases, and exact port schemas;
- the purchase guest authenticates the selected pool and its prestate;
- the route composer rejects every substituted resource with empty effects;
- permissionless callers may trigger an eligible command and cannot choose its
  economic resources.

### PBAB-PR-01: price-free reserve extraction

Attack query:

```text
Can an adversary manipulate the selected pool immediately before a buyback and
sell ZDEX to the protocol above the governed price envelope?
```

Required closure:

- positive minimum output;
- maximum quote spend per command and epoch;
- finalized and fresh Oracle or TWAP occurrence;
- maximum deviation and execution-impact bounds;
- authenticated reserve prestate and minimum-liquidity policy;
- deterministic ordering, deadline, cooldown, and split-execution rules;
- a bounded MEV-loss theorem or a protected batch or commit-reveal ordering
  mechanism.

### PBAB-BR-01: reusable fee budget

Attack query:

```text
Can two distinct buyback occurrences present the same verified fee-allocation
object and each spend its full amount?
```

The current ZenoDEX SHADOW composer admits this bounded counterexample. The
route must remain unmounted until the budget is represented by a state-linked
single-use authorization or by one atomic command occurrence whose complete
fee-allocation, purchase, and burn state transition is chained through the
lane coordinator and epoch verifier.

### PBAB-TS-01: terminal or partial-effect bypass

Attack query:

```text
Can a consumer apply the purchase effect plan while ignoring the burn, the
tokenomics lane transition, or a nonzero terminal obligation?
```

Required closure:

- one route certificate commits global prestate and poststate roots;
- every changed lane has one canonically sequenced lane write;
- the transient burn port is occurrence-scoped and cannot survive acceptance;
- accepted effects are inaccessible to the publisher until every terminal
  obligation is discharged;
- crash and partial-failure tests show that quote assets or purchased ZDEX
  cannot become stranded.

### PBAB-CF-01: configuration suppresses burning

Attack query:

```text
Can a zero fee, zero bounty, maximum developer share, or another boundary
configuration purchase ZDEX without burning the exact net amount?
```

Required closure:

- burn amount is computed independently of optional compensation branches;
- `purchased_zdex_atoms = burned_zdex_atoms` is a route invariant;
- zero, one-basis-point, maximum-neighbor, and maximum parameter tests kill
  branch-coupling mutants;
- profile activation rejects parameter combinations outside the proved
  envelope.

## Current ZenoDEX status

The SHADOW pool-binding patch closes literal reserve-principal substitution at
the outer composer. It does not yet close semantic pool-definition
substitution, reusable fee budgets, price integrity, real purchase-proof
coverage, complete tokenomics lane state chaining, terminal closure, or epoch
publication. Production and value-moving authority remain `NONE`.

ShapeForge terminology was used to name the disaster states and evidence
obligations. ShapeForge output is advisory and supplies no acceptance evidence.

