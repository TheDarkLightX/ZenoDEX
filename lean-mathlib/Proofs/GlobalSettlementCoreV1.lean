/-!
# GlobalSettlementABI V1 — structural core

This file is a machine-checked *structural* foundation for the
`GlobalSettlementABI V1` object graph defined in
`src/core/global_settlement_types_v1.py`. It is deliberately narrow: it fixes
the closed lane enumeration, the per-asset effect algebra, the conservation
law relating accounted holdings to accounted supply, the separate
non-negativity admission premise, and the shape of a typed rejection.

## What is modeled

* The twelve stable lane identifiers of `LaneIdV1`, in canonical order.
* `EconomicEffectKindV1` as a closed nine-constructor enumeration.
* `EconomicEffectRowV1` as a row carrying a kind, principal, asset, custody
  domain tag, and a signed atom delta.
* The per-asset issue/burn projection that `GlobalEconomicEffectPlanV1`
  computes in `_validate_issue_burn_projection`.
* The two conservation equations of `AssetConservationRowV1`:
  `owned_and_custodied_post = owned_and_custodied_pre + issue - burn` and
  `supply_post = supply_pre + issue - burn`.
* `LaneTransitionRejectCodeV1` and the `LaneTransitionRejectedV1` discipline
  that a rejection returns the exact pre-state and the empty effect plan.

## Modeling decisions

Every quantity is indexed by asset. Balances are functions `Asset → Int`, and
the issue/burn projections take the asset as an argument. There is no
operation in this file that adds atoms of one asset to atoms of another, and
`netIssuance_ignores_other_assets` states that separation as a theorem.

Atom counts are modeled in `Int`, not in a non-negative type. The Python ABI
stores these fields as `u128` and therefore rejects a negative result inside
`AssetConservationRowV1.__post_init__`. That check is a *separate admission
premise* here (`NonNegativityAdmitted`), not a consequence of conservation.
`nonNegativity_premise_is_necessary` exhibits a well-formed plan that drives a
non-negative book negative, so the premise is load-bearing rather than
decorative.

`accountedHoldings` and `accountedSupply` are two distinct ledger columns.
They are not assumed equal, and the conservation results are stated as
*preservation* results: the gap between the two columns is invariant, so an
equality that held before a plan still holds after it. The `custodyDomain`
field is an uninterpreted accounting tag copied from the ABI; nothing here reads
it, and no statement in this file concerns legal custody, title, or
enforceable claim over any asset.

## What is NOT claimed

This file proves none of the following, and no theorem below should be cited
as evidence for any of them:

* economic-policy correctness, adequacy, or safety of any lane;
* canonical byte encoding injectivity, or any property of `hash_global_v1`;
* refinement between this model and the Python or Rust runtime;
* replay safety, occurrence-consumption soundness, or nonce discipline;
* mounted authority, release-status gating, or evidence-status semantics;
* production readiness of any component;
* commutativity of commands, lanes, or effect plans. `seqPlan` is proved
  associative and is *not* proved commutative;
  `seqPlan_rows_not_commutative` exhibits a concrete ordered pair whose row
  journals differ under exchange.
-/

namespace Proofs
namespace GlobalSettlementCoreV1

/-! ## 1. Lane identifiers

The closed enumeration `LaneIdV1`. The `code` function reproduces the exact
Python string values, and `allLaneIds_codes` pins the canonical order that
`ALL_LANE_IDS_V1` and `LaneRegistryV1` depend on. -/

/-- The twelve ABI V1 settlement lanes. -/
inductive LaneId where
  | assetTransfer
  | spotLiquidity
  | farmIncentives
  | zdexTokenomics
  | zusdMonetary
  | perpsMarket
  | oracleMarket
  | sealedAuction
  | strategyEscrow
  | proofRewards
  | externalCustody
  | governanceMigration
  deriving DecidableEq, Repr

/-- The stable wire string for each lane, matching `LaneIdV1` values. -/
def LaneId.code : LaneId → String
  | .assetTransfer => "ASSET_TRANSFER"
  | .spotLiquidity => "SPOT_LIQUIDITY"
  | .farmIncentives => "FARM_INCENTIVES"
  | .zdexTokenomics => "ZDEX_TOKENOMICS"
  | .zusdMonetary => "ZUSD_MONETARY"
  | .perpsMarket => "PERPS_MARKET"
  | .oracleMarket => "ORACLE_MARKET"
  | .sealedAuction => "SEALED_AUCTION"
  | .strategyEscrow => "STRATEGY_ESCROW"
  | .proofRewards => "PROOF_REWARDS"
  | .externalCustody => "EXTERNAL_CUSTODY"
  | .governanceMigration => "GOVERNANCE_MIGRATION"

/-- Canonical position of each lane, matching `ALL_LANE_IDS_V1.index`. -/
def LaneId.index : LaneId → Nat
  | .assetTransfer => 0
  | .spotLiquidity => 1
  | .farmIncentives => 2
  | .zdexTokenomics => 3
  | .zusdMonetary => 4
  | .perpsMarket => 5
  | .oracleMarket => 6
  | .sealedAuction => 7
  | .strategyEscrow => 8
  | .proofRewards => 9
  | .externalCustody => 10
  | .governanceMigration => 11

/-- The canonical lane order, mirroring `ALL_LANE_IDS_V1`. -/
def allLaneIds : List LaneId :=
  [ .assetTransfer, .spotLiquidity, .farmIncentives, .zdexTokenomics,
    .zusdMonetary, .perpsMarket, .oracleMarket, .sealedAuction,
    .strategyEscrow, .proofRewards, .externalCustody, .governanceMigration ]

/-- Boolean duplicate check, kept self-contained so the enumeration facts do
not depend on any library `Nodup` API. -/
def hasDuplicateLane : List LaneId → Bool
  | [] => false
  | l :: rest => rest.contains l || hasDuplicateLane rest

theorem allLaneIds_length : allLaneIds.length = 12 := rfl

/-- The canonical order, spelled out against the Python string values. -/
theorem allLaneIds_codes :
    allLaneIds.map LaneId.code =
      [ "ASSET_TRANSFER", "SPOT_LIQUIDITY", "FARM_INCENTIVES", "ZDEX_TOKENOMICS",
        "ZUSD_MONETARY", "PERPS_MARKET", "ORACLE_MARKET", "SEALED_AUCTION",
        "STRATEGY_ESCROW", "PROOF_REWARDS", "EXTERNAL_CUSTODY",
        "GOVERNANCE_MIGRATION" ] := rfl

theorem allLaneIds_indices :
    allLaneIds.map LaneId.index = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := rfl

/-- The enumeration is complete: there is no lane outside `allLaneIds`. -/
theorem allLaneIds_complete (l : LaneId) : l ∈ allLaneIds := by
  cases l <;> decide

/-- The enumeration has no repeats. Together with `allLaneIds_length` and
`allLaneIds_complete` this pins the lane set at exactly twelve members. -/
theorem allLaneIds_no_duplicates : hasDuplicateLane allLaneIds = false := by
  decide

theorem LaneId.index_lt_twelve (l : LaneId) : l.index < 12 := by
  cases l <;> decide

theorem LaneId.index_injective {a b : LaneId} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-! ## 2. Assets, principals, custody domains

These are uninterpreted tokens in the ABI. `custodyDomain` is a tag only:
no theorem in this file interprets it, and none asserts anything about legal
custody or enforceable title. -/

abbrev Asset := String
abbrev Principal := String
abbrev CustodyDomain := String

/-! ## 3. Effect rows

`EconomicEffectKindV1` and `EconomicEffectRowV1`. `RowWellFormed` mirrors the
three invariants enforced in `EconomicEffectRowV1.__post_init__`. -/

/-- The closed set of economic effect kinds. -/
inductive EffectKind where
  | accountMovement
  | issue
  | burn
  | custody
  | liability
  | reserve
  | feeAllocation
  | reward
  | slash
  deriving DecidableEq, Repr

/-- A single canonical effect row. `deltaAtoms` is signed. -/
structure EffectRow where
  kind : EffectKind
  principal : Principal
  asset : Asset
  custodyDomain : CustodyDomain
  deltaAtoms : Int
  deriving DecidableEq, Repr

/-- Row-level invariants from `EconomicEffectRowV1.__post_init__`: the delta is
nonzero, an issue is strictly positive, and a burn is strictly negative. -/
structure RowWellFormed (r : EffectRow) : Prop where
  nonzero : r.deltaAtoms ≠ 0
  issuePositive : r.kind = EffectKind.issue → 0 < r.deltaAtoms
  burnNegative : r.kind = EffectKind.burn → r.deltaAtoms < 0

/-! ## 4. Per-asset issue and burn projections

Each projection is indexed by asset. Rows for other assets contribute zero, so
atoms of unlike assets are never added together. -/

/-- Contribution of one row to the issued total *for a named asset*. -/
def issuedAtoms (asset : Asset) (r : EffectRow) : Int :=
  if r.kind = EffectKind.issue ∧ r.asset = asset then r.deltaAtoms else 0

/-- Contribution of one row to the burned total *for a named asset*. Burn rows
carry a negative delta, so the burned magnitude is its negation, matching
`burn_by_asset[...] - row.delta_atoms` in the Python projection. -/
def burnedAtoms (asset : Asset) (r : EffectRow) : Int :=
  if r.kind = EffectKind.burn ∧ r.asset = asset then -r.deltaAtoms else 0

/-- Total authorized issue for one asset across a row journal. -/
def issuedFor (asset : Asset) : List EffectRow → Int
  | [] => 0
  | r :: rest => issuedAtoms asset r + issuedFor asset rest

/-- Total authorized burn magnitude for one asset across a row journal. -/
def burnedFor (asset : Asset) : List EffectRow → Int
  | [] => 0
  | r :: rest => burnedAtoms asset r + burnedFor asset rest

/-- Net authorized issuance for one asset: issued minus burned. -/
def netIssuance (asset : Asset) (rows : List EffectRow) : Int :=
  issuedFor asset rows - burnedFor asset rows

theorem issuedFor_nil (asset : Asset) : issuedFor asset [] = 0 := rfl

theorem burnedFor_nil (asset : Asset) : burnedFor asset [] = 0 := rfl

theorem netIssuance_nil (asset : Asset) : netIssuance asset [] = 0 := rfl

theorem issuedFor_append (asset : Asset) (xs ys : List EffectRow) :
    issuedFor asset (xs ++ ys) = issuedFor asset xs + issuedFor asset ys := by
  induction xs with
  | nil =>
      simp only [List.nil_append, issuedFor]
      omega
  | cons r rest ih =>
      simp only [List.cons_append, issuedFor, ih]
      omega

theorem burnedFor_append (asset : Asset) (xs ys : List EffectRow) :
    burnedFor asset (xs ++ ys) = burnedFor asset xs + burnedFor asset ys := by
  induction xs with
  | nil =>
      simp only [List.nil_append, burnedFor]
      omega
  | cons r rest ih =>
      simp only [List.cons_append, burnedFor, ih]
      omega

theorem netIssuance_append (asset : Asset) (xs ys : List EffectRow) :
    netIssuance asset (xs ++ ys) = netIssuance asset xs + netIssuance asset ys := by
  simp only [netIssuance, issuedFor_append, burnedFor_append]
  omega

/-- A row for a different asset contributes nothing to that asset's issue
total. This is the formal content of "never sum unlike assets". -/
theorem issuedAtoms_of_other_asset {asset : Asset} {r : EffectRow}
    (h : r.asset ≠ asset) : issuedAtoms asset r = 0 := by
  simp only [issuedAtoms]
  exact if_neg (fun hc => h hc.2)

theorem burnedAtoms_of_other_asset {asset : Asset} {r : EffectRow}
    (h : r.asset ≠ asset) : burnedAtoms asset r = 0 := by
  simp only [burnedAtoms]
  exact if_neg (fun hc => h hc.2)

theorem issuedFor_cons_of_other_asset {asset : Asset} {r : EffectRow}
    {rest : List EffectRow} (h : r.asset ≠ asset) :
    issuedFor asset (r :: rest) = issuedFor asset rest := by
  simp only [issuedFor, issuedAtoms_of_other_asset h]
  omega

theorem burnedFor_cons_of_other_asset {asset : Asset} {r : EffectRow}
    {rest : List EffectRow} (h : r.asset ≠ asset) :
    burnedFor asset (r :: rest) = burnedFor asset rest := by
  simp only [burnedFor, burnedAtoms_of_other_asset h]
  omega

/-- Asset separation, stated on the net projection. -/
theorem netIssuance_ignores_other_assets {asset : Asset} {r : EffectRow}
    {rest : List EffectRow} (h : r.asset ≠ asset) :
    netIssuance asset (r :: rest) = netIssuance asset rest := by
  simp only [netIssuance, issuedFor_cons_of_other_asset h,
    burnedFor_cons_of_other_asset h]

/-- Under the row invariants the issued total is non-negative, matching the
`u128` typing of `authorized_issue_atoms`. -/
theorem issuedFor_nonneg {asset : Asset} {rows : List EffectRow}
    (h : ∀ r ∈ rows, RowWellFormed r) : 0 ≤ issuedFor asset rows := by
  induction rows with
  | nil =>
      simp only [issuedFor]
      decide
  | cons r rest ih =>
      have hr : RowWellFormed r := h r List.mem_cons_self
      have hrest : ∀ x ∈ rest, RowWellFormed x :=
        fun x hx => h x (List.mem_cons_of_mem r hx)
      have hhead : 0 ≤ issuedAtoms asset r := by
        simp only [issuedAtoms]
        split
        · next hc =>
            have hpos := hr.issuePositive hc.1
            omega
        · omega
      have htail := ih hrest
      simp only [issuedFor]
      omega

/-- Under the row invariants the burned magnitude is non-negative, matching the
`u128` typing of `authorized_burn_atoms`. -/
theorem burnedFor_nonneg {asset : Asset} {rows : List EffectRow}
    (h : ∀ r ∈ rows, RowWellFormed r) : 0 ≤ burnedFor asset rows := by
  induction rows with
  | nil =>
      simp only [burnedFor]
      decide
  | cons r rest ih =>
      have hr : RowWellFormed r := h r List.mem_cons_self
      have hrest : ∀ x ∈ rest, RowWellFormed x :=
        fun x hx => h x (List.mem_cons_of_mem r hx)
      have hhead : 0 ≤ burnedAtoms asset r := by
        simp only [burnedAtoms]
        split
        · next hc =>
            have hneg := hr.burnNegative hc.1
            omega
        · omega
      have htail := ih hrest
      simp only [burnedFor]
      omega

/-! ## 5. Effect plans

A plan carries its canonical row journal together with the per-asset holdings
and supply deltas that `AssetConservationRowV1` records. Well-formedness is
exactly the pair of conservation equations from that dataclass. -/

/-- A global economic effect plan, modeled as a row journal plus the per-asset
deltas it authorizes. -/
structure EffectPlan where
  rows : List EffectRow
  holdingsDelta : Asset → Int
  supplyDelta : Asset → Int

/-- The two conservation equations of `AssetConservationRowV1`, stated for
every asset: the accounted-holdings delta and the accounted-supply delta each
equal issued minus burned. -/
structure PlanWellFormed (p : EffectPlan) : Prop where
  holdings : ∀ a : Asset, p.holdingsDelta a = netIssuance a p.rows
  supply : ∀ a : Asset, p.supplyDelta a = netIssuance a p.rows

/-- Row invariants lifted to a whole plan. -/
def PlanRowsWellFormed (p : EffectPlan) : Prop :=
  ∀ r ∈ p.rows, RowWellFormed r

/-- The identity plan, corresponding to `GlobalEconomicEffectPlanV1.empty()`. -/
def identityPlan : EffectPlan where
  rows := []
  holdingsDelta := fun _ => 0
  supplyDelta := fun _ => 0

/-- The empty effect plan carried by every rejection. -/
abbrev emptyPlan : EffectPlan := identityPlan

/-- Sequential composition: journals concatenate in order, deltas add per
asset. -/
def seqPlan (p q : EffectPlan) : EffectPlan where
  rows := p.rows ++ q.rows
  holdingsDelta := fun a => p.holdingsDelta a + q.holdingsDelta a
  supplyDelta := fun a => p.supplyDelta a + q.supplyDelta a

theorem identityPlan_rows : identityPlan.rows = [] := rfl

theorem identityPlan_holdingsDelta (a : Asset) :
    identityPlan.holdingsDelta a = 0 := rfl

theorem identityPlan_supplyDelta (a : Asset) :
    identityPlan.supplyDelta a = 0 := rfl

/-- The identity plan is well-formed. -/
theorem identityPlan_wellFormed : PlanWellFormed identityPlan :=
  { holdings := fun _ => rfl, supply := fun _ => rfl }

theorem identityPlan_rowsWellFormed : PlanRowsWellFormed identityPlan := by
  intro r hr
  simp [identityPlan] at hr

/-- Sequential composition preserves well-formedness. -/
theorem seqPlan_wellFormed {p q : EffectPlan}
    (hp : PlanWellFormed p) (hq : PlanWellFormed q) :
    PlanWellFormed (seqPlan p q) := by
  constructor
  · intro a
    simp only [seqPlan, netIssuance_append, hp.holdings a, hq.holdings a]
  · intro a
    simp only [seqPlan, netIssuance_append, hp.supply a, hq.supply a]

/-- Sequential composition preserves the row invariants. -/
theorem seqPlan_rowsWellFormed {p q : EffectPlan}
    (hp : PlanRowsWellFormed p) (hq : PlanRowsWellFormed q) :
    PlanRowsWellFormed (seqPlan p q) := by
  intro r hr
  simp only [seqPlan, List.mem_append] at hr
  cases hr with
  | inl h => exact hp r h
  | inr h => exact hq r h

theorem seqPlan_identity_left (p : EffectPlan) :
    (seqPlan identityPlan p).rows = p.rows := by
  simp only [seqPlan, identityPlan, List.nil_append]

theorem seqPlan_identity_right (p : EffectPlan) :
    (seqPlan p identityPlan).rows = p.rows := by
  simp only [seqPlan, identityPlan, List.append_nil]

/-- Composition is associative on row journals. Associativity is *not*
commutativity; see `seqPlan_rows_not_commutative`. -/
theorem seqPlan_rows_assoc (p q r : EffectPlan) :
    (seqPlan (seqPlan p q) r).rows = (seqPlan p (seqPlan q r)).rows := by
  simp only [seqPlan, List.append_assoc]

/-! ## 6. Books

Two distinct accounted columns. `accountedHoldings` corresponds to
`owned_and_custodied_*_atoms` and `accountedSupply` to `supply_*_atoms`. They
are not assumed equal. -/

/-- Per-asset accounted balances. -/
structure AssetBook where
  accountedHoldings : Asset → Int
  accountedSupply : Asset → Int

/-- The signed gap between the two accounted columns, per asset. -/
def gap (b : AssetBook) (a : Asset) : Int :=
  b.accountedHoldings a - b.accountedSupply a

/-- The property that accounted holdings equal accounted supply, per asset.
This is a statement about two ledger columns, not about legal custody. -/
def HoldingsMatchSupply (b : AssetBook) : Prop :=
  ∀ a : Asset, b.accountedHoldings a = b.accountedSupply a

/-- Non-negativity of both accounted columns, mirroring the `u128` typing. -/
def NonNegative (b : AssetBook) : Prop :=
  ∀ a : Asset, 0 ≤ b.accountedHoldings a ∧ 0 ≤ b.accountedSupply a

/-! ## 7. Application and the conservation theorem -/

/-- The pre/post application relation for a plan. -/
structure Applies (pre : AssetBook) (p : EffectPlan) (post : AssetBook) : Prop where
  holdings : ∀ a : Asset,
    post.accountedHoldings a = pre.accountedHoldings a + p.holdingsDelta a
  supply : ∀ a : Asset,
    post.accountedSupply a = pre.accountedSupply a + p.supplyDelta a

/-- The canonical post-state produced by applying a plan. -/
def applyPlan (pre : AssetBook) (p : EffectPlan) : AssetBook where
  accountedHoldings := fun a => pre.accountedHoldings a + p.holdingsDelta a
  accountedSupply := fun a => pre.accountedSupply a + p.supplyDelta a

/-- `applyPlan` inhabits the relation, so `Applies` is never vacuous. -/
theorem applyPlan_applies (pre : AssetBook) (p : EffectPlan) :
    Applies pre p (applyPlan pre p) := by
  constructor
  · intro a
    rfl
  · intro a
    rfl

/-- Core conservation result: a well-formed plan moves both accounted columns
by the same per-asset amount, so the gap between them is invariant. -/
theorem applies_preserves_gap {pre post : AssetBook} {p : EffectPlan}
    (hp : PlanWellFormed p) (happ : Applies pre p post) (a : Asset) :
    gap post a = gap pre a := by
  have hh := happ.holdings a
  have hs := happ.supply a
  have hdh := hp.holdings a
  have hds := hp.supply a
  simp only [gap, hh, hs, hdh, hds]
  omega

/-- Every well-formed plan preserves the equality of accounted holdings and
accounted supply. -/
theorem applies_preserves_holdingsMatchSupply {pre post : AssetBook}
    {p : EffectPlan} (hp : PlanWellFormed p) (happ : Applies pre p post)
    (hmatch : HoldingsMatchSupply pre) : HoldingsMatchSupply post := by
  intro a
  have hgap := applies_preserves_gap hp happ a
  have hpre := hmatch a
  simp only [gap] at hgap
  omega

/-! ## 8. Non-negativity as a separate acceptance premise

Conservation alone does not keep balances non-negative. The runtime rejects a
plan whose result would underflow, and that check is modeled here as an
explicit admission premise rather than derived. -/

/-- The admission check: the post-state that this plan would produce is
non-negative in both columns for every asset. -/
def NonNegativityAdmitted (pre : AssetBook) (p : EffectPlan) : Prop :=
  ∀ a : Asset,
    0 ≤ pre.accountedHoldings a + p.holdingsDelta a ∧
    0 ≤ pre.accountedSupply a + p.supplyDelta a

/-- An accepted transition: a well-formed plan with well-formed rows, applied
to the pre-state, whose non-negativity was separately admitted. -/
structure Accepted (pre : AssetBook) (p : EffectPlan) (post : AssetBook) : Prop where
  planWellFormed : PlanWellFormed p
  rowsWellFormed : PlanRowsWellFormed p
  applies : Applies pre p post
  nonNegativityAdmitted : NonNegativityAdmitted pre p

/-- Accepted transitions preserve the holdings/supply equality. -/
theorem accepted_preserves_holdingsMatchSupply {pre post : AssetBook}
    {p : EffectPlan} (hacc : Accepted pre p post)
    (hmatch : HoldingsMatchSupply pre) : HoldingsMatchSupply post :=
  applies_preserves_holdingsMatchSupply hacc.planWellFormed hacc.applies hmatch

/-- Non-negativity of the post-state follows *from the admission premise*, and
only from it. -/
theorem accepted_post_nonNegative {pre post : AssetBook} {p : EffectPlan}
    (hacc : Accepted pre p post) : NonNegative post := by
  intro a
  have hadm := hacc.nonNegativityAdmitted a
  have hh := hacc.applies.holdings a
  have hs := hacc.applies.supply a
  have h1 := hadm.1
  have h2 := hadm.2
  exact ⟨by omega, by omega⟩

/-! ## 9. Typed rejection

`LaneTransitionRejectedV1` forces `post_state_root == pre_state_root` and an
empty effect plan. Here the rejected constructor carries only a code, so the
returned state is definitionally the pre-state and the returned plan is
definitionally empty: the discipline is structural, not a side condition. -/

/-- The closed set of rejection codes from `LaneTransitionRejectCodeV1`. -/
inductive RejectCode where
  | unknownCommand
  | disabledFeature
  | releaseMismatch
  | invalidContext
  | invalidState
  | policyReject
  | resourceLimit
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .disabledFeature => "DISABLED_FEATURE"
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .invalidContext => "INVALID_CONTEXT"
  | .invalidState => "INVALID_STATE"
  | .policyReject => "POLICY_REJECT"
  | .resourceLimit => "RESOURCE_LIMIT"

def allRejectCodes : List RejectCode :=
  [ .unknownCommand, .disabledFeature, .releaseMismatch, .invalidContext,
    .invalidState, .policyReject, .resourceLimit ]

theorem allRejectCodes_length : allRejectCodes.length = 7 := rfl

theorem allRejectCodes_complete (c : RejectCode) : c ∈ allRejectCodes := by
  cases c <;> decide

theorem allRejectCodes_codes :
    allRejectCodes.map RejectCode.code =
      [ "UNKNOWN_COMMAND", "DISABLED_FEATURE", "RELEASE_MISMATCH",
        "INVALID_CONTEXT", "INVALID_STATE", "POLICY_REJECT",
        "RESOURCE_LIMIT" ] := rfl

/-- The outcome of a lane transition attempt. A rejection carries only its
code; it has no room to carry a different state or a nonempty plan. -/
inductive Outcome where
  | accepted (post : AssetBook) (plan : EffectPlan)
  | rejected (code : RejectCode)

/-- The state observed after an outcome, given the pre-state. -/
def Outcome.postState (pre : AssetBook) : Outcome → AssetBook
  | .accepted post _ => post
  | .rejected _ => pre

/-- The effect plan emitted by an outcome. -/
def Outcome.effects : Outcome → EffectPlan
  | .accepted _ plan => plan
  | .rejected _ => emptyPlan

/-- Every rejection returns the exact pre-state. -/
theorem rejected_postState (c : RejectCode) (pre : AssetBook) :
    (Outcome.rejected c).postState pre = pre := rfl

/-- Every rejection emits the empty effect plan. -/
theorem rejected_effects (c : RejectCode) :
    (Outcome.rejected c).effects = emptyPlan := rfl

theorem rejected_effects_rows (c : RejectCode) :
    (Outcome.rejected c).effects.rows = [] := rfl

theorem rejected_effects_holdingsDelta (c : RejectCode) (a : Asset) :
    (Outcome.rejected c).effects.holdingsDelta a = 0 := rfl

theorem rejected_effects_supplyDelta (c : RejectCode) (a : Asset) :
    (Outcome.rejected c).effects.supplyDelta a = 0 := rfl

/-- Pointwise restatement: no accounted balance moves under a rejection. -/
theorem rejected_preserves_holdings (c : RejectCode) (pre : AssetBook)
    (a : Asset) :
    ((Outcome.rejected c).postState pre).accountedHoldings a
      = pre.accountedHoldings a := rfl

theorem rejected_preserves_supply (c : RejectCode) (pre : AssetBook)
    (a : Asset) :
    ((Outcome.rejected c).postState pre).accountedSupply a
      = pre.accountedSupply a := rfl

/-- A rejection preserves the holdings/supply equality, for free. -/
theorem rejected_preserves_holdingsMatchSupply (c : RejectCode)
    {pre : AssetBook} (h : HoldingsMatchSupply pre) :
    HoldingsMatchSupply ((Outcome.rejected c).postState pre) := h

/-- A rejection preserves non-negativity, for free. -/
theorem rejected_preserves_nonNegative (c : RejectCode) {pre : AssetBook}
    (h : NonNegative pre) :
    NonNegative ((Outcome.rejected c).postState pre) := h

/-- Applying the identity plan leaves the book unchanged. -/
theorem applies_identityPlan (pre : AssetBook) : Applies pre identityPlan pre := by
  constructor
  · intro a
    show pre.accountedHoldings a = pre.accountedHoldings a + 0
    omega
  · intro a
    show pre.accountedSupply a = pre.accountedSupply a + 0
    omega

/-- A rejected outcome applies the identity plan to the pre-state. -/
theorem rejected_applies_identity (c : RejectCode) (pre : AssetBook) :
    Applies pre (Outcome.rejected c).effects
      ((Outcome.rejected c).postState pre) :=
  applies_identityPlan pre

/-- Outcomes are exactly accepted or rejected. -/
theorem outcome_dichotomy (o : Outcome) :
    (∃ post plan, o = Outcome.accepted post plan) ∨
    (∃ c, o = Outcome.rejected c) := by
  cases o with
  | accepted post plan => exact Or.inl ⟨post, plan, rfl⟩
  | rejected c => exact Or.inr ⟨c, rfl⟩

/-! ## 10. Non-vacuity witnesses

Concrete instances so that the definitions above are not satisfied only by
degenerate objects. One same-asset transfer, one managed issue, one burn, and
one two-asset plan showing that unlike assets stay separate. -/

def zusd : Asset := "ZUSD"
def zdex : Asset := "ZDEX"
def alice : Principal := "alice"
def bob : Principal := "bob"
def treasury : Principal := "treasury"
def ledgerDomain : CustodyDomain := "zenoledger:core"

theorem zusd_ne_zdex : zusd ≠ zdex := by decide

/-- A ledger-internal transfer: one debit and one credit of the same asset. -/
def transferRows : List EffectRow :=
  [ { kind := .accountMovement, principal := alice, asset := zusd,
      custodyDomain := ledgerDomain, deltaAtoms := -100 },
    { kind := .accountMovement, principal := bob, asset := zusd,
      custodyDomain := ledgerDomain, deltaAtoms := 100 } ]

def transferPlan : EffectPlan where
  rows := transferRows
  holdingsDelta := fun _ => 0
  supplyDelta := fun _ => 0

/-- A managed issue of 250 atoms to the treasury principal. -/
def issueRows : List EffectRow :=
  [ { kind := .issue, principal := treasury, asset := zusd,
      custodyDomain := ledgerDomain, deltaAtoms := 250 } ]

def issuePlan : EffectPlan where
  rows := issueRows
  holdingsDelta := fun a => if zusd = a then 250 else 0
  supplyDelta := fun a => if zusd = a then 250 else 0

/-- A burn of 70 atoms from the treasury principal. -/
def burnRows : List EffectRow :=
  [ { kind := .burn, principal := treasury, asset := zusd,
      custodyDomain := ledgerDomain, deltaAtoms := -70 } ]

def burnPlan : EffectPlan where
  rows := burnRows
  holdingsDelta := fun a => if zusd = a then -70 else 0
  supplyDelta := fun a => if zusd = a then -70 else 0

theorem transferPlan_rows_ne_nil : transferPlan.rows ≠ [] := by decide

theorem issuePlan_rows_ne_nil : issuePlan.rows ≠ [] := by decide

theorem burnPlan_rows_ne_nil : burnPlan.rows ≠ [] := by decide

theorem transferPlan_rowsWellFormed : PlanRowsWellFormed transferPlan := by
  intro r hr
  simp [transferPlan, transferRows] at hr
  cases hr with
  | inl h =>
      subst h
      exact ⟨by decide, by intro hk; exact absurd hk (by decide),
        by intro hk; exact absurd hk (by decide)⟩
  | inr h =>
      subst h
      exact ⟨by decide, by intro hk; exact absurd hk (by decide),
        by intro hk; exact absurd hk (by decide)⟩

theorem issuePlan_rowsWellFormed : PlanRowsWellFormed issuePlan := by
  intro r hr
  simp [issuePlan, issueRows] at hr
  subst hr
  exact ⟨by decide, by intro _; decide, by intro hk; exact absurd hk (by decide)⟩

theorem burnPlan_rowsWellFormed : PlanRowsWellFormed burnPlan := by
  intro r hr
  simp [burnPlan, burnRows] at hr
  subst hr
  exact ⟨by decide, by intro hk; exact absurd hk (by decide), by intro _; decide⟩

/-- A same-asset transfer authorizes no issuance for any asset. -/
theorem transferRows_netIssuance (a : Asset) : netIssuance a transferRows = 0 := by
  simp [transferRows, netIssuance, issuedFor, burnedFor, issuedAtoms, burnedAtoms]

theorem transferPlan_wellFormed : PlanWellFormed transferPlan :=
  { holdings := fun a => (transferRows_netIssuance a).symm
    supply := fun a => (transferRows_netIssuance a).symm }

theorem issueRows_netIssuance_zusd : netIssuance zusd issueRows = 250 := by decide

theorem issueRows_netIssuance_other {a : Asset} (h : zusd ≠ a) :
    netIssuance a issueRows = 0 := by
  simp [issueRows, netIssuance, issuedFor, burnedFor, issuedAtoms, burnedAtoms, h]

theorem issuePlan_wellFormed : PlanWellFormed issuePlan := by
  constructor
  · intro a
    show (if zusd = a then (250 : Int) else 0) = netIssuance a issueRows
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact issueRows_netIssuance_zusd.symm
    · rw [if_neg h]
      exact (issueRows_netIssuance_other h).symm
  · intro a
    show (if zusd = a then (250 : Int) else 0) = netIssuance a issueRows
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact issueRows_netIssuance_zusd.symm
    · rw [if_neg h]
      exact (issueRows_netIssuance_other h).symm

theorem burnRows_netIssuance_zusd : netIssuance zusd burnRows = -70 := by decide

theorem burnRows_netIssuance_other {a : Asset} (h : zusd ≠ a) :
    netIssuance a burnRows = 0 := by
  simp [burnRows, netIssuance, issuedFor, burnedFor, issuedAtoms, burnedAtoms, h]

theorem burnPlan_wellFormed : PlanWellFormed burnPlan := by
  constructor
  · intro a
    show (if zusd = a then (-70 : Int) else 0) = netIssuance a burnRows
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact burnRows_netIssuance_zusd.symm
    · rw [if_neg h]
      exact (burnRows_netIssuance_other h).symm
  · intro a
    show (if zusd = a then (-70 : Int) else 0) = netIssuance a burnRows
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact burnRows_netIssuance_zusd.symm
    · rw [if_neg h]
      exact (burnRows_netIssuance_other h).symm

/-- A demonstration book holding 1000 atoms of ZUSD in both columns. -/
def demoBook : AssetBook where
  accountedHoldings := fun a => if zusd = a then 1000 else 0
  accountedSupply := fun a => if zusd = a then 1000 else 0

theorem demoBook_holdingsMatchSupply : HoldingsMatchSupply demoBook := by
  intro a
  rfl

theorem demoBook_nonNegative : NonNegative demoBook := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, if_neg h]
    exact ⟨by decide, by decide⟩

theorem transferPlan_admitted : NonNegativityAdmitted demoBook transferPlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, transferPlan, if_neg h]
    exact ⟨by decide, by decide⟩

theorem issuePlan_admitted : NonNegativityAdmitted demoBook issuePlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, issuePlan, if_neg h]
    exact ⟨by decide, by decide⟩

theorem burnPlan_admitted : NonNegativityAdmitted demoBook burnPlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, burnPlan, if_neg h]
    exact ⟨by decide, by decide⟩

/-- Witness 1: a transfer is an accepted transition. -/
theorem transfer_accepted :
    Accepted demoBook transferPlan (applyPlan demoBook transferPlan) :=
  { planWellFormed := transferPlan_wellFormed
    rowsWellFormed := transferPlan_rowsWellFormed
    applies := applyPlan_applies demoBook transferPlan
    nonNegativityAdmitted := transferPlan_admitted }

/-- Witness 2: a managed issue is an accepted transition. -/
theorem issue_accepted :
    Accepted demoBook issuePlan (applyPlan demoBook issuePlan) :=
  { planWellFormed := issuePlan_wellFormed
    rowsWellFormed := issuePlan_rowsWellFormed
    applies := applyPlan_applies demoBook issuePlan
    nonNegativityAdmitted := issuePlan_admitted }

/-- Witness 3: a burn is an accepted transition. -/
theorem burn_accepted :
    Accepted demoBook burnPlan (applyPlan demoBook burnPlan) :=
  { planWellFormed := burnPlan_wellFormed
    rowsWellFormed := burnPlan_rowsWellFormed
    applies := applyPlan_applies demoBook burnPlan
    nonNegativityAdmitted := burnPlan_admitted }

/-- Concrete post-state values, so the witnesses are visibly non-degenerate. -/
theorem transfer_post_values :
    (applyPlan demoBook transferPlan).accountedHoldings zusd = 1000 ∧
    (applyPlan demoBook transferPlan).accountedSupply zusd = 1000 := by
  constructor
  · rfl
  · rfl

theorem issue_post_values :
    (applyPlan demoBook issuePlan).accountedHoldings zusd = 1250 ∧
    (applyPlan demoBook issuePlan).accountedSupply zusd = 1250 := by
  constructor
  · rfl
  · rfl

theorem burn_post_values :
    (applyPlan demoBook burnPlan).accountedHoldings zusd = 930 ∧
    (applyPlan demoBook burnPlan).accountedSupply zusd = 930 := by
  constructor
  · rfl
  · rfl

/-- Each witness preserves the holdings/supply equality. -/
theorem transfer_preserves_holdingsMatchSupply :
    HoldingsMatchSupply (applyPlan demoBook transferPlan) :=
  accepted_preserves_holdingsMatchSupply transfer_accepted
    demoBook_holdingsMatchSupply

theorem issue_preserves_holdingsMatchSupply :
    HoldingsMatchSupply (applyPlan demoBook issuePlan) :=
  accepted_preserves_holdingsMatchSupply issue_accepted
    demoBook_holdingsMatchSupply

theorem burn_preserves_holdingsMatchSupply :
    HoldingsMatchSupply (applyPlan demoBook burnPlan) :=
  accepted_preserves_holdingsMatchSupply burn_accepted
    demoBook_holdingsMatchSupply

/-- Composition of the issue and burn witnesses is well-formed, netting +180. -/
theorem issueThenBurn_wellFormed : PlanWellFormed (seqPlan issuePlan burnPlan) :=
  seqPlan_wellFormed issuePlan_wellFormed burnPlan_wellFormed

theorem issueThenBurn_netIssuance_zusd :
    netIssuance zusd (seqPlan issuePlan burnPlan).rows = 180 := by decide

/-- A two-asset plan: unlike assets are projected separately and never summed
into a single raw total. -/
def mixedAssetRows : List EffectRow :=
  [ { kind := .issue, principal := treasury, asset := zusd,
      custodyDomain := ledgerDomain, deltaAtoms := 250 },
    { kind := .issue, principal := treasury, asset := zdex,
      custodyDomain := ledgerDomain, deltaAtoms := 40 } ]

theorem mixedAsset_netIssuance_zusd :
    netIssuance zusd mixedAssetRows = 250 := by decide

theorem mixedAsset_netIssuance_zdex :
    netIssuance zdex mixedAssetRows = 40 := by decide

/-- Neither per-asset projection equals the raw sum of the two deltas. -/
theorem mixedAsset_no_cross_asset_sum :
    netIssuance zusd mixedAssetRows ≠ 290 ∧
    netIssuance zdex mixedAssetRows ≠ 290 := by decide

/-! ## 11. The non-negativity premise is load-bearing

Conservation is preserved unconditionally, but non-negativity is not. This
countermodel is a well-formed plan with well-formed rows applied to a
non-negative book, whose post-state is negative. It shows
`NonNegativityAdmitted` cannot be dropped from `Accepted`. -/

/-- A book with only 10 atoms of ZUSD, less than `burnPlan` destroys. -/
def thinBook : AssetBook where
  accountedHoldings := fun a => if zusd = a then 10 else 0
  accountedSupply := fun a => if zusd = a then 10 else 0

theorem thinBook_nonNegative : NonNegative thinBook := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [thinBook, if_neg h]
    exact ⟨by decide, by decide⟩

theorem thinBook_holdingsMatchSupply : HoldingsMatchSupply thinBook := by
  intro a
  rfl

/-- The countermodel: well-formed plan, non-negative pre-state, negative
post-state. Hence non-negativity is preserved only under the explicit
admission premise. -/
theorem nonNegativity_premise_is_necessary :
    PlanWellFormed burnPlan ∧
    PlanRowsWellFormed burnPlan ∧
    NonNegative thinBook ∧
    Applies thinBook burnPlan (applyPlan thinBook burnPlan) ∧
    ¬ NonNegative (applyPlan thinBook burnPlan) := by
  refine ⟨burnPlan_wellFormed, burnPlan_rowsWellFormed, thinBook_nonNegative,
    applyPlan_applies thinBook burnPlan, ?_⟩
  intro hcontra
  have h := (hcontra zusd).1
  have hval : (applyPlan thinBook burnPlan).accountedHoldings zusd = -60 := rfl
  rw [hval] at h
  exact absurd h (by decide)

/-- Conservation still holds in the countermodel: the rejected-by-underflow
plan is not unsound, it is merely inadmissible. -/
theorem countermodel_still_conserves :
    HoldingsMatchSupply (applyPlan thinBook burnPlan) :=
  applies_preserves_holdingsMatchSupply burnPlan_wellFormed
    (applyPlan_applies thinBook burnPlan) thinBook_holdingsMatchSupply

/-- The admission premise genuinely fails here. -/
theorem thinBook_burn_not_admitted :
    ¬ NonNegativityAdmitted thinBook burnPlan := by
  intro hcontra
  have h := (hcontra zusd).1
  have hval : thinBook.accountedHoldings zusd + burnPlan.holdingsDelta zusd
      = -60 := rfl
  rw [hval] at h
  exact absurd h (by decide)

/-! ## 12. Sequential composition is not proved commutative

The row journal records order. Exchanging two plans yields a different
journal, so nothing in this file licenses a commutativity claim. The per-asset
*net arithmetic* of these two particular plans does coincide, since integer
addition is commutative; that is an arithmetic fact about `Int` and is not a
statement about command ordering, lane scheduling, or runtime execution. -/

theorem seqPlan_rows_not_commutative :
    (seqPlan issuePlan burnPlan).rows ≠ (seqPlan burnPlan issuePlan).rows := by
  intro h
  simp only [seqPlan, issuePlan, burnPlan, issueRows, burnRows,
    List.cons_append, List.nil_append, List.cons.injEq, EffectRow.mk.injEq] at h
  exact absurd h.1.1 (by decide)

end GlobalSettlementCoreV1
end Proofs
