import Init.Omega
import Init.Data.List.Lemmas

/-!
# ZDEX acquisition-and-burn occurrence exactness V2

This file proves an aggregate accounting condition for a modeled two-lane
buy-and-burn plan and establishes limits of that condition.

`Proofs/ZDEXAtomicBuybackAccountingV1.lean` takes `purchased = burned` as the
premise `exactPurchasedBurned`, and `Proofs/ZDEXAtomicBuybackTwoPhaseV2.lean`
obtains it by construction, because `acceptedEffects` copies one receipt field
into both `zdexPurchased` and `zdexBurned`. The Python route composer asserts
the same equality directly, comparing
`tokenomics.journal.burned_zdex_atoms` with `spot.journal.purchased_zdex_atoms`
inside `_terminal_bindings_match_v2`. Equality by construction and explicit
terminal binding remain the route guarantees. The additional result here
derives a necessary aggregate equation from conservation; it does not replace
those guarantees.

The derivation uses an accounting-row model of the composed effect plan from
`compose_zdex_atomic_buyback_route_shadow_v2`. Two facts about its modeled
shape drive it:

* the acquisition leg debits the pool's ZDEX custody row and credits nothing,
  because the occurrence burn port is a flow identity and never receives a
  state-bearing effect row; and
* the burn row of the Tokenomics leg is the only plan row that moves ZDEX
  supply, and it moves no owned ZDEX.

Under the refinement that `refine_zdex_atomic_buyback_route_state_v2` performs
(exact per-table effect/state deltas, exact supply projection, and per-asset
owned-total equals supply-total before and after), those two facts force the
burned amount to equal the acquired amount. `conservation_forces_exact_burn`
is that derivation: `purchased` and `burned` enter as independent variables and
the conclusion is an equation, not a hypothesis.

Two limits of the same argument are proved as well, because they say exactly
where the conservation identity stops being sufficient:

* the modeled accounting rows mention no occurrence burn port. Per-asset totals
  and the presence of row principals therefore do not establish the
  acquisition-to-burn occurrence binding; and
* conservation is preserved when part of the acquired ZDEX is diverted to an
  unrelated principal, so it does not establish authorized ownership.

The runtime effect plan also retains `occurrence_consumptions`, which this row
model omits. Receipt, terminal, and occurrence checks remain separate runtime
obligations; the theorem makes no claim that occurrence data is absent there.

## Modeling boundary

State tables are modeled as ledgers of `(key, amount)` rows and the projector
as append, matching `_project_amount_table_v1` and `_project_supplies_v1` up to
the sparse canonical form. `assetTotal_merge_same_key` and
`assetTotal_drop_zero_row` prove that the two steps producing that canonical
form (summing rows that share a key, deleting a zero row) leave every per-asset
total unchanged, so the append model computes the same totals the runtime does.

## Nonclaims

This file proves no canonical-byte encoding, no hash injectivity, no
Python/Rust refinement, no receipt cryptography, no RISC0 validity, no lane
release admission, no durable publication, and no production authority. It does
not prove that the runtime composer always produces the modeled plan shape;
`tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py` compares a finite
runtime corpus. Occurrence and owner binding remain separate obligations.
-/

namespace Proofs.ZDEXAcquisitionBurnOccurrenceV2

/-! ## Vocabulary -/

abbrev Asset := Nat
abbrev Domain := Nat

/-- Principals reachable on the ZDEX or quote asset in this route. The burn port
is occurrence-indexed, matching `zdex_occurrence_burn_port_v1`. -/
inductive Principal where
  | poolReserve (poolId : Nat) (asset : Asset)
  | occurrenceBurnPort (profileRoot routeReleaseId occurrenceId : Nat)
  | zdexSupply
  | feeIngress
  | feeBuyback
  | feeSink (tag : Nat)
  | feeResidue
  | unbound (tag : Nat)
  deriving DecidableEq, Repr

structure Key where
  principal : Principal
  asset : Asset
  domain : Domain
  deriving DecidableEq, Repr

inductive Kind where
  | accountMovement | custody | reserve | liability | issue | burn | feeAllocation
  deriving DecidableEq, Repr

/-- `balances`, `custody` and `reserves` are the tables folded into the owned
total by `_amount_totals_by_asset_v1`. -/
def Kind.owned : Kind → Bool
  | .accountMovement | .custody | .reserve => true
  | _ => false

/-- `_effect_supply_delta_rows_v1` moves supply from issue and burn rows only. -/
def Kind.supplyBearing : Kind → Bool
  | .issue | .burn => true
  | _ => false

structure Row where
  kind : Kind
  key : Key
  delta : Int
  deriving DecidableEq, Repr

abbrev Plan := List Row

structure AmountRow where
  key : Key
  amount : Int
  deriving DecidableEq, Repr

abbrev Ledger := List AmountRow

/-! ## Per-asset aggregates -/

def ledgerContribution (asset : Asset) (row : AmountRow) : Int :=
  if row.key.asset = asset then row.amount else 0

def assetTotal (asset : Asset) (ledger : Ledger) : Int :=
  (ledger.map (ledgerContribution asset)).sum

def ownedContribution (asset : Asset) (row : Row) : Int :=
  if row.kind.owned = true ∧ row.key.asset = asset then row.delta else 0

def supplyContribution (asset : Asset) (row : Row) : Int :=
  if row.kind.supplyBearing = true ∧ row.key.asset = asset then row.delta else 0

def ownedDelta (asset : Asset) (plan : Plan) : Int :=
  (plan.map (ownedContribution asset)).sum

def supplyDelta (asset : Asset) (plan : Plan) : Int :=
  (plan.map (supplyContribution asset)).sum

def keyDelta (key : Key) (plan : Plan) : Int :=
  (plan.map (fun row => if row.key = key then row.delta else 0)).sum

def mentionsPrincipal (principal : Principal) (plan : Plan) : Bool :=
  plan.any (fun row => row.key.principal == principal)

/-! ## The sparse canonical form does not move any per-asset total -/

/-- Merging two rows that share a key, as the runtime dictionary does, leaves
every per-asset total unchanged. -/
theorem assetTotal_merge_same_key
    (asset : Asset) (key : Key) (left right : Int) (rest : Ledger) :
    assetTotal asset (⟨key, left⟩ :: ⟨key, right⟩ :: rest)
      = assetTotal asset (⟨key, left + right⟩ :: rest) := by
  simp only [assetTotal, List.map_cons, List.sum_cons, ledgerContribution]
  split <;> omega

/-- Deleting a zero row, as the sparse canonical form does, leaves every
per-asset total unchanged. -/
theorem assetTotal_drop_zero_row (asset : Asset) (key : Key) (rest : Ledger) :
    assetTotal asset (⟨key, 0⟩ :: rest) = assetTotal asset rest := by
  simp only [assetTotal, List.map_cons, List.sum_cons, ledgerContribution]
  split <;> omega

/-! ## Projection of one effect plan into the modeled tables -/

def ownedProjection : Plan → Ledger
  | [] => []
  | row :: rest =>
      if row.kind.owned = true then ⟨row.key, row.delta⟩ :: ownedProjection rest
      else ownedProjection rest

def supplyProjection : Plan → Ledger
  | [] => []
  | row :: rest =>
      if row.kind.supplyBearing = true then ⟨row.key, row.delta⟩ :: supplyProjection rest
      else supplyProjection rest

theorem assetTotal_append (asset : Asset) (left right : Ledger) :
    assetTotal asset (left ++ right) = assetTotal asset left + assetTotal asset right := by
  unfold assetTotal
  induction left with
  | nil => simp
  | cons _ _ ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [ih]
      omega

theorem ownedDelta_append (asset : Asset) (left right : Plan) :
    ownedDelta asset (left ++ right) = ownedDelta asset left + ownedDelta asset right := by
  unfold ownedDelta
  induction left with
  | nil => simp
  | cons _ _ ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [ih]
      omega

theorem supplyDelta_append (asset : Asset) (left right : Plan) :
    supplyDelta asset (left ++ right) = supplyDelta asset left + supplyDelta asset right := by
  unfold supplyDelta
  induction left with
  | nil => simp
  | cons _ _ ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [ih]
      omega

theorem assetTotal_ownedProjection (asset : Asset) (plan : Plan) :
    assetTotal asset (ownedProjection plan) = ownedDelta asset plan := by
  induction plan with
  | nil => rfl
  | cons row rest ih =>
      by_cases hKind : row.kind.owned = true
      · by_cases hAsset : row.key.asset = asset
        · simp [ownedProjection, assetTotal, ownedDelta, ledgerContribution,
            ownedContribution, hKind, hAsset] at *
          omega
        · simp [ownedProjection, assetTotal, ownedDelta, ledgerContribution,
            ownedContribution, hKind, hAsset] at *
          omega
      · simp [ownedProjection, assetTotal, ownedDelta, ownedContribution, hKind] at *
        omega

theorem assetTotal_supplyProjection (asset : Asset) (plan : Plan) :
    assetTotal asset (supplyProjection plan) = supplyDelta asset plan := by
  induction plan with
  | nil => rfl
  | cons row rest ih =>
      by_cases hKind : row.kind.supplyBearing = true
      · by_cases hAsset : row.key.asset = asset
        · simp [supplyProjection, assetTotal, supplyDelta, ledgerContribution,
            supplyContribution, hKind, hAsset] at *
          omega
        · simp [supplyProjection, assetTotal, supplyDelta, ledgerContribution,
            supplyContribution, hKind, hAsset] at *
          omega
      · simp [supplyProjection, assetTotal, supplyDelta, supplyContribution, hKind] at *
        omega

/-! ## Global totals and the conservation obligation -/

structure GlobalTotals where
  ownedLedger : Ledger
  supplyLedger : Ledger
  deriving DecidableEq, Repr

def GlobalTotals.owned (state : GlobalTotals) (asset : Asset) : Int :=
  assetTotal asset state.ownedLedger

def GlobalTotals.supply (state : GlobalTotals) (asset : Asset) : Int :=
  assetTotal asset state.supplyLedger

def project (state : GlobalTotals) (plan : Plan) : GlobalTotals where
  ownedLedger := state.ownedLedger ++ ownedProjection plan
  supplyLedger := state.supplyLedger ++ supplyProjection plan

/-- `_require_conservation_refinement_v1` requires this on the pre-state and on
the post-state, for every asset present in either. -/
def OwnedMatchesSupply (state : GlobalTotals) (asset : Asset) : Prop :=
  state.owned asset = state.supply asset

theorem project_owned (state : GlobalTotals) (plan : Plan) (asset : Asset) :
    (project state plan).owned asset = state.owned asset + ownedDelta asset plan := by
  simp [project, GlobalTotals.owned, assetTotal_append, assetTotal_ownedProjection]

theorem project_supply (state : GlobalTotals) (plan : Plan) (asset : Asset) :
    (project state plan).supply asset = state.supply asset + supplyDelta asset plan := by
  simp [project, GlobalTotals.supply, assetTotal_append, assetTotal_supplyProjection]

/-- Refining a plan against states that both satisfy owned-equals-supply forces
the plan's own owned and supply movements to agree on every asset. -/
theorem conservation_forces_plan_balance
    (state : GlobalTotals) (plan : Plan) (asset : Asset)
    (hPre : OwnedMatchesSupply state asset)
    (hPost : OwnedMatchesSupply (project state plan) asset) :
    ownedDelta asset plan = supplyDelta asset plan := by
  unfold OwnedMatchesSupply at hPre hPost
  rw [project_owned, project_supply] at hPost
  omega

/-! ## The derived acquisition-to-burn identity -/

/--
The missing link. `purchased` and `burned` are independent variables: nothing
relates them except the two shape facts about the composed plan and the
refinement obligation. The equality is the conclusion.
-/
theorem conservation_forces_exact_burn
    (state : GlobalTotals) (plan : Plan) (asset : Asset) (purchased burned : Nat)
    (hAcquired : ownedDelta asset plan = -(purchased : Int))
    (hBurned : supplyDelta asset plan = -(burned : Int))
    (hPre : OwnedMatchesSupply state asset)
    (hPost : OwnedMatchesSupply (project state plan) asset) :
    purchased = burned := by
  have hBalance := conservation_forces_plan_balance state plan asset hPre hPost
  omega

/-- Contrapositive control: a plan that burns an amount other than the acquired
amount cannot be refined against any conserving pre-state. -/
theorem mismatched_burn_breaks_conservation
    (state : GlobalTotals) (plan : Plan) (asset : Asset) (purchased burned : Nat)
    (hAcquired : ownedDelta asset plan = -(purchased : Int))
    (hBurned : supplyDelta asset plan = -(burned : Int))
    (hPre : OwnedMatchesSupply state asset)
    (hDifferent : purchased ≠ burned) :
    ¬ OwnedMatchesSupply (project state plan) asset := by
  intro hPost
  exact hDifferent (conservation_forces_exact_burn state plan asset purchased burned
    hAcquired hBurned hPre hPost)

/-- The acquisition leg cannot be committed on its own. Removing the burn row
removes the only supply movement, so a positive acquisition can never reach a
conserving post-state. Atomicity here is structural, not procedural. -/
theorem acquisition_without_burn_is_unrefinable
    (state : GlobalTotals) (plan : Plan) (asset : Asset) (purchased : Nat)
    (hPositive : 0 < purchased)
    (hAcquired : ownedDelta asset plan = -(purchased : Int))
    (hNoSupplyMovement : supplyDelta asset plan = 0)
    (hPre : OwnedMatchesSupply state asset) :
    ¬ OwnedMatchesSupply (project state plan) asset := by
  intro hPost
  have hBalance := conservation_forces_plan_balance state plan asset hPre hPost
  omega

/-! ## The composed route plan -/

def quoteAsset : Asset := 1
def zdexAsset : Asset := 2
def ammPoolDomain : Domain := 1
def protocolSupplyDomain : Domain := 2
def protocolBuybackDomain : Domain := 3
def feeIngressDomain : Domain := 4
def feeSinkDomain : Domain := 5
def feeResidueDomain : Domain := 6

def poolQuoteKey (poolId : Nat) : Key :=
  ⟨.poolReserve poolId quoteAsset, quoteAsset, ammPoolDomain⟩

def poolZdexKey (poolId : Nat) : Key :=
  ⟨.poolReserve poolId zdexAsset, zdexAsset, ammPoolDomain⟩

def zdexSupplyKey : Key := ⟨.zdexSupply, zdexAsset, protocolSupplyDomain⟩
def feeIngressKey : Key := ⟨.feeIngress, quoteAsset, feeIngressDomain⟩
def buybackReserveKey : Key := ⟨.feeBuyback, quoteAsset, protocolBuybackDomain⟩
def feeSinkKey (tag : Nat) : Key := ⟨.feeSink tag, quoteAsset, feeSinkDomain⟩
def feeResidueKey : Key := ⟨.feeResidue, quoteAsset, feeResidueDomain⟩

/-- The Spot lane after `_materialize_spot_custody_v2`: quote into the pool and
ZDEX out of the pool. The occurrence burn port receives no row. -/
def acquisitionLeg (poolId gross purchased : Nat) : Plan :=
  [ ⟨.custody, poolQuoteKey poolId, (gross : Int)⟩,
    ⟨.custody, poolZdexKey poolId, -(purchased : Int)⟩ ]

/-- The Tokenomics lane after `_materialize_fee_allocations_v2`: the fee split
with its custody mirrors, the reserve spend, and the ZDEX burn. -/
def burnLeg (burned fee allocation otherAllocations residue spend tag : Nat) : Plan :=
  [ ⟨.custody, feeIngressKey, -(fee : Int)⟩,
    ⟨.feeAllocation, buybackReserveKey, (allocation : Int)⟩,
    ⟨.custody, buybackReserveKey, (allocation : Int) - (spend : Int)⟩,
    ⟨.feeAllocation, feeSinkKey tag, (otherAllocations : Int)⟩,
    ⟨.custody, feeSinkKey tag, (otherAllocations : Int)⟩,
    ⟨.reserve, feeResidueKey, (residue : Int)⟩,
    ⟨.burn, zdexSupplyKey, -(burned : Int)⟩ ]

def routePlan (poolId gross purchased burned fee allocation otherAllocations
    residue spend tag : Nat) : Plan :=
  acquisitionLeg poolId gross purchased
    ++ burnLeg burned fee allocation otherAllocations residue spend tag

/-! ### The two lanes move ZDEX disjointly

The acquisition lane carries the whole ZDEX owned movement and no supply
movement; the burn lane carries the whole ZDEX supply movement and no owned
movement. Neither lane can substitute for the other. -/

theorem acquisition_leg_owned_zdex (poolId gross purchased : Nat) :
    ownedDelta zdexAsset (acquisitionLeg poolId gross purchased)
      = -(purchased : Int) := by
  simp [acquisitionLeg, ownedDelta, ownedContribution, poolQuoteKey, poolZdexKey,
    quoteAsset, zdexAsset, Kind.owned]

theorem acquisition_leg_supply_zdex (poolId gross purchased : Nat) :
    supplyDelta zdexAsset (acquisitionLeg poolId gross purchased) = 0 := by
  simp [acquisitionLeg, supplyDelta, supplyContribution, poolQuoteKey, poolZdexKey,
    quoteAsset, zdexAsset, Kind.supplyBearing]

theorem burn_leg_owned_zdex (burned fee allocation otherAllocations residue spend
    tag : Nat) :
    ownedDelta zdexAsset
        (burnLeg burned fee allocation otherAllocations residue spend tag) = 0 := by
  simp [burnLeg, ownedDelta, ownedContribution, zdexSupplyKey, feeIngressKey,
    buybackReserveKey, feeSinkKey, feeResidueKey, quoteAsset, zdexAsset, Kind.owned]

theorem burn_leg_supply_zdex (burned fee allocation otherAllocations residue spend
    tag : Nat) :
    supplyDelta zdexAsset
        (burnLeg burned fee allocation otherAllocations residue spend tag)
      = -(burned : Int) := by
  simp [burnLeg, supplyDelta, supplyContribution, zdexSupplyKey, feeIngressKey,
    buybackReserveKey, feeSinkKey, feeResidueKey, quoteAsset, zdexAsset,
    Kind.supplyBearing]

theorem route_owned_zdex (poolId gross purchased burned fee allocation
    otherAllocations residue spend tag : Nat) :
    ownedDelta zdexAsset
        (routePlan poolId gross purchased burned fee allocation otherAllocations
          residue spend tag)
      = -(purchased : Int) := by
  unfold routePlan
  rw [ownedDelta_append, acquisition_leg_owned_zdex, burn_leg_owned_zdex]
  omega

theorem route_supply_zdex (poolId gross purchased burned fee allocation
    otherAllocations residue spend tag : Nat) :
    supplyDelta zdexAsset
        (routePlan poolId gross purchased burned fee allocation otherAllocations
          residue spend tag)
      = -(burned : Int) := by
  unfold routePlan
  rw [supplyDelta_append, acquisition_leg_supply_zdex, burn_leg_supply_zdex]
  omega

/-- The route instance of the derived identity. -/
theorem route_conservation_forces_exact_burn
    (state : GlobalTotals)
    (poolId gross purchased burned fee allocation otherAllocations residue spend
      tag : Nat)
    (hPre : OwnedMatchesSupply state zdexAsset)
    (hPost : OwnedMatchesSupply
      (project state (routePlan poolId gross purchased burned fee allocation
        otherAllocations residue spend tag)) zdexAsset) :
    purchased = burned :=
  conservation_forces_exact_burn state
    (routePlan poolId gross purchased burned fee allocation otherAllocations
      residue spend tag)
    zdexAsset purchased burned
    (route_owned_zdex poolId gross purchased burned fee allocation otherAllocations
      residue spend tag)
    (route_supply_zdex poolId gross purchased burned fee allocation otherAllocations
      residue spend tag)
    hPre hPost

/-- The route instance of structural atomicity. -/
theorem route_acquisition_leg_alone_is_unrefinable
    (state : GlobalTotals) (poolId gross purchased : Nat)
    (hPositive : 0 < purchased)
    (hPre : OwnedMatchesSupply state zdexAsset) :
    ¬ OwnedMatchesSupply (project state (acquisitionLeg poolId gross purchased))
      zdexAsset :=
  acquisition_without_burn_is_unrefinable state
    (acquisitionLeg poolId gross purchased) zdexAsset purchased hPositive
    (acquisition_leg_owned_zdex poolId gross purchased)
    (acquisition_leg_supply_zdex poolId gross purchased)
    hPre

/-! ## Where the conservation argument stops -/

/--
The modeled accounting rows carry no row addressed to an occurrence burn port,
while distinct occurrences have distinct burn ports. This row-principal
observation cannot establish the acquisition-to-burn occurrence binding. The
runtime plan's occurrence consumption data is outside this row model.
-/
theorem conservation_cannot_bind_the_acquisition_occurrence
    (poolId gross purchased burned fee allocation otherAllocations residue spend
      tag profileRoot routeReleaseId leftOccurrence rightOccurrence : Nat)
    (hDistinct : leftOccurrence ≠ rightOccurrence) :
    Principal.occurrenceBurnPort profileRoot routeReleaseId leftOccurrence
        ≠ Principal.occurrenceBurnPort profileRoot routeReleaseId rightOccurrence
      ∧ mentionsPrincipal
          (.occurrenceBurnPort profileRoot routeReleaseId leftOccurrence)
          (routePlan poolId gross purchased burned fee allocation otherAllocations
            residue spend tag) = false
      ∧ mentionsPrincipal
          (.occurrenceBurnPort profileRoot routeReleaseId rightOccurrence)
          (routePlan poolId gross purchased burned fee allocation otherAllocations
            residue spend tag) = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hDistinct]
  · simp [mentionsPrincipal, routePlan, acquisitionLeg, burnLeg, poolQuoteKey,
      poolZdexKey, zdexSupplyKey, feeIngressKey, buybackReserveKey, feeSinkKey,
      feeResidueKey]
  · simp [mentionsPrincipal, routePlan, acquisitionLeg, burnLeg, poolQuoteKey,
      poolZdexKey, zdexSupplyKey, feeIngressKey, buybackReserveKey, feeSinkKey,
      feeResidueKey]

/-- A plan that debits the governed pool by `purchased + diverted` and credits
`diverted` to an unrelated principal. -/
def divertedRoutePlan (poolId gross purchased burned fee allocation
    otherAllocations residue spend tag diverted thief : Nat) : Plan :=
  [ ⟨.custody, poolQuoteKey poolId, (gross : Int)⟩,
    ⟨.custody, poolZdexKey poolId, -((purchased : Int) + (diverted : Int))⟩,
    ⟨.custody, ⟨.unbound thief, zdexAsset, ammPoolDomain⟩, (diverted : Int)⟩ ]
    ++ burnLeg burned fee allocation otherAllocations residue spend tag

/--
Conservation does not pin the owner of the acquisition. The diverted plan has
exactly the same owned and supply movements on ZDEX as the honest plan, so it
satisfies the same refinement obligation, yet the governed pool loses
`purchased + diverted` while only `purchased` is burned. Ownership of the
acquisition is bound by the authenticated Spot leaf effects alone.
-/
theorem conservation_admits_owner_diversion
    (poolId gross purchased burned fee allocation otherAllocations residue spend
      tag diverted thief : Nat) :
    ownedDelta zdexAsset
        (divertedRoutePlan poolId gross purchased burned fee allocation
          otherAllocations residue spend tag diverted thief)
        = ownedDelta zdexAsset
          (routePlan poolId gross purchased burned fee allocation otherAllocations
            residue spend tag)
      ∧ supplyDelta zdexAsset
          (divertedRoutePlan poolId gross purchased burned fee allocation
            otherAllocations residue spend tag diverted thief)
        = supplyDelta zdexAsset
          (routePlan poolId gross purchased burned fee allocation otherAllocations
            residue spend tag)
      ∧ keyDelta (poolZdexKey poolId)
          (divertedRoutePlan poolId gross purchased burned fee allocation
            otherAllocations residue spend tag diverted thief)
        = -((purchased : Int) + (diverted : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [divertedRoutePlan, routePlan, acquisitionLeg, burnLeg, ownedDelta,
      ownedContribution, poolQuoteKey, poolZdexKey, zdexSupplyKey, feeIngressKey,
      buybackReserveKey, feeSinkKey, feeResidueKey, quoteAsset, zdexAsset,
      Kind.owned]
    omega
  · simp [divertedRoutePlan, routePlan, acquisitionLeg, burnLeg, supplyDelta,
      supplyContribution, poolQuoteKey, poolZdexKey, zdexSupplyKey, feeIngressKey,
      buybackReserveKey, feeSinkKey, feeResidueKey, quoteAsset, zdexAsset,
      Kind.supplyBearing]
  · simp [divertedRoutePlan, burnLeg, keyDelta, poolQuoteKey, poolZdexKey,
      zdexSupplyKey, feeIngressKey, buybackReserveKey, feeSinkKey, feeResidueKey,
      quoteAsset, zdexAsset, ammPoolDomain, protocolSupplyDomain,
      protocolBuybackDomain, feeIngressDomain, feeSinkDomain, feeResidueDomain]

/-! ## Non-vacuity -/

instance decidableOwnedMatchesSupply (state : GlobalTotals) (asset : Asset) :
    Decidable (OwnedMatchesSupply state asset) := by
  unfold OwnedMatchesSupply
  infer_instance

/-- The amounts of the running SHADOW route fixture. The four fee sinks of the
live plan are collapsed into one sink carrying their total. -/
def witnessPoolId : Nat := 7
def witnessGross : Nat := 125
def witnessPurchased : Nat := 111
def witnessFee : Nat := 125
def witnessAllocation : Nat := 25
def witnessOtherAllocations : Nat := 67
def witnessResidue : Nat := 33
def witnessSpend : Nat := 125
def witnessTag : Nat := 0

def witnessPlan (burned : Nat) : Plan :=
  routePlan witnessPoolId witnessGross witnessPurchased burned witnessFee
    witnessAllocation witnessOtherAllocations witnessResidue witnessSpend witnessTag

def witnessState : GlobalTotals where
  ownedLedger :=
    [ ⟨feeIngressKey, 125⟩,
      ⟨poolQuoteKey witnessPoolId, 1000⟩,
      ⟨buybackReserveKey, 100⟩,
      ⟨poolZdexKey witnessPoolId, 1000⟩ ]
  supplyLedger := [ ⟨feeIngressKey, 1225⟩, ⟨zdexSupplyKey, 1000⟩ ]

theorem witness_state_conserves :
    OwnedMatchesSupply witnessState quoteAsset ∧
      OwnedMatchesSupply witnessState zdexAsset := by
  decide

/-- The honest occurrence is reachable: both assets still conserve afterwards,
the quote asset is unmoved by the fee split, and ZDEX supply falls by the
acquired amount. -/
theorem witness_route_is_refinable :
    OwnedMatchesSupply (project witnessState (witnessPlan 111)) quoteAsset ∧
    OwnedMatchesSupply (project witnessState (witnessPlan 111)) zdexAsset ∧
    ownedDelta zdexAsset (witnessPlan 111) = -111 ∧
    supplyDelta zdexAsset (witnessPlan 111) = -111 ∧
    ownedDelta quoteAsset (witnessPlan 111) = 0 ∧
    (project witnessState (witnessPlan 111)).supply zdexAsset = 889 := by
  decide

/--
With the acquisition fixed at 111 atoms, the refinement obligation pins the
burn to the single value 111: every other burn amount, above or below, fails.
The forward direction is the derived identity and the reverse direction is the
reachable witness, so the solution set is exactly one point.
-/
theorem witness_burn_is_pinned (burned : Nat) :
    OwnedMatchesSupply (project witnessState (witnessPlan burned)) zdexAsset
      ↔ burned = witnessPurchased := by
  constructor
  · intro hPost
    exact (route_conservation_forces_exact_burn witnessState witnessPoolId
      witnessGross witnessPurchased burned witnessFee witnessAllocation
      witnessOtherAllocations witnessResidue witnessSpend witnessTag
      witness_state_conserves.2 hPost).symm
  · intro hEqual
    subst hEqual
    decide

end Proofs.ZDEXAcquisitionBurnOccurrenceV2
