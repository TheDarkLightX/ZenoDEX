import Proofs.CheckedEconomicAggregationV1
import Proofs.GlobalEconomicStateRefinementV2

/-!
Checked accounting composition for an ordered list of route effect plans.
`TableChain` requires the existing `ExactEconomicTables` relation at every
adjacent state. Its endpoints are actual `GlobalState` values, and its rows are
actual `EconomicEffectRow` values. The adapter retains all four key fields.

The universal result is conditional on each route's table correctness. It
does not certify that a route verifier establishes that premise. No height,
receipt, replay, supply, conservation, lane-write, or publication claim is
made. In particular, several commands in one epoch need not each advance
height. The checked loop models the row stage of the Python epoch composer;
finite executable comparisons provide evidence about that runtime connection.
Function-valued totals do not establish Python's sorted, unique, zero-eliding
tuple representation or whole-plan acceptance. The model has no 1..64 command
arity or metadata admission guard; its arbitrary finite-list theorem includes
the lists admitted by those separate runtime guards.
-/
namespace Proofs.CheckedEpochEconomicTablesV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open CheckedEconomicAggregationV1

def encodeKind : EffectKind → Kind
  | .accountMovement => .accountMovement
  | .issue => .issue
  | .burn => .burn
  | .custody => .custody
  | .liability => .liability
  | .reserve => .reserve
  | .feeAllocation => .feeAllocation
  | .reward => .reward
  | .slash => .slash

def encodeKey (kind : EffectKind) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) : Key :=
  ⟨encodeKind kind, owner, asset, domain⟩

def encodeRow (row : EconomicEffectRow) : Row :=
  ⟨encodeKey row.kind row.principal row.asset row.custodyDomain, row.deltaAtoms⟩

def encodeRows (rows : List EconomicEffectRow) : List Row :=
  rows.map encodeRow

/-- Both route order and the order of rows inside a route are retained. -/
def orderedRows : List EffectPlan → List Row
  | [] => []
  | plan :: plans => encodeRows plan.rows ++ orderedRows plans

def checkedEpoch (bounds : Bounds) (plans : List EffectPlan) :
    Except Reject Totals :=
  checkedFold bounds empty (orderedRows plans)

inductive Table where
  | balances | custody | liabilities | reserves
  deriving DecidableEq, Repr

def tableKind : Table → EffectKind
  | .balances => .accountMovement
  | .custody => .custody
  | .liabilities => .liability
  | .reserves => .reserve

def tableRows : Table → GlobalState → List AmountRow
  | .balances, state => state.balances
  | .custody, state => state.custody
  | .liabilities, state => state.liabilities
  | .reserves, state => state.reserves

/-- The sole economic premise is the existing per-route table relation. -/
inductive TableChain : GlobalState → List EffectPlan → GlobalState → Prop
  | nil (state : GlobalState) : TableChain state [] state
  | cons {pre middle post : GlobalState} {plan : EffectPlan} {plans : List EffectPlan}
      (route : ExactEconomicTables pre middle plan)
      (rest : TableChain middle plans post) : TableChain pre (plan :: plans) post

theorem encodeKind_eq_iff (left right : EffectKind) :
    encodeKind left = encodeKind right ↔ left = right := by
  cases left <;> cases right <;> decide

theorem encodeKey_eq_iff (leftKind rightKind : EffectKind)
    (leftOwner rightOwner : Principal) (leftAsset rightAsset : Asset)
    (leftDomain rightDomain : AccountingLocation) :
    encodeKey leftKind leftOwner leftAsset leftDomain =
        encodeKey rightKind rightOwner rightAsset rightDomain ↔
      leftKind = rightKind ∧ leftOwner = rightOwner ∧ leftAsset = rightAsset ∧
        leftDomain = rightDomain := by
  simp only [encodeKey, Key.mk.injEq, encodeKind_eq_iff]

theorem encoded_keyed_sum (rows : List EconomicEffectRow) (kind : EffectKind)
    (owner : Principal) (asset : Asset) (domain : AccountingLocation) :
    keyedSum (encodeKey kind owner asset domain) (encodeRows rows) =
      (rows.map fun row =>
        if row.kind = kind ∧ row.principal = owner ∧ row.asset = asset ∧
            row.custodyDomain = domain then row.deltaAtoms else 0).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [encodeRows, List.map_cons, keyedSum, encodeRow,
        encodeKey_eq_iff, List.sum_cons] at *
      rw [ih]

theorem encoded_plan_effect (plan : EffectPlan) (kind : EffectKind)
    (owner : Principal) (asset : Asset) (domain : AccountingLocation) :
    keyedSum (encodeKey kind owner asset domain) (encodeRows plan.rows) =
      effectFor kind plan owner asset domain :=
  encoded_keyed_sum plan.rows kind owner asset domain

theorem orderedRows_append (left right : List EffectPlan) :
    orderedRows (left ++ right) = orderedRows left ++ orderedRows right := by
  induction left with
  | nil => rfl
  | cons plan plans ih => simp only [List.cons_append, orderedRows, ih, List.append_assoc]

theorem exactEconomicTables_iff (pre post : GlobalState) (plan : EffectPlan) :
    ExactEconomicTables pre post plan ↔
      ∀ table, ExactTableEffect (tableKind table)
        (tableRows table pre) (tableRows table post) plan := by
  constructor
  · intro exact table
    cases table with
    | balances => exact exact.1
    | custody => exact exact.2.1
    | liabilities => exact exact.2.2.1
    | reserves => exact exact.2.2.2
  · intro exact
    exact ⟨exact .balances, exact .custody, exact .liabilities, exact .reserves⟩

theorem tableChain_append {pre middle post : GlobalState} {left right : List EffectPlan}
    (first : TableChain pre left middle) (second : TableChain middle right post) :
    TableChain pre (left ++ right) post := by
  induction first with
  | nil => exact second
  | cons route rest ih => exact .cons route (ih second)

/-- Every owner/asset/domain coordinate telescopes independently in all four tables. -/
theorem tableChain_telescopes {pre post : GlobalState} {plans : List EffectPlan}
    (chain : TableChain pre plans post) (table : Table) (owner : Principal)
    (asset : Asset) (domain : AccountingLocation) :
    amountAt (tableRows table post) owner asset domain -
        amountAt (tableRows table pre) owner asset domain =
      keyedSum (encodeKey (tableKind table) owner asset domain)
        (orderedRows plans) := by
  induction chain with
  | nil => simp only [orderedRows, keyedSum, Int.sub_self]
  | @cons pre middle post plan plans route rest ih =>
      have step := (exactEconomicTables_iff pre middle plan).mp route table owner asset domain
      rw [orderedRows, keyedSum_append, encoded_plan_effect]
      omega

theorem checkedFold_append (bounds : Bounds) (initial : Totals)
    (left right : List Row) :
    checkedFold bounds initial (left ++ right) =
      (checkedFold bounds initial left).bind
        (fun middle => checkedFold bounds middle right) := by
  induction left generalizing initial with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.cons_append, checkedFold]
      split <;> simp_all only [Except.bind]

theorem checkedEpoch_success_iff (bounds : Bounds) (plans : List EffectPlan) :
    (∃ output, checkedEpoch bounds plans = .ok output) ↔
      PrefixFits bounds empty (orderedRows plans) :=
  checkedFold_success_iff bounds empty (orderedRows plans)

theorem checkedEpoch_reject_iff (bounds : Bounds) (plans : List EffectPlan) :
    checkedEpoch bounds plans = .error .signedAggregationBounds ↔
      ¬PrefixFits bounds empty (orderedRows plans) :=
  checkedFold_reject_iff bounds empty (orderedRows plans)

theorem successful_epoch_complete_keys (bounds : Bounds)
    (plans : List EffectPlan) (output : Totals)
    (accepted : checkedEpoch bounds plans = .ok output) (key : Key) :
    output key = keyedSum key (orderedRows plans) :=
  successful_complete_keyed_sums bounds (orderedRows plans) output accepted key

/-- Table correctness follows from per-route correctness and the actual accepted fold. -/
theorem successful_epoch_exact_tables (bounds : Bounds)
    {pre post : GlobalState} {plans : List EffectPlan} (output : Totals)
    (chain : TableChain pre plans post)
    (accepted : checkedEpoch bounds plans = .ok output)
    (table : Table) (owner : Principal) (asset : Asset) (domain : AccountingLocation) :
    amountAt (tableRows table post) owner asset domain -
        amountAt (tableRows table pre) owner asset domain =
      output (encodeKey (tableKind table) owner asset domain) := by
  rw [successful_epoch_complete_keys bounds plans output accepted]
  exact tableChain_telescopes chain table owner asset domain

/-- Checked composition exists with exact endpoint tables exactly when all row prefixes fit. -/
theorem checked_epoch_table_composition_iff (bounds : Bounds)
    {pre post : GlobalState} {plans : List EffectPlan} (chain : TableChain pre plans post) :
    (∃ output, checkedEpoch bounds plans = .ok output ∧
      ∀ table owner asset domain,
        amountAt (tableRows table post) owner asset domain -
            amountAt (tableRows table pre) owner asset domain =
          output (encodeKey (tableKind table) owner asset domain)) ↔
      PrefixFits bounds empty (orderedRows plans) := by
  constructor
  · rintro ⟨output, accepted, _⟩
    exact (checkedEpoch_success_iff bounds plans).mp ⟨output, accepted⟩
  · intro fits
    obtain ⟨output, accepted⟩ := (checkedEpoch_success_iff bounds plans).mpr fits
    exact ⟨output, accepted, successful_epoch_exact_tables bounds output chain accepted⟩

/-- Splitting at any command boundary recovers the actual accepted accumulator. -/
theorem checked_ordered_prefix_equation (bounds : Bounds)
    (before after : List EffectPlan) (output : Totals)
    (accepted : checkedEpoch bounds (before ++ after) = .ok output) :
    ∃ middle,
      checkedEpoch bounds before = .ok middle ∧
      checkedFold bounds middle (orderedRows after) = .ok output ∧
      ∀ key, middle key = keyedSum key (orderedRows before) ∧
        output key = middle key + keyedSum key (orderedRows after) := by
  unfold checkedEpoch at accepted
  rw [orderedRows_append, checkedFold_append] at accepted
  cases prefixResult : checkedFold bounds empty (orderedRows before) with
  | error reason => simp only [prefixResult, Except.bind] at accepted; contradiction
  | ok middle =>
      simp only [prefixResult, Except.bind] at accepted
      refine ⟨middle, prefixResult, accepted, ?_⟩
      intro key
      exact ⟨successful_complete_keyed_sums bounds _ middle prefixResult key,
        ((checkedFold_ok_iff bounds middle _ output).mp accepted).2 key⟩

theorem successful_prefix_exact_tables (bounds : Bounds)
    {pre middle post : GlobalState} {before after : List EffectPlan}
    (output : Totals) (prefixChain : TableChain pre before middle)
    (suffixChain : TableChain middle after post)
    (accepted : checkedEpoch bounds (before ++ after) = .ok output) :
    ∃ prefixOutput,
      checkedEpoch bounds before = .ok prefixOutput ∧
      checkedFold bounds prefixOutput (orderedRows after) = .ok output ∧
      ∀ table owner asset domain,
        amountAt (tableRows table middle) owner asset domain -
            amountAt (tableRows table pre) owner asset domain =
          prefixOutput (encodeKey (tableKind table) owner asset domain) ∧
        amountAt (tableRows table post) owner asset domain -
            amountAt (tableRows table middle) owner asset domain =
          output (encodeKey (tableKind table) owner asset domain) -
            prefixOutput (encodeKey (tableKind table) owner asset domain) := by
  obtain ⟨prefixOutput, prefixAccepted, suffixAccepted, equations⟩ :=
    checked_ordered_prefix_equation bounds before after output accepted
  refine ⟨prefixOutput, prefixAccepted, suffixAccepted, ?_⟩
  intro table owner asset domain
  constructor
  · exact successful_epoch_exact_tables bounds prefixOutput prefixChain prefixAccepted
      table owner asset domain
  · have delta := tableChain_telescopes suffixChain table owner asset domain
    have equation := (equations (encodeKey (tableKind table) owner asset domain)).2
    omega

/-- A row checks its earlier commands plus its earlier rows, without regrouping. -/
theorem successful_within_route_prefix_fits (bounds : Bounds)
    (before after : List EffectPlan) (plan : EffectPlan)
    (rowBefore rowAfter : List EconomicEffectRow) (row : EconomicEffectRow)
    (rowSplit : plan.rows = rowBefore ++ row :: rowAfter) (output : Totals)
    (accepted : checkedEpoch bounds (before ++ plan :: after) = .ok output) :
    Fits bounds
      (keyedSum (encodeRow row).key (orderedRows before) +
        keyedSum (encodeRow row).key (encodeRows rowBefore) + row.deltaAtoms) := by
  have safe := (checkedEpoch_success_iff bounds _).mp ⟨output, accepted⟩
  have splitRows : orderedRows (before ++ plan :: after) =
      (orderedRows before ++ encodeRows rowBefore) ++
        encodeRow row :: (encodeRows rowAfter ++ orderedRows after) := by
    simp only [orderedRows_append, orderedRows, rowSplit, encodeRows, List.map_append,
      List.map_cons, List.cons_append, List.append_assoc]
  have bound := safe (orderedRows before ++ encodeRows rowBefore) (encodeRow row)
    (encodeRows rowAfter ++ orderedRows after) splitRows
  simpa only [empty, Int.zero_add, keyedSum_append, encodeRow]
    using bound

theorem out_of_range_route_prefix_rejects (bounds : Bounds)
    (before after : List EffectPlan) (plan : EffectPlan)
    (rowBefore rowAfter : List EconomicEffectRow) (row : EconomicEffectRow)
    (rowSplit : plan.rows = rowBefore ++ row :: rowAfter)
    (outside : ¬Fits bounds
      (keyedSum (encodeRow row).key (orderedRows before) +
        keyedSum (encodeRow row).key (encodeRows rowBefore) + row.deltaAtoms)) :
    checkedEpoch bounds (before ++ plan :: after) = .error .signedAggregationBounds := by
  cases result : checkedEpoch bounds (before ++ plan :: after) with
  | error reason => cases reason; rfl
  | ok output =>
      exact False.elim (outside (successful_within_route_prefix_fits bounds before after plan
        rowBefore rowAfter row rowSplit output result))

/-!
A concrete chain has positive tables and two commands at the same final height.
It exercises `ExactEconomicTables` only, not a globally admitted, conserved or
authenticated trace: all four tables grow while the static supplies stay fixed.
-/

def exampleState (height : Nat) (amount : Int) : GlobalState :=
  { staticGlobalState with
    height := height
    balances := [⟨"alice", "USD", "vault", amount⟩]
    custody := [⟨"alice", "USD", "vault", 2 * amount⟩]
    liabilities := [⟨"alice", "USD", "vault", 3 * amount⟩]
    reserves := [⟨"alice", "USD", "vault", 4 * amount⟩] }

def examplePlan (delta : Int) : EffectPlan :=
  { EffectPlan.empty with rows :=
    [⟨.accountMovement, "alice", "USD", "vault", delta⟩,
     ⟨.custody, "alice", "USD", "vault", 2 * delta⟩,
     ⟨.liability, "alice", "USD", "vault", 3 * delta⟩,
     ⟨.reserve, "alice", "USD", "vault", 4 * delta⟩] }

theorem example_route_tables (preHeight postHeight : Nat) (preAmount postAmount : Int) :
    ExactEconomicTables (exampleState preHeight preAmount) (exampleState postHeight postAmount)
      (examplePlan (postAmount - preAmount)) := by
  apply (exactEconomicTables_iff _ _ _).mpr
  intro table owner asset domain
  have presentOrAbsent := Classical.em ("alice" = owner ∧ "USD" = asset ∧ "vault" = domain)
  cases table <;> rcases presentOrAbsent with present | present <;>
    simp [tableKind, tableRows, exampleState, examplePlan, amountAt,
      effectFor, present] <;> omega

def exampleOutput : Totals :=
  (orderedRows [examplePlan 3, examplePlan (-2)]).foldl advance empty

theorem positive_tables_same_epoch_example :
    TableChain (exampleState 100 20) [examplePlan 3, examplePlan (-2)] (exampleState 101 21) ∧
    checkedEpoch i128 [examplePlan 3, examplePlan (-2)] = .ok exampleOutput ∧
    exampleOutput (encodeKey .accountMovement "alice" "USD" "vault") = 1 ∧
    exampleOutput (encodeKey .custody "alice" "USD" "vault") = 2 ∧
    exampleOutput (encodeKey .liability "alice" "USD" "vault") = 3 ∧
    exampleOutput (encodeKey .reserve "alice" "USD" "vault") = 4 ∧
    (∀ table, 0 < amountAt (tableRows table (exampleState 100 20)) "alice" "USD" "vault" ∧
      0 < amountAt (tableRows table (exampleState 101 23)) "alice" "USD" "vault" ∧
      0 < amountAt (tableRows table (exampleState 101 21)) "alice" "USD" "vault") := by
  refine ⟨.cons (example_route_tables 100 101 20 23)
    (.cons (example_route_tables 101 101 23 21) (.nil _)), rfl, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro table
  cases table <;> decide

end Proofs.CheckedEpochEconomicTablesV1
