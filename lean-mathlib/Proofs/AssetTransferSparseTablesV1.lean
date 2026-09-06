import Proofs.AssetTransferCustodyCompositionV1
import Proofs.CanonicalEpochEconomicRowsV1

/-!
Constructive sparse accounting projection of the selected-policy V1 transfer.
The existing leaf supplies its guarded, alias-coalesced deltas. A checked
role-ordered update constructs the finite account rows, deletes zeros and
checks the actual 4096-row ceiling. The local balance function is computed
from these source rows; no principal enumeration or exact-table postcondition
is supplied. Other global tables are an explicit frame.

This is an accounting-row projection, not a complete module/route plan. It
does not construct conservation, journal, root, occurrence or receipt fields.
Policy selection, constructor admission and exact-command authentication are
separate boundaries. Only source key uniqueness and positive accounts-domain
u128 balances are needed by the conditional table theorem. Relating the old
leaf's rejection order to runtime additionally uses its existing command,
policy and supply width premises. This model does not perform full input
constructor validation or policy-list lookup. Finite Python comparisons are not universal execution or
compiler refinement. In particular a positive fee allocated to the sender can
pass this leaf while failing the global fee-mirror guard. The custody successor
retains the same movement rows but has separate conservation/release semantics.
-/
namespace Proofs.AssetTransferSparseTablesV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
namespace T
export Proofs.AssetTransferRefinementV1 (Context Policy Command TransferState
  RejectCode Verdict IsU128 StateWellFormed CommandWellFormed u128Max
  delta roleOrder movementRows acceptedEffects transition accepted_iff_all_guards)
end T
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (AmountKey amountKey amountSum
  amountSum_eq_amountAt lookupLast lookupLast_eq_amountAt sortOn sortOn_perm
  mem_sortOn sortOn_ordered)
end C
namespace M
export Proofs.AssetTransferCustodyCompositionV1 (movementDeltaSum
  movementRows_sum_eq_delta_mul_occ delta_mul_occ_roleOrder)
end M

attribute [local instance] lexOrd

def accounts : String := "accounts"
def maxBalanceRows : Nat := 4096
def accountKey (asset owner : String) : C.AmountKey := (owner, asset, accounts)
def balanceWire (row : AmountRow) : String × String := (row.asset, row.owner)

def makeAmount (key : C.AmountKey) (atoms : Int) : AmountRow :=
  ⟨key.1, key.2.1, key.2.2, atoms⟩

def eraseKey (key : C.AmountKey) (rows : List AmountRow) : List AmountRow :=
  rows.filter (fun row => C.amountKey row != key)

def putAmount (key : C.AmountKey) (atoms : Int) (rows : List AmountRow) : List AmountRow :=
  if atoms = 0 then eraseKey key rows
  else makeAmount key atoms :: eraseKey key rows

def Unique (rows : List AmountRow) : Prop := (rows.map C.amountKey).Nodup
def PositiveAccounts (rows : List AmountRow) : Prop :=
  ∀ row ∈ rows, row.custodyDomain = accounts ∧ T.IsU128 row.amountAtoms ∧ row.amountAtoms ≠ 0

def checkedUpdate (rows : List AmountRow) (asset owner : String) (delta : Int) :
    Except T.RejectCode (List AmountRow) :=
  let atoms := C.lookupLast (accountKey asset owner) rows + delta
  if atoms < 0 then .error .insufficientBalance
  else if T.u128Max < atoms then .error .balanceOverflow
  else .ok (putAmount (accountKey asset owner) atoms rows)

def updateRoles (asset : String) (delta : String → Int) :
    List String → List AmountRow → Except T.RejectCode (List AmountRow)
  | [], rows => .ok rows
  | owner :: owners, rows =>
      (checkedUpdate rows asset owner (delta owner)).bind
        (fun next => updateRoles asset delta owners next)

def finishBalances (rows : List AmountRow) : Except T.RejectCode (List AmountRow) :=
  if rows.length > maxBalanceRows then .error .postStateResourceBoundExceeded
  else .ok (C.sortOn balanceWire rows)

structure Input where
  context : T.Context
  moduleReleaseId : String
  policy : T.Policy
  command : T.Command
  pre : GlobalState

def localState (input : Input) : T.TransferState :=
  ⟨input.moduleReleaseId, input.policy,
    fun owner => C.lookupLast (accountKey input.policy.asset owner) input.pre.balances,
    supplyFor input.pre.supplies input.policy.asset⟩

def leaf (input : Input) := T.transition input.context (localState input) input.command

def checkedBalances (input : Input) : Except T.RejectCode (List AmountRow) :=
  (updateRoles input.command.asset (T.delta (localState input) input.command)
    (T.roleOrder (localState input) input.command) input.pre.balances).bind finishBalances

def movementEffects (kind : EffectKind) (asset : String)
    (rows : List Proofs.AssetTransferRefinementV1.MovementRow) : List EconomicEffectRow :=
  rows.map (fun row => ⟨kind, row.principal, asset, accounts, row.deltaAtoms⟩)

def effectWire (row : EconomicEffectRow) : String × String × String × String :=
  (row.kind.code, row.asset, row.principal, row.custodyDomain)

def projectedPlan (input : Input) : EffectPlan :=
  let effects := T.acceptedEffects (localState input) input.command
  let rows := C.sortOn effectWire
    (movementEffects .accountMovement input.command.asset effects.movements ++
     movementEffects .feeAllocation input.command.asset effects.feeAllocations)
  { EffectPlan.empty with rows := rows }

structure Result where
  verdict : T.Verdict
  post : GlobalState
  plan : EffectPlan

def rejected (input : Input) (code : T.RejectCode) : Result :=
  ⟨.rejected code, input.pre, EffectPlan.empty⟩

def step (input : Input) : Result :=
  match (leaf input).verdict with
  | .rejected code => rejected input code
  | .accepted => match checkedBalances input with
      | .error code => rejected input code
      | .ok rows => ⟨.accepted, { input.pre with balances := rows }, projectedPlan input⟩

theorem makeAmount_key (key : C.AmountKey) (atoms : Int) :
    C.amountKey (makeAmount key atoms) = key := by
  rcases key with ⟨owner, asset, domain⟩
  rfl

theorem mem_eraseKey (key : C.AmountKey) (rows : List AmountRow) (row : AmountRow) :
    row ∈ eraseKey key rows ↔ row ∈ rows ∧ C.amountKey row ≠ key := by
  simp only [eraseKey, List.mem_filter, bne_iff_ne]

theorem amountSum_eraseKey (key query : C.AmountKey) (rows : List AmountRow) :
    C.amountSum query (eraseKey key rows) =
      if key = query then 0 else C.amountSum query rows := by
  induction rows with
  | nil => simp only [eraseKey, List.filter_nil, C.amountSum, ite_self]
  | cons row rows ih =>
      by_cases hr : C.amountKey row = key
      · simp only [eraseKey, List.filter_cons, bne_iff_ne,
          if_neg (fun (hn : C.amountKey row ≠ key) => hn hr)]
        change C.amountSum query (eraseKey key rows) = _
        rw [ih]
        by_cases hq : key = query
        · simp only [if_pos hq]
        · simp only [C.amountSum, hr, if_neg hq, Int.zero_add]
      · simp only [eraseKey, List.filter_cons, bne_iff_ne, if_pos hr, C.amountSum]
        change (if C.amountKey row = query then row.amountAtoms else 0) +
          C.amountSum query (eraseKey key rows) = _
        rw [ih]
        by_cases hq : key = query
        · subst query
          simp only [if_neg hr, Int.zero_add]
        · simp only [if_neg hq]

theorem amountSum_putAmount (key query : C.AmountKey) (atoms : Int) (rows : List AmountRow) :
    C.amountSum query (putAmount key atoms rows) =
      if key = query then atoms else C.amountSum query rows := by
  unfold putAmount
  split
  · rename_i zero
    rw [amountSum_eraseKey]
    simp only [zero]
  · simp only [C.amountSum, makeAmount_key, amountSum_eraseKey]
    split <;> simp_all only [makeAmount, Int.add_zero, Int.zero_add]

theorem eraseKey_unique (key : C.AmountKey) (rows : List AmountRow) (unique : Unique rows) :
    Unique (eraseKey key rows) := by
  exact ((List.filter_sublist (l := rows)).map C.amountKey).nodup unique

theorem eraseKey_absent (key : C.AmountKey) (rows : List AmountRow) :
    key ∉ (eraseKey key rows).map C.amountKey := by
  intro member
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  exact (mem_eraseKey key rows row).mp member |>.2 same

theorem putAmount_unique (key : C.AmountKey) (atoms : Int) (rows : List AmountRow)
    (unique : Unique rows) : Unique (putAmount key atoms rows) := by
  unfold putAmount
  split
  · exact eraseKey_unique key rows unique
  · exact List.nodup_cons.mpr ⟨by simpa only [makeAmount_key] using eraseKey_absent key rows,
      eraseKey_unique key rows unique⟩

theorem checkedUpdate_spec {rows out : List AmountRow} {asset owner : String} {delta : Int}
    (accepted : checkedUpdate rows asset owner delta = .ok out) :
    out = putAmount (accountKey asset owner)
      (C.lookupLast (accountKey asset owner) rows + delta) rows ∧
    T.IsU128 (C.lookupLast (accountKey asset owner) rows + delta) := by
  dsimp only [checkedUpdate] at accepted
  split at accepted
  · contradiction
  · rename_i lower
    split at accepted
    · contradiction
    · rename_i upper
      cases accepted
      exact ⟨rfl, by constructor <;> omega⟩

theorem checkedUpdate_unique {rows out : List AmountRow} {asset owner : String} {delta : Int}
    (unique : Unique rows) (accepted : checkedUpdate rows asset owner delta = .ok out) :
    Unique out := by
  rw [(checkedUpdate_spec accepted).1]
  exact putAmount_unique _ _ _ unique

theorem checkedUpdate_positive {rows out : List AmountRow} {asset owner : String} {delta : Int}
    (positive : PositiveAccounts rows)
    (accepted : checkedUpdate rows asset owner delta = .ok out) : PositiveAccounts out := by
  obtain ⟨shape, bounded⟩ := checkedUpdate_spec accepted
  rw [shape]
  unfold PositiveAccounts putAmount
  split
  · intro row member
    exact positive row ((mem_eraseKey _ _ _).mp member).1
  · rename_i nonzero
    intro row member
    rcases List.mem_cons.mp member with same | member
    · subst row
      exact ⟨rfl, bounded, nonzero⟩
    · exact positive row ((mem_eraseKey _ _ _).mp member).1

theorem checkedUpdate_equation {rows out : List AmountRow} {asset owner : String} {delta : Int}
    (unique : Unique rows) (accepted : checkedUpdate rows asset owner delta = .ok out)
    (query : C.AmountKey) :
    C.amountSum query out = C.amountSum query rows +
      (if accountKey asset owner = query then delta else 0) := by
  rw [(checkedUpdate_spec accepted).1, amountSum_putAmount]
  by_cases same : accountKey asset owner = query
  · rw [if_pos same, same, C.lookupLast_eq_amountAt query rows unique,
      ← C.amountSum_eq_amountAt]
    simp only [if_true]
  · simp only [if_neg same, Int.add_zero]

def roleDelta (asset : String) (delta : String → Int) (query : C.AmountKey) : List String → Int
  | [] => 0
  | owner :: owners =>
      (if accountKey asset owner = query then delta owner else 0) +
        roleDelta asset delta query owners

theorem updateRoles_preserves {asset : String} {delta : String → Int} {owners : List String}
    {rows out : List AmountRow} (unique : Unique rows) (positive : PositiveAccounts rows)
    (accepted : updateRoles asset delta owners rows = .ok out) :
    Unique out ∧ PositiveAccounts out ∧
      ∀ query, C.amountSum query out = C.amountSum query rows + roleDelta asset delta query owners := by
  induction owners generalizing rows with
  | nil =>
      cases accepted
      exact ⟨unique, positive, fun query => by simp only [roleDelta, Int.add_zero]⟩
  | cons owner owners ih =>
      simp only [updateRoles] at accepted
      cases update : checkedUpdate rows asset owner (delta owner) with
      | error code => simp only [update, Except.bind] at accepted; contradiction
      | ok next =>
          simp only [update, Except.bind] at accepted
          obtain ⟨un, pos, equation⟩ := ih (checkedUpdate_unique unique update)
            (checkedUpdate_positive positive update) accepted
          refine ⟨un, pos, fun query => ?_⟩
          rw [equation, checkedUpdate_equation unique update query, roleDelta, Int.add_assoc]

theorem roleDelta_eq_occ (asset : String) (delta : String → Int) (owner queriedAsset domain : String)
    (owners : List String) :
    roleDelta asset delta (owner, queriedAsset, domain) owners =
      if asset = queriedAsset ∧ accounts = domain then
        delta owner * Proofs.AssetTransferRefinementV1.occ owner owners else 0 := by
  induction owners with
  | nil => simp only [roleDelta, Proofs.AssetTransferRefinementV1.occ, Int.mul_zero, ite_self]
  | cons p ps ih =>
      simp only [roleDelta, accountKey, Prod.mk.injEq, ih,
        Proofs.AssetTransferRefinementV1.occ]
      by_cases location : asset = queriedAsset ∧ accounts = domain
      · by_cases same : p = owner
        · simp only [same, location, and_self, if_pos, Int.mul_add, Int.mul_one]
        · simp only [same, location, false_and, if_false, Int.zero_add]
      · have mismatch : ¬(p = owner ∧ asset = queriedAsset ∧ accounts = domain) :=
          fun h => location h.2
        simp only [if_neg mismatch, if_neg location, Int.zero_add]

theorem perm_sum_int {left right : List Int} (perm : left.Perm right) : left.sum = right.sum := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp only [List.sum_cons, ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ left right => exact left.trans right

theorem amountSum_sortOn (rows : List AmountRow) (key : C.AmountKey) :
    C.amountSum key (C.sortOn balanceWire rows) = C.amountSum key rows := by
  rw [C.amountSum_eq_amountAt, C.amountSum_eq_amountAt]
  exact perm_sum_int ((C.sortOn_perm balanceWire rows).map _)

theorem finishBalances_spec {rows out : List AmountRow}
    (accepted : finishBalances rows = .ok out) :
    out = C.sortOn balanceWire rows ∧ out.length ≤ maxBalanceRows := by
  unfold finishBalances at accepted
  split at accepted
  · contradiction
  · rename_i bounded
    cases accepted
    have length := (C.sortOn_perm balanceWire rows).length_eq
    exact ⟨rfl, by omega⟩

theorem accepted_step_shape {input : Input}
    (accepted : (step input).verdict = .accepted) :
    (leaf input).verdict = .accepted ∧
    checkedBalances input = .ok (step input).post.balances ∧
    (step input).post = { input.pre with balances := (step input).post.balances } ∧
    (step input).plan = projectedPlan input := by
  unfold step at accepted ⊢
  split at accepted
  · contradiction
  · rename_i leafAccepted
    rw [leafAccepted]
    split at accepted
    · contradiction
    · rename_i rows rowAccepted
      rw [rowAccepted]
      exact ⟨rfl, rfl, rfl, rfl⟩

def CanonicalBalances (rows : List AmountRow) : Prop :=
  Unique rows ∧ PositiveAccounts rows ∧ rows.length ≤ maxBalanceRows ∧
    rows.Pairwise (fun a b => compare (balanceWire a) (balanceWire b) = .lt)

theorem finishBalances_canonical {rows out : List AmountRow}
    (unique : Unique rows) (positive : PositiveAccounts rows)
    (accepted : finishBalances rows = .ok out) : CanonicalBalances out := by
  obtain ⟨shape, bounded⟩ := finishBalances_spec accepted
  have perm : out.Perm rows := shape ▸ C.sortOn_perm balanceWire rows
  have outUnique : Unique out := (perm.map C.amountKey).nodup_iff.mpr unique
  have outPositive : PositiveAccounts out := fun row member => positive row (perm.mem_iff.mp member)
  refine ⟨outUnique, outPositive, bounded, ?_⟩
  have ordered := shape ▸ C.sortOn_ordered balanceWire rows
  have distinct : out.Pairwise (fun a b => C.amountKey a ≠ C.amountKey b) :=
    List.pairwise_map.mp outUnique
  apply List.Pairwise.imp_of_mem (p := ordered.and distinct)
  intro a b ma mb ⟨le, ne⟩
  rcases Ordering.isLE_iff_eq_lt_or_eq_eq.mp le with lt | eq
  · exact lt
  · have same := Std.LawfulEqOrd.eq_of_compare eq
    have keys : C.amountKey a = C.amountKey b := by
      have coords := Prod.mk.inj same
      simp only [C.amountKey, (outPositive a ma).1, (outPositive b mb).1]
      rw [coords.1, coords.2]
    exact False.elim (ne keys)

theorem checkedBalances_properties {input : Input} {out : List AmountRow}
    (unique : Unique input.pre.balances) (positive : PositiveAccounts input.pre.balances)
    (accepted : checkedBalances input = .ok out) :
    CanonicalBalances out ∧ ∀ query,
      C.amountSum query out = C.amountSum query input.pre.balances +
        roleDelta input.command.asset (T.delta (localState input) input.command) query
          (T.roleOrder (localState input) input.command) := by
  unfold checkedBalances at accepted
  cases updates : updateRoles input.command.asset (T.delta (localState input) input.command)
      (T.roleOrder (localState input) input.command) input.pre.balances with
  | error code => simp only [updates, Except.bind] at accepted; contradiction
  | ok rows =>
      simp only [updates, Except.bind] at accepted
      obtain ⟨un, pos, equation⟩ := updateRoles_preserves unique positive updates
      refine ⟨finishBalances_canonical un pos accepted, fun query => ?_⟩
      rw [(finishBalances_spec accepted).1, amountSum_sortOn, equation]

theorem accepted_balance_equation {input : Input}
    (unique : Unique input.pre.balances) (positive : PositiveAccounts input.pre.balances)
    (accepted : (step input).verdict = .accepted) (owner asset domain : String) :
    amountAt (step input).post.balances owner asset domain -
      amountAt input.pre.balances owner asset domain =
        if input.command.asset = asset ∧ accounts = domain then
          T.delta (localState input) input.command owner else 0 := by
  have shape := accepted_step_shape accepted
  have equation := (checkedBalances_properties unique positive shape.2.1).2 (owner, asset, domain)
  rw [C.amountSum_eq_amountAt, C.amountSum_eq_amountAt, roleDelta_eq_occ] at equation
  have distinct := ((T.accepted_iff_all_guards input.context (localState input) input.command).mp
    shape.1) .selfTransfer
  rw [M.delta_mul_occ_roleOrder distinct owner] at equation
  dsimp only at equation
  omega

def rowsEffect (kind : EffectKind) (owner asset domain : String) (rows : List EconomicEffectRow) : Int :=
  (rows.map fun row =>
    if row.kind = kind ∧ row.principal = owner ∧ row.asset = asset ∧ row.custodyDomain = domain
    then row.deltaAtoms else 0).sum

theorem rowsEffect_sortOn (kind : EffectKind) (owner asset domain : String)
    (rows : List EconomicEffectRow) :
    rowsEffect kind owner asset domain (C.sortOn effectWire rows) =
      rowsEffect kind owner asset domain rows :=
  perm_sum_int ((C.sortOn_perm effectWire rows).map _)

theorem rowsEffect_append (kind : EffectKind) (owner asset domain : String)
    (left right : List EconomicEffectRow) :
    rowsEffect kind owner asset domain (left ++ right) =
      rowsEffect kind owner asset domain left + rowsEffect kind owner asset domain right := by
  induction left with
  | nil => simp only [List.nil_append, rowsEffect, List.map_nil, List.sum_nil, Int.zero_add]
  | cons row rows ih =>
      simp only [List.cons_append, rowsEffect, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, Int.add_assoc]

theorem rowsEffect_movements (kind queryKind : EffectKind) (asset owner queryAsset domain : String)
    (movements : List Proofs.AssetTransferRefinementV1.MovementRow) :
    rowsEffect queryKind owner queryAsset domain (movementEffects kind asset movements) =
      if kind = queryKind ∧ asset = queryAsset ∧ accounts = domain then
        M.movementDeltaSum owner movements else 0 := by
  induction movements with
  | nil => simp only [movementEffects, List.map_nil, rowsEffect, List.sum_nil,
      M.movementDeltaSum, ite_self]
  | cons row rows ih =>
      simp only [movementEffects, List.map_cons, rowsEffect, List.sum_cons]
      change (if kind = queryKind ∧ row.principal = owner ∧ asset = queryAsset ∧ accounts = domain
        then row.deltaAtoms else 0) + rowsEffect queryKind owner queryAsset domain
          (movementEffects kind asset rows) = _
      rw [ih]
      by_cases matchKey : kind = queryKind ∧ asset = queryAsset ∧ accounts = domain
      · by_cases matchOwner : row.principal = owner
        · simp only [matchKey.1, matchKey.2.1, matchKey.2.2, matchOwner, and_self, if_pos,
            M.movementDeltaSum]
        · simp only [matchKey.1, matchKey.2.1, matchKey.2.2, matchOwner, false_and, true_and,
            if_false, if_true, M.movementDeltaSum, Int.zero_add]
      · have mismatch : ¬(kind = queryKind ∧ row.principal = owner ∧
            asset = queryAsset ∧ accounts = domain) := fun h => matchKey ⟨h.1, h.2.2⟩
        simp only [if_neg mismatch, if_neg matchKey, Int.zero_add]

theorem projectedPlan_effect (input : Input) (kind : EffectKind) (owner asset domain : String) :
    effectFor kind (projectedPlan input) owner asset domain =
      (if .accountMovement = kind ∧ input.command.asset = asset ∧ accounts = domain then
        M.movementDeltaSum owner (T.acceptedEffects (localState input) input.command).movements else 0) +
      (if .feeAllocation = kind ∧ input.command.asset = asset ∧ accounts = domain then
        M.movementDeltaSum owner (T.acceptedEffects (localState input) input.command).feeAllocations else 0) := by
  change rowsEffect kind owner asset domain (C.sortOn effectWire _) = _
  rw [rowsEffect_sortOn, rowsEffect_append, rowsEffect_movements, rowsEffect_movements]

theorem accepted_account_effect {input : Input}
    (accepted : (step input).verdict = .accepted) (owner asset domain : String) :
    effectFor .accountMovement (step input).plan owner asset domain =
      if input.command.asset = asset ∧ accounts = domain then
        T.delta (localState input) input.command owner else 0 := by
  have shape := accepted_step_shape accepted
  rw [shape.2.2.2, projectedPlan_effect]
  have distinct := ((T.accepted_iff_all_guards input.context (localState input) input.command).mp
    shape.1) .selfTransfer
  simp only [reduceCtorEq, true_and, false_and, if_false, Int.add_zero, T.acceptedEffects]
  rw [M.movementRows_sum_eq_delta_mul_occ, M.delta_mul_occ_roleOrder distinct owner]

theorem projectedPlan_frame_effects (input : Input) (owner asset domain : String) :
    effectFor .custody (projectedPlan input) owner asset domain = 0 ∧
    effectFor .liability (projectedPlan input) owner asset domain = 0 ∧
    effectFor .reserve (projectedPlan input) owner asset domain = 0 := by
  simp only [projectedPlan_effect, reduceCtorEq, false_and, if_false, Int.zero_add, and_self]

theorem accepted_exact_economic_tables {input : Input}
    (unique : Unique input.pre.balances) (positive : PositiveAccounts input.pre.balances)
    (accepted : (step input).verdict = .accepted) :
    ExactEconomicTables input.pre (step input).post (step input).plan := by
  have shape := accepted_step_shape accepted
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro owner asset domain
    rw [accepted_balance_equation unique positive accepted, accepted_account_effect accepted]
  all_goals
    intro owner asset domain
    rw [shape.2.2.1, shape.2.2.2]
    simp only [Int.sub_self]
  · exact (projectedPlan_frame_effects input owner asset domain).1.symm
  · exact (projectedPlan_frame_effects input owner asset domain).2.1.symm
  · exact (projectedPlan_frame_effects input owner asset domain).2.2.symm

theorem projectedPlan_row_kinds (input : Input) (row : EconomicEffectRow)
    (member : row ∈ (projectedPlan input).rows) :
    row.kind = .accountMovement ∨ row.kind = .feeAllocation := by
  change row ∈ C.sortOn effectWire _ at member
  have raw := (C.mem_sortOn effectWire row _).mp member
  rcases List.mem_append.mp raw with movement | fee
  · obtain ⟨source, _, same⟩ := List.mem_map.mp movement
    subst row
    exact Or.inl rfl
  · obtain ⟨source, _, same⟩ := List.mem_map.mp fee
    subst row
    exact Or.inr rfl

theorem sum_map_zero {α : Type} (rows : List α) (f : α → Int)
    (zero : ∀ row ∈ rows, f row = 0) : (rows.map f).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [List.map_cons, List.sum_cons, zero row (List.mem_cons_self ..)]
      exact Int.zero_add _ |>.trans (ih (fun r m => zero r (List.mem_cons_of_mem _ m)))

theorem projectedPlan_supply_zero (input : Input) (asset : String) :
    issueDeltaFor (projectedPlan input) asset = 0 ∧
    burnDeltaFor (projectedPlan input) asset = 0 := by
  constructor
  · apply sum_map_zero
    intro row member
    rcases projectedPlan_row_kinds input row member with account | fee
    · simp only [issueContribution, account, reduceCtorEq, false_and, if_false]
    · simp only [issueContribution, fee, reduceCtorEq, false_and, if_false]
  · apply sum_map_zero
    intro row member
    rcases projectedPlan_row_kinds input row member with account | fee
    · simp only [burnContribution, account, reduceCtorEq, false_and, if_false]
    · simp only [burnContribution, fee, reduceCtorEq, false_and, if_false]

theorem accepted_exact_supply {input : Input}
    (accepted : (step input).verdict = .accepted) :
    ExactSupplyEffects input.pre (step input).post (step input).plan := by
  have shape := accepted_step_shape accepted
  intro asset
  rw [shape.2.2.1, shape.2.2.2, (projectedPlan_supply_zero input asset).1,
    (projectedPlan_supply_zero input asset).2]
  exact Int.sub_self _

theorem step_frame (input : Input) :
    (step input).post = { input.pre with balances := (step input).post.balances } := by
  unfold step
  split
  · rfl
  · split <;> rfl

theorem rejected_step_noop {input : Input} {code : T.RejectCode}
    (rejection : (step input).verdict = .rejected code) :
    (step input).post = input.pre ∧ (step input).plan = EffectPlan.empty := by
  unfold step at rejection ⊢
  split at rejection
  · exact ⟨rfl, rfl⟩
  · split at rejection
    · exact ⟨rfl, rfl⟩
    · contradiction

/-- The existing sender guard is derived; authenticating this context is separate. -/
theorem accepted_sender_is_context {input : Input}
    (accepted : (step input).verdict = .accepted) :
    input.command.sender = input.context.subjectId :=
  ((T.accepted_iff_all_guards input.context (localState input) input.command).mp
    (accepted_step_shape accepted).1) .unauthorizedSubject

/-- No assumed exact table relation, output representation, or principal coverage. -/
theorem accepted_sparse_transfer {input : Input}
    (unique : Unique input.pre.balances) (positive : PositiveAccounts input.pre.balances)
    (accepted : (step input).verdict = .accepted) :
    ExactEconomicTables input.pre (step input).post (step input).plan ∧
    ExactSupplyEffects input.pre (step input).post (step input).plan ∧
    CanonicalBalances (step input).post.balances ∧
    (step input).post = { input.pre with balances := (step input).post.balances } ∧
    input.command.sender = input.context.subjectId := by
  exact ⟨accepted_exact_economic_tables unique positive accepted, accepted_exact_supply accepted,
    (checkedBalances_properties unique positive (accepted_step_shape accepted).2.1).1,
    step_frame input, accepted_sender_is_context accepted⟩

/-- Lift only the table equality/frame portion of global allocation binding.
Metadata may reflect a real same-epoch occurrence; no height equation is assumed. -/
theorem disclosed_tables_refine {input : Input} {post : GlobalState} {plan : EffectPlan}
    (unique : Unique input.pre.balances) (positive : PositiveAccounts input.pre.balances)
    (accepted : (step input).verdict = .accepted)
    (balances : post.balances = (step input).post.balances)
    (custody : post.custody = input.pre.custody)
    (liabilities : post.liabilities = input.pre.liabilities)
    (reserves : post.reserves = input.pre.reserves)
    (supplies : post.supplies = input.pre.supplies)
    (effects : plan.rows = (step input).plan.rows) :
    ExactEconomicTables input.pre post plan ∧ ExactSupplyEffects input.pre post plan := by
  have tables := accepted_exact_economic_tables unique positive accepted
  have supply := accepted_exact_supply accepted
  rw [step_frame input] at tables supply
  constructor
  · simpa only [ExactEconomicTables, ExactTableEffect, effectFor, balances, custody,
      liabilities, reserves, effects] using tables
  · simpa only [ExactSupplyEffects, issueDeltaFor, burnDeltaFor, supplies, effects] using supply

/-! Nonempty accounting controls use the real four-table representation and
have physical owned supply equal to declared supply. They are not complete
authenticated global-admission traces. -/
def demo : Input :=
  { context := ⟨"module", "alice"⟩
    moduleReleaseId := "module"
    policy := ⟨"USD", "treasury", 2, true⟩
    command := ⟨"asset_transfer", "USD", "alice", "bob", 30, 2⟩
    pre := { staticGlobalState with
      balances := [⟨"alice", "USD", accounts, 32⟩, ⟨"zed", "ZZZ", accounts, 7⟩]
      supplies := [⟨"USD", 35⟩, ⟨"ZZZ", 12⟩]
      custody := [⟨"vault", "USD", "vault", 3⟩]
      liabilities := [⟨"claimant", "USD", "vault", 3⟩]
      reserves := [⟨"reserve", "ZZZ", "reserve", 5⟩] } }

theorem demo_source : Unique demo.pre.balances ∧ PositiveAccounts demo.pre.balances := by
  constructor
  · unfold Unique
    decide
  · intro row member
    simp only [demo, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

theorem demo_deletes_zero_and_frames_other_asset :
    (step demo).verdict = .accepted ∧
    (step demo).post.balances =
      [⟨"bob", "USD", accounts, 30⟩, ⟨"treasury", "USD", accounts, 2⟩,
       ⟨"zed", "ZZZ", accounts, 7⟩] := by
  constructor
  · decide
  · change C.sortOn balanceWire
      [⟨"treasury", "USD", accounts, 2⟩, ⟨"bob", "USD", accounts, 30⟩,
       ⟨"zed", "ZZZ", accounts, 7⟩] = _
    simp +decide [C.sortOn, List.mergeSort, List.MergeSort.Internal.splitInTwo,
      List.splitAt_eq, List.take, List.drop]

theorem demo_derived_tables :
    ExactEconomicTables demo.pre (step demo).post (step demo).plan ∧
    CanonicalBalances (step demo).post.balances :=
  ⟨(accepted_sparse_transfer demo_source.1 demo_source.2 demo_deletes_zero_and_frames_other_asset.1).1,
    (accepted_sparse_transfer demo_source.1 demo_source.2 demo_deletes_zero_and_frames_other_asset.1).2.2.1⟩

theorem demo_fee_aliases :
    (step { demo with policy := { demo.policy with feeOwner := "alice" } }).post.balances =
      [⟨"alice", "USD", accounts, 2⟩, ⟨"bob", "USD", accounts, 30⟩,
       ⟨"zed", "ZZZ", accounts, 7⟩] ∧
    (step { demo with policy := { demo.policy with feeOwner := "bob" } }).post.balances =
      [⟨"bob", "USD", accounts, 32⟩, ⟨"zed", "ZZZ", accounts, 7⟩] := by
  constructor
  · change C.sortOn balanceWire
      [⟨"bob", "USD", accounts, 30⟩, ⟨"alice", "USD", accounts, 2⟩,
       ⟨"zed", "ZZZ", accounts, 7⟩] = _
    simp +decide [C.sortOn, List.mergeSort, List.MergeSort.Internal.splitInTwo,
      List.splitAt_eq, List.take, List.drop]
  · change C.sortOn balanceWire
      [⟨"bob", "USD", accounts, 32⟩, ⟨"zed", "ZZZ", accounts, 7⟩] = _
    simp +decide [C.sortOn, List.mergeSort, List.MergeSort.Internal.splitInTwo,
      List.splitAt_eq, List.take, List.drop]

theorem demo_owned_supply : OwnedMatchesSupply demo.pre ∧ OwnedMatchesSupply (step demo).post := by
  constructor
  · intro asset
    by_cases usd : asset = "USD"
    · subst asset
      decide
    · by_cases zzz : asset = "ZZZ"
      · subst asset
        decide
      · simp [ownedFor, amountForAsset, supplyFor, demo, Ne.symm usd, Ne.symm zzz]
  · intro asset
    rw [step_frame demo]
    change amountForAsset (step demo).post.balances asset +
      amountForAsset demo.pre.custody asset + amountForAsset demo.pre.reserves asset =
        supplyFor demo.pre.supplies asset
    rw [demo_deletes_zero_and_frames_other_asset.2]
    by_cases usd : asset = "USD"
    · subst asset
      decide
    · by_cases zzz : asset = "ZZZ"
      · subst asset
        decide
      · simp [amountForAsset, supplyFor, demo, Ne.symm usd, Ne.symm zzz]

end Proofs.AssetTransferSparseTablesV1
