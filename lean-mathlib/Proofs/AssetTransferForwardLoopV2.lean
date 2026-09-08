import Proofs.AssetTransferFiniteOutcomeV2

/-!
Literal checked forward row execution equals the existing initial scan and
canonical tail materialization. The working table is updated head first and
sorted once. V2 rejection order and final-only resource checks remain explicit.
Dictionary/parser representation, cryptographic roots and complete effect or
journal/runtime refinement are external to this finite-row algorithm theorem.
-/
set_option warningAsError true

namespace Proofs.AssetTransferForwardLoopV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace C
export CanonicalEpochEconomicRowsV1 (AmountKey amountKey lookupLast lookupLast_absent
  lookupLast_eq_amountAt amountSum amountSum_eq_amountAt sortOn sortOn_perm sortOn_ordered)
end C
namespace S
export AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey balanceWire accounts
  putAmount putAmount_unique amountSum_putAmount amountSum_sortOn makeAmount eraseKey mem_eraseKey)
end S
namespace A
export ManagedAssetFiniteAccountingV2 (updateRows updateRows_lookup updateRows_unique updateRows_positive)
end A
namespace F
export AssetTransferFiniteAccountingV2 (project updateRoles transferRows update_roles_unique
  update_roles_lookup update_roles_positive ordered_roles_unique accepted_selected_asset accepted_distinct)
end F
namespace T
export AssetTransferRefinementV2 (RejectCode IsU128 u128Max Policy TransferState Context Command
  orderedRoles delta balanceCodeOn postBalance guardPasses firstFailing firstFailing_eq_none_iff
  preBalanceRejectCodes Root)
end T
namespace O
export AssetTransferFiniteOutcomeV2 (State Structural CommandAdmission candidate candidateFor
  project policyFor policyFor_spec economicRejectCode economic_none_iff_selected
  economic_matches_selected transition Resources Verdict reject rejected_noop accepted_iff
  resource_reject_iff accepted_post_effects economic_reject_precedes_resource contextRejectCode)
end O
namespace R
export AssetLaneFiniteRecompositionV2 (AccountsDomain sortOn_eq_of_perm_keys balance_wire_keys_unique)
end R

attribute [local instance] lexOrd

def Ordered (rows : List AmountRow) : Prop :=
  rows.Pairwise (fun left right => (compare (S.balanceWire left) (S.balanceWire right)).isLE = true)

/-- Checks the new amount in the actual working table. It does not sort. -/
def checkedPut (rows : List AmountRow) (asset owner : String) (delta : Int) :
    Except T.RejectCode (List AmountRow) :=
  let amount := C.lookupLast (S.accountKey asset owner) rows + delta
  if amount < 0 then .error .insufficientBalance
  else if T.u128Max < amount then .error .balanceOverflow
  else .ok (S.putAmount (S.accountKey asset owner) amount rows)

/-- The literal head-first working-table loop. -/
def forwardRaw (rows : List AmountRow) (asset : String) (delta : String → Int) :
    List String → Except T.RejectCode (List AmountRow)
  | [] => .ok rows
  | owner :: rest =>
      (checkedPut rows asset owner (delta owner)).bind (fun next => forwardRaw next asset delta rest)

/-- Final sorting occurs only after the raw loop succeeds. -/
def forward (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) : Except T.RejectCode (List AmountRow) :=
  (forwardRaw rows asset delta roles).map (C.sortOn S.balanceWire)

/-- Independent scan of initial-table quantities in the supplied role order. -/
def initialScan (rows : List AmountRow) (asset : String) (delta : String → Int) :
    List String → Option T.RejectCode
  | [] => none
  | owner :: rest =>
      let amount := C.lookupLast (S.accountKey asset owner) rows + delta owner
      if amount < 0 then some .insufficientBalance
      else if T.u128Max < amount then some .balanceOverflow
      else initialScan rows asset delta rest

def errorCode (result : Except T.RejectCode (List AmountRow)) : Option T.RejectCode :=
  match result with
  | .error code => some code
  | .ok _ => none

theorem put_lookup (rows : List AmountRow) (asset owner : String) (amount : Int)
    (unique : S.Unique rows) (queryAsset queryOwner : String) :
    C.lookupLast (S.accountKey queryAsset queryOwner) (S.putAmount (S.accountKey asset owner) amount rows) =
      if asset = queryAsset ∧ owner = queryOwner then amount
      else C.lookupLast (S.accountKey queryAsset queryOwner) rows := by
  rw [C.lookupLast_eq_amountAt _ _ (S.putAmount_unique _ _ _ unique),
    ← C.amountSum_eq_amountAt, S.amountSum_putAmount,
    C.amountSum_eq_amountAt, ← C.lookupLast_eq_amountAt _ _ unique]
  by_cases selected : asset = queryAsset ∧ owner = queryOwner
  · rcases selected with ⟨rfl, rfl⟩
    simp
  · have different : S.accountKey asset owner ≠ S.accountKey queryAsset queryOwner := by
      simpa [S.accountKey, and_comm] using selected
    simp only [if_neg different, if_neg selected]

theorem put_positive (rows : List AmountRow) (asset owner : String) (amount : Int)
    (positive : S.PositiveAccounts rows) (bounded : T.IsU128 amount) :
    S.PositiveAccounts (S.putAmount (S.accountKey asset owner) amount rows) := by
  intro row member
  unfold S.putAmount at member
  split at member
  · exact positive row ((S.mem_eraseKey _ rows row).mp member).1
  · rename_i nonzero
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl, bounded, nonzero⟩
    · exact positive row ((S.mem_eraseKey _ rows row).mp member).1

theorem checkedPut_spec {rows out : List AmountRow} {asset owner : String} {delta : Int}
    (accepted : checkedPut rows asset owner delta = .ok out) :
    out = S.putAmount (S.accountKey asset owner) (C.lookupLast (S.accountKey asset owner) rows + delta) rows ∧
      T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta) := by
  dsimp only [checkedPut] at accepted
  split at accepted
  · contradiction
  · rename_i lower
    split at accepted
    · contradiction
    · rename_i upper
      cases accepted
      exact ⟨rfl, by constructor <;> omega⟩

theorem initialScan_congr (left right : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String)
    (same : ∀ owner ∈ roles, C.lookupLast (S.accountKey asset owner) left =
      C.lookupLast (S.accountKey asset owner) right) :
    initialScan left asset delta roles = initialScan right asset delta roles := by
  induction roles with
  | nil => rfl
  | cons owner rest ih =>
      simp only [initialScan, same owner List.mem_cons_self]
      split <;> try rfl
      split <;> try rfl
      exact ih (fun next member => same next (List.mem_cons_of_mem owner member))

theorem initialScan_none_iff (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) : initialScan rows asset delta roles = none ↔
      ∀ owner ∈ roles, T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta owner) := by
  induction roles with
  | nil => simp [initialScan]
  | cons owner rest ih =>
      rw [List.forall_mem_cons]
      dsimp only [initialScan]
      split
      · rename_i negative
        simp only [Option.some_ne_none, false_iff, not_and]
        intro bounded
        exact False.elim (by have lower := bounded.1; omega)
      · rename_i lower
        split
        · rename_i overflow
          simp only [Option.some_ne_none, false_iff, not_and]
          intro bounded
          exact False.elim (by have upper := bounded.2; omega)
        · rename_i upper
          rw [ih]
          have bounded : T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta owner) := by
            constructor <;> omega
          simp only [bounded, true_and]

theorem forwardRaw_error (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) (unique : S.Unique rows) (rolesUnique : roles.Nodup) :
    errorCode (forwardRaw rows asset delta roles) = initialScan rows asset delta roles := by
  induction roles generalizing rows with
  | nil => rfl
  | cons owner rest ih =>
      have parts := List.nodup_cons.mp rolesUnique
      dsimp only [forwardRaw, checkedPut, initialScan]
      split
      · rfl
      · split
        · rfl
        · simp only [Except.bind]
          rw [ih _ (S.putAmount_unique _ _ _ unique) parts.2]
          apply initialScan_congr
          intro next member
          rw [put_lookup _ _ _ _ unique]
          have different : owner ≠ next := fun same => parts.1 (same ▸ member)
          simp only [true_and, if_neg different]


/-- Successful raw execution preserves the actual table and records every touched
account exactly once. The proof uses V2 checks, not a converted V1 result. -/
theorem forwardRaw_spec {rows out : List AmountRow} {asset : String} {delta : String → Int}
    {roles : List String} (unique : S.Unique rows) (positive : S.PositiveAccounts rows)
    (rolesUnique : roles.Nodup) (accepted : forwardRaw rows asset delta roles = .ok out) :
    S.Unique out ∧ S.PositiveAccounts out ∧
      ∀ queryAsset queryOwner, C.lookupLast (S.accountKey queryAsset queryOwner) out =
        C.lookupLast (S.accountKey queryAsset queryOwner) rows +
          (if asset = queryAsset ∧ queryOwner ∈ roles then delta queryOwner else 0) := by
  induction roles generalizing rows with
  | nil =>
      cases accepted
      exact ⟨unique, positive, fun queryAsset queryOwner => by simp⟩
  | cons owner rest ih =>
      have parts := List.nodup_cons.mp rolesUnique
      simp only [forwardRaw] at accepted
      cases step : checkedPut rows asset owner (delta owner) with
      | error code => simp only [step, Except.bind] at accepted; contradiction
      | ok next =>
          simp only [step, Except.bind] at accepted
          obtain ⟨rfl, bounded⟩ := checkedPut_spec step
          obtain ⟨outUnique, outPositive, equation⟩ := ih (S.putAmount_unique _ _ _ unique)
            (put_positive _ _ _ _ positive bounded) parts.2 accepted
          constructor
          · exact outUnique
          constructor
          · exact outPositive
          intro queryAsset queryOwner
          rw [equation, put_lookup _ _ _ _ unique]
          by_cases sameAsset : asset = queryAsset
          · subst queryAsset
            by_cases sameOwner : owner = queryOwner
            · subst queryOwner
              simp only [true_and, if_neg parts.1, List.mem_cons_self, if_true, Int.add_zero]
            · simp only [true_and, if_neg sameOwner, List.mem_cons, Ne.symm sameOwner, false_or]
          · simp only [sameAsset, false_and, if_false, Int.add_zero]

theorem row_eq_of_key_amount {left right : AmountRow}
    (key : C.amountKey left = C.amountKey right) (amount : left.amountAtoms = right.amountAtoms) :
    left = right := by
  cases left with
  | mk lo la ld ln =>
      cases right with
      | mk ro ra rd rn =>
          simp only [C.amountKey, Prod.mk.injEq] at key
          obtain ⟨rfl, rfl, rfl⟩ := key
          cases amount
          rfl

theorem member_of_lookup (rows : List AmountRow) (row : AmountRow) (unique : S.Unique rows)
    (domain : row.custodyDomain = S.accounts) (nonzero : row.amountAtoms ≠ 0)
    (lookup : C.lookupLast (S.accountKey row.asset row.owner) rows = row.amountAtoms) : row ∈ rows := by
  have present : S.accountKey row.asset row.owner ∈ rows.map C.amountKey := by
    by_cases member : S.accountKey row.asset row.owner ∈ rows.map C.amountKey
    · exact member
    · have zero := C.lookupLast_absent _ rows member
      exact False.elim (nonzero (lookup.symm.trans zero))
  obtain ⟨other, member, key⟩ := List.mem_map.mp present
  have value := AssetLaneFiniteRowGrowthV2.lookupLast_member rows other unique member
  rw [key, lookup] at value
  have same : row = other := row_eq_of_key_amount
    (by simpa only [C.amountKey, S.accountKey, domain] using key.symm) value
  exact same ▸ member

/-- Nonzero canonical account rows make lookups sufficient to recover support.
The restriction excludes stored zero rows, whose presence a lookup cannot see. -/
theorem rows_perm_of_lookup (left right : List AmountRow)
    (leftUnique : S.Unique left) (rightUnique : S.Unique right)
    (leftPositive : S.PositiveAccounts left) (rightPositive : S.PositiveAccounts right)
    (lookups : ∀ asset owner, C.lookupLast (S.accountKey asset owner) left =
      C.lookupLast (S.accountKey asset owner) right) : left.Perm right := by
  have subset : ∀ (xs ys : List AmountRow), S.Unique xs → S.Unique ys → S.PositiveAccounts xs →
      (∀ asset owner, C.lookupLast (S.accountKey asset owner) xs =
        C.lookupLast (S.accountKey asset owner) ys) → xs ⊆ ys := by
    intro xs ys xsUnique ysUnique xsPositive same row member
    have facts := xsPositive row member
    have value := AssetLaneFiniteRowGrowthV2.lookupLast_member xs row xsUnique member
    have key : C.amountKey row = S.accountKey row.asset row.owner := by
      simp only [C.amountKey, S.accountKey, facts.1]
    rw [key, same] at value
    exact member_of_lookup ys row ysUnique facts.1 facts.2.2 value
  have lr := subset left right leftUnique rightUnique leftPositive lookups
  have rl := subset right left rightUnique leftUnique rightPositive (fun asset owner => (lookups asset owner).symm)
  have plainUnique : ∀ xs : List AmountRow, S.Unique xs → xs.Nodup := by
    intro xs keys
    have pairs := List.pairwise_map.mp keys
    exact pairs.imp (fun different same => different (congrArg C.amountKey same))
  apply List.perm_iff_count.mpr
  intro row
  rw [(plainUnique left leftUnique).count, (plainUnique right rightUnique).count]
  have same : row ∈ left ↔ row ∈ right := ⟨fun member => lr member, fun member => rl member⟩
  simp only [same]

theorem tail_ordered (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) (ordered : Ordered rows) : Ordered (F.updateRoles rows asset delta roles) := by
  cases roles with
  | nil => exact ordered
  | cons owner rest => exact C.sortOn_ordered S.balanceWire _

/-- Exact error-or-final-table equality. All hypotheses concern the initial
rows or the role list; the operational loop computes its own success. -/
theorem forward_eq_scan_tail (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) (unique : S.Unique rows) (positive : S.PositiveAccounts rows)
    (ordered : Ordered rows) (rolesUnique : roles.Nodup) :
    forward rows asset delta roles =
      match initialScan rows asset delta roles with
      | some code => .error code
      | none => .ok (F.updateRoles rows asset delta roles) := by
  have error := forwardRaw_error rows asset delta roles unique rolesUnique
  unfold forward
  cases result : forwardRaw rows asset delta roles with
  | error code =>
      simp only [result, errorCode] at error
      simp only [← error, Except.map]
  | ok out =>
      simp only [result, errorCode] at error
      simp only [← error, Except.map, Except.ok.injEq]
      obtain ⟨outUnique, outPositive, outLookup⟩ := forwardRaw_spec unique positive rolesUnique result
      have tailUnique := F.update_roles_unique rows asset delta roles unique
      have tailPositive := F.update_roles_positive rows asset delta roles unique positive rolesUnique
        ((initialScan_none_iff rows asset delta roles).mp error.symm)
      apply R.sortOn_eq_of_perm_keys
      · exact rows_perm_of_lookup out _ outUnique tailUnique outPositive tailPositive
          (fun queryAsset queryOwner => (outLookup queryAsset queryOwner).trans
            (F.update_roles_lookup rows asset delta roles unique rolesUnique queryAsset queryOwner).symm)
      · exact R.balance_wire_keys_unique _ tailUnique (fun row member => (tailPositive row member).1)
      · exact tail_ordered rows asset delta roles ordered


theorem project_scan (release : String) (policy : T.Policy) (rows : List AmountRow) (supply : Int)
    (command : T.Command) (roles : List String) :
    initialScan rows policy.asset (T.delta (F.project release policy rows supply) command) roles =
      T.balanceCodeOn (F.project release policy rows supply) command roles := by
  induction roles with
  | nil => rfl
  | cons owner rest ih =>
      simp only [initialScan, T.balanceCodeOn, T.postBalance, F.project]
      split <;> try rfl
      split <;> try rfl
      exact ih

/-- Actual V2 ordered roles and coalesced deltas instantiate the loop equality.
The asset equality is an explicit selected-policy binding. -/
theorem selected_forward_eq (release : String) (policy : T.Policy) (rows : List AmountRow)
    (supply : Int) (command : T.Command) (unique : S.Unique rows) (positive : S.PositiveAccounts rows)
    (ordered : Ordered rows) (assetBinding : command.asset = policy.asset)
    (distinct : command.sender ≠ command.recipient) :
    forward rows command.asset (T.delta (F.project release policy rows supply) command)
      (T.orderedRoles (F.project release policy rows supply) command) =
        match T.balanceCodeOn (F.project release policy rows supply) command
          (T.orderedRoles (F.project release policy rows supply) command) with
        | some code => .error code
        | none => .ok (F.transferRows (F.project release policy rows supply) command rows) := by
  have scan : initialScan rows command.asset (T.delta (F.project release policy rows supply) command)
      (T.orderedRoles (F.project release policy rows supply) command) =
      T.balanceCodeOn (F.project release policy rows supply) command
        (T.orderedRoles (F.project release policy rows supply) command) := by
    rw [assetBinding]
    exact project_scan release policy rows supply command _
  simpa only [scan, F.transferRows] using forward_eq_scan_tail rows command.asset
    (T.delta (F.project release policy rows supply) command)
    (T.orderedRoles (F.project release policy rows supply) command) unique positive ordered
    (F.ordered_roles_unique _ command distinct)

/-- Actual finite policy lookup and prefix validation feed the literal forward
loop. It computes a candidate or V2 economic rejection before any size check. -/
def operationalCandidate (ctx : T.Context) (pre : O.State) (command : T.Command) :
    Except T.RejectCode O.State :=
  match O.contextRejectCode ctx pre.moduleReleaseId command with
  | some code => .error code
  | none =>
      match O.policyFor pre command.asset with
      | none => .error .unknownAsset
      | some policy =>
          let selected := O.project pre policy
          match T.firstFailing (T.guardPasses ctx selected command) T.preBalanceRejectCodes with
          | some code => .error code
          | none =>
              (forward pre.balances command.asset (T.delta selected command)
                (T.orderedRoles selected command)).map (fun rows => {pre with balances := rows})

/-- Full policy-list lookup and the V2 prefix establish the binding/distinctness
needed by row execution; neither is supplied as a successful leaf witness. -/
theorem operationalCandidate_eq (ctx : T.Context) (pre : O.State) (command : T.Command)
    (structural : O.Structural pre) :
    operationalCandidate ctx pre command =
      match O.economicRejectCode ctx pre command with
      | some code => .error code
      | none => .ok (O.candidate pre command) := by
  unfold operationalCandidate O.economicRejectCode
  cases common : O.contextRejectCode ctx pre.moduleReleaseId command with
  | some code => rfl
  | none =>
      cases selected : O.policyFor pre command.asset with
      | none => rfl
      | some policy =>
          dsimp only
          unfold AssetTransferRefinementV2.rejectCode
          cases prefixClear : T.firstFailing (T.guardPasses ctx (O.project pre policy) command)
              T.preBalanceRejectCodes with
          | some code => rfl
          | none =>
              have guards := (T.firstFailing_eq_none_iff
                (T.guardPasses ctx (O.project pre policy) command) T.preBalanceRejectCodes).mp prefixClear
              have distinct : command.sender ≠ command.recipient := guards .selfTransfer (by decide)
              have ordered : Ordered pre.balances := structural.balanceOrdered.imp
                (fun strict => by simp only [strict]; rfl)
              have actual := selected_forward_eq pre.moduleReleaseId policy pre.balances
                (supplyFor (RegisteredSupplySupportV1.numericRows pre.supplies) policy.asset) command
                structural.balanceUnique structural.balancePositive ordered
                (O.policyFor_spec selected).2.symm distinct
              change forward pre.balances command.asset (T.delta (O.project pre policy) command)
                  (T.orderedRoles (O.project pre policy) command) =
                (match T.balanceCodeOn (O.project pre policy) command
                    (T.orderedRoles (O.project pre policy) command) with
                 | some code => .error code
                 | none => .ok (F.transferRows (O.project pre policy) command pre.balances)) at actual
              rw [actual]
              cases arithmetic : T.balanceCodeOn (O.project pre policy) command
                  (T.orderedRoles (O.project pre policy) command) with
              | some code => rfl
              | none => simp only [Except.map, O.candidate, selected, O.candidateFor]

/-- A caller can compute resources on the exact forward result. No intermediate
working table is admitted or rejected by a row or byte ceiling. -/
theorem finite_accepts_iff_forward (digest : AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
    (ctx : T.Context) (pre : O.State) (command : T.Command) (structural : O.Structural pre) :
    (O.transition digest ctx pre command).verdict = .accepted ↔
      ∃ post, operationalCandidate ctx pre command = .ok post ∧ O.Resources post := by
  rw [O.accepted_iff, operationalCandidate_eq ctx pre command structural]
  cases code : O.economicRejectCode ctx pre command with
  | some code => simp
  | none => simp

theorem finite_resource_reject_iff_forward (digest : AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
    (ctx : T.Context) (pre : O.State) (command : T.Command) (structural : O.Structural pre) :
    (O.transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
      ∃ post, operationalCandidate ctx pre command = .ok post ∧ ¬ O.Resources post := by
  rw [O.resource_reject_iff, operationalCandidate_eq ctx pre command structural]
  cases code : O.economicRejectCode ctx pre command with
  | some code => simp
  | none => simp

theorem finite_accepted_forward_post {digest : AssetLaneFiniteByteAccountingV2.Bytes → T.Root}
    {ctx : T.Context} {pre : O.State} {command : T.Command} (structural : O.Structural pre)
    (accepted : (O.transition digest ctx pre command).verdict = .accepted) :
    operationalCandidate ctx pre command = .ok (O.transition digest ctx pre command).post := by
  rw [(O.accepted_post_effects accepted).1, operationalCandidate_eq ctx pre command structural,
    (O.accepted_iff digest ctx pre command).mp accepted |>.1]

theorem forward_error_rejects_noop (digest : AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
    (ctx : T.Context) (pre : O.State) (command : T.Command) (structural : O.Structural pre)
    (code : T.RejectCode) (failed : operationalCandidate ctx pre command = .error code) :
    O.transition digest ctx pre command = O.reject (.economic code) pre := by
  rw [operationalCandidate_eq ctx pre command structural] at failed
  cases economic : O.economicRejectCode ctx pre command with
  | none => simp only [economic] at failed; contradiction
  | some reason =>
      simp only [economic, Except.error.injEq] at failed
      subst reason
      exact O.economic_reject_precedes_resource digest ctx pre command code economic


theorem finite_economic_reject_iff_forward (digest : AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
    (ctx : T.Context) (pre : O.State) (command : T.Command) (structural : O.Structural pre)
    (code : T.RejectCode) :
    (O.transition digest ctx pre command).verdict = .rejected (.economic code) ↔
      operationalCandidate ctx pre command = .error code := by
  rw [operationalCandidate_eq ctx pre command structural]
  unfold O.transition
  cases economic : O.economicRejectCode ctx pre command with
  | some reason => simp [O.reject]
  | none =>
      by_cases resource : O.Resources (O.candidate pre command) <;> simp [resource, O.reject]

end Proofs.AssetTransferForwardLoopV2
