import Proofs.AssetTransferRefinementV1
import Proofs.GlobalEconomicStateRefinementV2

/-!
# Constructive restricted transfer-to-global accounting preservation

This accounting lift executes the existing formal transfer transition. Its
global state is the existing V2 mathematical state, with only balance rows
changed on acceptance. It is deliberately not a full V2 `Verified` constructor:
height, replay, roots, publication, effects application and canonical sparse
serialization require separate refinement. Materialization keeps zero rows.

The representation premise identifies every global account row and its single
asset supply with a local balance function over an explicit finite enumeration.
Touched principals occur exactly once; other principals and completeness of the
enumeration are supplied by the representation boundary, not inferred from
conservation. No runtime decoder or authenticated snapshot is constructed here.

Owned supply uses V2's physical balances + custody + reserves. Claimant
liabilities and terminal obligations are never added to owned supply. Exact
allocation below is per asset/domain custody-to-claim partition, not the full
lane certificate or evidence of claimant title. Whole claimant and terminal
tables remain unchanged. Authorization proves sender = context subject; the
context must separately be authenticated for the exact command by the shell.

No Python/Rust refinement, cryptographic signature verification, receipt
admission, external asset possession, or production value safety is claimed.
-/

namespace Proofs.AssetTransferGlobalPreservationV1

namespace T
export Proofs.AssetTransferRefinementV1 (AbstractEffects Command Context Principal RejectCode TransferState acceptDistinct acceptedState accepted_conserves_total accepted_iff_all_guards accepted_post_eq alice baseRows bob ledger mallory occ rejected_effects_empty scenario sumOver transition treasury usd)
end T
namespace G
export Proofs.GlobalEconomicStateRefinementV2 (AmountRow ClaimantLiabilitiesBacked GlobalState OpenTerminalLiabilitiesCovered OwnedMatchesSupply amountAt amountForAsset amountForAssetDomain openTerminalAmountFor ownedFor staticGlobalState supplyFor)
end G

def balanceRows (asset domain : String) (balance : T.Principal → Int) :
    List T.Principal → List G.AmountRow
  | [] => []
  | p :: ps => ⟨p, asset, domain, balance p⟩ :: balanceRows asset domain balance ps

theorem balanceRows_total (asset domain queriedAsset : String)
    (balance : T.Principal → Int) (ps : List T.Principal) :
    G.amountForAsset (balanceRows asset domain balance ps) queriedAsset =
      if asset = queriedAsset then T.sumOver balance ps else 0 := by
  induction ps with
  | nil => simp [balanceRows, G.amountForAsset, T.sumOver]
  | cons p ps ih =>
      by_cases h : asset = queriedAsset
      · simp [balanceRows, G.amountForAsset, T.sumOver, h] at ih ⊢
        exact ih
      · simp [balanceRows, G.amountForAsset, h] at ih ⊢
        exact ih

structure State where
  localState : T.TransferState
  globalState : G.GlobalState

def Represents (ps : List T.Principal) (domain : String) (s : State) : Prop :=
  s.globalState.balances =
      balanceRows s.localState.policy.asset domain s.localState.balance ps ∧
  s.globalState.supplies = [⟨s.localState.policy.asset, s.localState.supplyAtoms⟩]

def RoleCoverage (ps : List T.Principal) (s : State) (cmd : T.Command) : Prop :=
  T.occ cmd.sender ps = 1 ∧ T.occ cmd.recipient ps = 1 ∧
    T.occ s.localState.policy.feeOwner ps = 1

/-- Only the account table is projected. This is not a global publication. -/
def step (ps : List T.Principal) (domain : String) (ctx : T.Context)
    (cmd : T.Command) (s : State) : State :=
  let result := T.transition ctx s.localState cmd
  match result.verdict with
  | .rejected _ => s
  | .accepted =>
      ⟨result.post, { s.globalState with
        balances := balanceRows result.post.policy.asset domain result.post.balance ps }⟩

/-- Equality of the entire frame preserves even fields absent from the
accounting predicates; metadata here stays static and is not publication-ready. -/
theorem step_frame (ps : List T.Principal) (domain : String) (ctx : T.Context)
    (cmd : T.Command) (s : State) :
    (step ps domain ctx cmd s).globalState =
      { s.globalState with balances := (step ps domain ctx cmd s).globalState.balances } := by
  cases h : (T.transition ctx s.localState cmd).verdict <;> simp [step, h]

theorem step_represents {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State} (hr : Represents ps domain s) :
    Represents ps domain (step ps domain ctx cmd s) := by
  cases h : (T.transition ctx s.localState cmd).verdict with
  | rejected code => simpa [step, h] using hr
  | accepted =>
      have hp := (T.accepted_post_eq h).1
      simp only [step, h, Represents]
      constructor
      · trivial
      · simpa [hp, T.acceptedState] using hr.2

/-- Conservation is derived from the existing command semantics, not stored
as a postcondition in an accepted witness. Fee-owner aliases are unrestricted. -/
theorem step_account_totals {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State}
    (hr : Represents ps domain s) (hc : RoleCoverage ps s cmd) (asset : String) :
    G.amountForAsset (step ps domain ctx cmd s).globalState.balances asset =
      G.amountForAsset s.globalState.balances asset := by
  cases h : (T.transition ctx s.localState cmd).verdict with
  | rejected code => simp [step, h]
  | accepted =>
      have conserved := T.accepted_conserves_total h ps hc.1 hc.2.1 hc.2.2
      have hp := (T.accepted_post_eq h).1
      simp only [step, h]
      rw [hr.1, balanceRows_total, balanceRows_total, conserved]
      simp [hp, T.acceptedState]

theorem step_owned_supply {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State}
    (hr : Represents ps domain s) (hc : RoleCoverage ps s cmd)
    (hpre : G.OwnedMatchesSupply s.globalState) :
    G.OwnedMatchesSupply (step ps domain ctx cmd s).globalState := by
  intro asset
  have totals := step_account_totals (ctx := ctx) hr hc asset
  have frame := step_frame ps domain ctx cmd s
  unfold G.ownedFor
  rw [frame]
  change G.amountForAsset (step ps domain ctx cmd s).globalState.balances asset +
    G.amountForAsset s.globalState.custody asset +
    G.amountForAsset s.globalState.reserves asset = G.supplyFor s.globalState.supplies asset
  rw [totals]
  exact hpre asset

def ExactAllocation (s : G.GlobalState) : Prop :=
  ∀ asset domain, G.amountForAssetDomain s.custody asset domain =
    G.amountForAssetDomain s.liabilities asset domain

theorem step_exact_allocation {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State}
    (hpre : ExactAllocation s.globalState) :
    ExactAllocation (step ps domain ctx cmd s).globalState := by
  rw [step_frame]
  exact hpre

theorem step_claimant_backing {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State}
    (hpre : G.ClaimantLiabilitiesBacked s.globalState) :
    G.ClaimantLiabilitiesBacked (step ps domain ctx cmd s).globalState := by
  rw [step_frame]
  exact hpre

theorem step_rejection_is_noop {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State} {code : T.RejectCode}
    (h : (T.transition ctx s.localState cmd).verdict = .rejected code) :
    step ps domain ctx cmd s = s ∧
      (T.transition ctx s.localState cmd).effects = Proofs.AssetTransferRefinementV1.AbstractEffects.empty := by
  exact ⟨by simp [step, h], T.rejected_effects_empty h⟩

/-- A policy guard, with authentic exact-command context as an external premise. -/
theorem accepted_sender_is_context_subject {ctx : T.Context} {cmd : T.Command}
    {s : State} (h : (T.transition ctx s.localState cmd).verdict = .accepted) :
    cmd.sender = ctx.subjectId := by
  exact ((T.accepted_iff_all_guards ctx s.localState cmd).mp h) .unauthorizedSubject

/-- Any change by this lift requires the sender to equal the supplied context
subject. Authenticating that context for this command remains a shell premise. -/
theorem step_changes_only_for_context_subject {ps : List T.Principal} {domain : String}
    {ctx : T.Context} {cmd : T.Command} {s : State}
    (hchange : step ps domain ctx cmd s ≠ s) : cmd.sender = ctx.subjectId := by
  cases h : (T.transition ctx s.localState cmd).verdict with
  | accepted => exact accepted_sender_is_context_subject h
  | rejected code => exact False.elim (hchange (by simp [step, h]))

abbrev Input := T.Context × T.Command

def run (ps : List T.Principal) (domain : String) : List Input → State → State
  | [], s => s
  | (ctx, cmd) :: rest, s => run ps domain rest (step ps domain ctx cmd s)

def TraceCoverage (ps : List T.Principal) (domain : String) : List Input → State → Prop
  | [], _ => True
  | (ctx, cmd) :: rest, s =>
      RoleCoverage ps s cmd ∧ TraceCoverage ps domain rest (step ps domain ctx cmd s)

theorem run_preserves_accounting {ps : List T.Principal} {domain : String}
    (inputs : List Input) (s : State)
    (hr : Represents ps domain s) (hc : TraceCoverage ps domain inputs s)
    (ho : G.OwnedMatchesSupply s.globalState)
    (ha : ExactAllocation s.globalState)
    (hb : G.ClaimantLiabilitiesBacked s.globalState) :
    Represents ps domain (run ps domain inputs s) ∧
    G.OwnedMatchesSupply (run ps domain inputs s).globalState ∧
    ExactAllocation (run ps domain inputs s).globalState ∧
    G.ClaimantLiabilitiesBacked (run ps domain inputs s).globalState := by
  induction inputs generalizing s with
  | nil => exact ⟨hr, ho, ha, hb⟩
  | cons input rest ih =>
      obtain ⟨ctx, cmd⟩ := input
      exact ih (step ps domain ctx cmd s) (step_represents hr) hc.2
        (step_owned_supply hr hc.1 ho) (step_exact_allocation ha) (step_claimant_backing hb)

/-! Concrete positive and premise-removal controls. Nonzero liabilities are
claimant addressed, with a nonzero open terminal obligation for the same key. -/

def principals : List T.Principal := [T.alice, T.bob, T.treasury]
def accountDomain : String := "zenoledger:accounts"
def claimDomain : String := "zenoledger:claims"

def demoLocal : T.TransferState := { T.acceptDistinct.pre with supplyAtoms := 125 }

def demoGlobal : G.GlobalState :=
  { G.staticGlobalState with
    balances := balanceRows T.usd accountDomain demoLocal.balance principals
    supplies := [⟨T.usd, 125⟩]
    custody := [⟨"vault", T.usd, claimDomain, 10⟩]
    liabilities := [⟨T.alice, T.usd, claimDomain, 10⟩]
    reserves := []
    terminalObligations := [⟨"claim-1", .assetTransfer, T.alice, T.usd, claimDomain, 10, .open⟩] }

def demo : State := ⟨demoLocal, demoGlobal⟩
def demoPost : State := step principals accountDomain T.acceptDistinct.ctx T.acceptDistinct.cmd demo

theorem demo_represents : Represents principals accountDomain demo := by
  constructor <;> rfl
theorem demo_coverage : RoleCoverage principals demo T.acceptDistinct.cmd := by
  unfold RoleCoverage
  decide

theorem demo_owned_supply : G.OwnedMatchesSupply demo.globalState := by
  intro asset
  by_cases h : T.usd = asset <;>
    simp [G.ownedFor, G.amountForAsset, G.supplyFor, demo, demoGlobal, demoLocal,
      principals, balanceRows, T.acceptDistinct, T.scenario, T.baseRows,
      T.ledger, T.bob, T.alice, T.treasury, h]

theorem demo_exact_allocation : ExactAllocation demo.globalState := by
  intro asset domain
  rfl

theorem demo_claimant_backing : G.ClaimantLiabilitiesBacked demo.globalState := by
  constructor
  · intro asset domain
    by_cases h : T.usd = asset ∧ claimDomain = domain <;>
      simp [demo, demoGlobal, G.amountForAssetDomain, h]
  · intro owner asset domain
    by_cases h : T.alice = owner ∧ T.usd = asset ∧ claimDomain = domain <;>
      simp [demo, demoGlobal, G.openTerminalAmountFor, G.amountAt, h]

theorem demo_nonempty_accepted :
    (T.transition T.acceptDistinct.ctx demo.localState T.acceptDistinct.cmd).verdict = .accepted ∧
    G.ownedFor demoPost.globalState T.usd = 125 ∧
    G.amountForAsset demoPost.globalState.balances T.usd = 115 ∧
    G.amountForAsset demoPost.globalState.custody T.usd = 10 ∧
    G.amountForAsset demoPost.globalState.liabilities T.usd = 10 ∧
    G.openTerminalAmountFor demoPost.globalState.terminalObligations T.alice T.usd claimDomain = 10 := by
  decide

theorem demo_derived_preservation :
    G.OwnedMatchesSupply demoPost.globalState ∧
    ExactAllocation demoPost.globalState ∧ G.ClaimantLiabilitiesBacked demoPost.globalState := by
  exact ⟨step_owned_supply demo_represents demo_coverage demo_owned_supply,
    step_exact_allocation demo_exact_allocation, step_claimant_backing demo_claimant_backing⟩

def demoWithFeeOwner (owner : T.Principal) : State :=
  { demo with localState := { demoLocal with policy := { demoLocal.policy with feeOwner := owner } } }

theorem fee_owner_alias_controls :
    G.ownedFor (step principals accountDomain T.acceptDistinct.ctx T.acceptDistinct.cmd
      (demoWithFeeOwner T.alice)).globalState T.usd = 125 ∧
    (step principals accountDomain T.acceptDistinct.ctx T.acceptDistinct.cmd
      (demoWithFeeOwner T.alice)).localState.balance T.alice = 70 ∧
    G.ownedFor (step principals accountDomain T.acceptDistinct.ctx T.acceptDistinct.cmd
      (demoWithFeeOwner T.bob)).globalState T.usd = 125 ∧
    (step principals accountDomain T.acceptDistinct.ctx T.acceptDistinct.cmd
      (demoWithFeeOwner T.bob)).localState.balance T.bob = 42 := by decide

def demoInputs : List Input :=
  [({ T.acceptDistinct.ctx with subjectId := T.mallory }, T.acceptDistinct.cmd),
    (T.acceptDistinct.ctx, T.acceptDistinct.cmd), (T.acceptDistinct.ctx, T.acceptDistinct.cmd)]

theorem demo_trace_coverage : TraceCoverage principals accountDomain demoInputs demo := by
  simp only [demoInputs, TraceCoverage, RoleCoverage]
  decide

theorem demo_trace_has_rejection_and_two_transfers :
    (T.transition { T.acceptDistinct.ctx with subjectId := T.mallory }
      demoLocal T.acceptDistinct.cmd).verdict = .rejected .unauthorizedSubject ∧
    (run principals accountDomain demoInputs demo).localState.balance T.alice = 36 ∧
    (run principals accountDomain demoInputs demo).localState.balance T.bob = 70 ∧
    (run principals accountDomain demoInputs demo).localState.balance T.treasury = 9 := by decide

theorem demo_trace_derived_preservation :
    Represents principals accountDomain (run principals accountDomain demoInputs demo) ∧
    G.OwnedMatchesSupply (run principals accountDomain demoInputs demo).globalState ∧
    ExactAllocation (run principals accountDomain demoInputs demo).globalState ∧
    G.ClaimantLiabilitiesBacked (run principals accountDomain demoInputs demo).globalState := by
  exact run_preserves_accounting demoInputs demo demo_represents demo_trace_coverage
    demo_owned_supply demo_exact_allocation demo_claimant_backing

/-- Omitting the fee owner loses two atoms in this finite observation. -/
theorem missing_principal_breaks_conservation :
    T.sumOver (T.transition T.acceptDistinct.ctx demoLocal T.acceptDistinct.cmd).post.balance
      [T.alice, T.bob] ≠ T.sumOver demoLocal.balance [T.alice, T.bob] := by decide

def extraCredit : G.GlobalState := { demoPost.globalState with balances :=
  ⟨T.bob, T.usd, accountDomain, 1⟩ :: demoPost.globalState.balances }

theorem extra_credit_breaks_owned_supply : ¬ G.OwnedMatchesSupply extraCredit := by
  intro h
  have impossible := h T.usd
  change (126 : Int) = 125 at impossible
  omega

def wrongClaimant : G.GlobalState := { demoPost.globalState with
  liabilities := [⟨T.mallory, T.usd, claimDomain, 10⟩] }

/-- Aggregate allocation alone cannot establish claimant identity or terminal coverage. -/
theorem wrong_claimant_keeps_totals_but_breaks_terminal :
    ExactAllocation wrongClaimant ∧ ¬ G.OpenTerminalLiabilitiesCovered wrongClaimant := by
  constructor
  · intro asset domain
    rfl
  · intro h
    have impossible := (h T.alice T.usd claimDomain).2
    change (10 : Int) ≤ 0 at impossible
    omega

end Proofs.AssetTransferGlobalPreservationV1
