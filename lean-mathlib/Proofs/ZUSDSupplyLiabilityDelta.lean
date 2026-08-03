import Mathlib

namespace ZenoDEX.ZUSDSupplyLiabilityDelta

/--
An abstract zUSD accounting state. `protocolFeeAccrual` must denote a current
outstanding fee fiber for `Balanced` to be a state invariant. The current Python
cumulative revenue counter establishes only the signed `DeltaCertificate` law.
-/
structure State where
  debt : Int
  ledgerSupply : Int
  protocolFeeAccrual : Int
  deriving DecidableEq, Repr

/-- A prospective scoped invariant once every custody and current fee fiber is represented. -/
def Balanced (state : State) : Prop :=
  state.debt = state.ledgerSupply + state.protocolFeeAccrual

/-- All represented quantities are valid monetary amounts. -/
def Nonnegative (state : State) : Prop :=
  0 ≤ state.debt ∧ 0 ≤ state.ledgerSupply ∧ 0 ≤ state.protocolFeeAccrual

/-- Mint principal to ledger supply and accrue the borrowing fee. -/
def mint (state : State) (principal fee : Int) : State :=
  { debt := state.debt + principal + fee
    ledgerSupply := state.ledgerSupply + principal
    protocolFeeAccrual := state.protocolFeeAccrual + fee }

/-- Burn ledger zUSD to reduce debt; protocol fee accrual is unchanged. -/
def burn (state : State) (amount : Int) : State :=
  { debt := state.debt - amount
    ledgerSupply := state.ledgerSupply - amount
    protocolFeeAccrual := state.protocolFeeAccrual }

/-- The exact signed-delta identity carried by the executable certificate. -/
def DeltaCertificate (pre post : State) : Prop :=
  post.debt - pre.debt =
    (post.ledgerSupply - pre.ledgerSupply) +
      (post.protocolFeeAccrual - pre.protocolFeeAccrual)

theorem mint_preserves_balance
    (state : State) (principal fee : Int) (h : Balanced state) :
    Balanced (mint state principal fee) := by
  simp only [Balanced, mint] at h ⊢
  omega

theorem mint_preserves_nonnegative
    (state : State) (principal fee : Int)
    (hState : Nonnegative state) (hPrincipal : 0 ≤ principal) (hFee : 0 ≤ fee) :
    Nonnegative (mint state principal fee) := by
  simp only [Nonnegative, mint] at hState ⊢
  omega

theorem burn_preserves_balance
    (state : State) (amount : Int) (h : Balanced state) :
    Balanced (burn state amount) := by
  simp only [Balanced, burn] at h ⊢
  omega

theorem burn_preserves_nonnegative
    (state : State) (amount : Int)
    (hState : Nonnegative state) (hBalanced : Balanced state)
    (hAvailable : amount ≤ state.ledgerSupply) :
    Nonnegative (burn state amount) := by
  simp only [Nonnegative, Balanced, burn] at hState hBalanced ⊢
  omega

theorem mint_has_delta_certificate
    (state : State) (principal fee : Int) :
    DeltaCertificate state (mint state principal fee) := by
  simp only [DeltaCertificate, mint]
  ring

theorem burn_has_delta_certificate
    (state : State) (amount : Int) :
    DeltaCertificate state (burn state amount) := by
  simp only [DeltaCertificate, burn]
  ring

/-- A balanced pre-state plus the delta certificate is exactly balance preservation. -/
theorem delta_certificate_preserves_balance
    (pre post : State) (hPre : Balanced pre)
    (hDelta : DeltaCertificate pre post) :
    Balanced post := by
  unfold Balanced DeltaCertificate at *
  omega

/-- Consecutive exact certificates compose without inspecting the intermediate state. -/
theorem delta_certificate_transitive
    (first middle last : State)
    (hFirst : DeltaCertificate first middle)
    (hSecond : DeltaCertificate middle last) :
    DeltaCertificate first last := by
  unfold DeltaCertificate at *
  omega

#print axioms delta_certificate_preserves_balance
#print axioms delta_certificate_transitive

end ZenoDEX.ZUSDSupplyLiabilityDelta
