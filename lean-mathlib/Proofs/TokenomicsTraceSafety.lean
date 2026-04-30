import Proofs.FiniteTraceBarriers
import Mathlib.Tactic

/-!
# Tokenomics Trace Safety

This packet imports the useful FIRE / post-AGI tokenomics math shape into the
ZenoDEX proof tree. The core rule is deliberately fail-closed:

- supply contraction must be proved stepwise,
- burns must be funded by a treasury/resource drawdown,
- controller outputs must preserve a positive-supply productivity ratio.

The theorem statements are generic over a transition system so they can be
instantiated by a DEX fee/buyback/burn controller, a bounty-auction reward
controller, or a future FIRE object admission gate.
-/

namespace Proofs
namespace TokenomicsTraceSafety

open FiniteTraceBarriers

abbrev MarketSystem (σ : Type*) := FiniteTraceBarriers.TransitionSystem σ

namespace MarketSystem

variable {σ : Type*}

abbrev TraceN (M : MarketSystem σ) := FiniteTraceBarriers.TransitionSystem.TraceN M

/-- Every tokenomics step leaves total circulating supply unchanged or lower. -/
def StepSupplyNonincreasing (M : MarketSystem σ) (S : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S t ≤ S s

/-- Every tokenomics step leaves supply at most a fixed factor of prior supply. -/
def StepSupplyLeFactor (M : MarketSystem σ) (S : σ → Rat) (q : Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S t ≤ q * S s

/-- Every supply burn is funded by a treasury or resource-account drawdown. -/
def StepBurnFundedByTreasury
    (M : MarketSystem σ) (S T : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S s - S t ≤ T s - T t

/-- The treasury or resource account is nonnegative at every state. -/
def TreasuryNonnegative (T : σ → Rat) : Prop :=
  ∀ s : σ, 0 ≤ T s

/-- Every step leaves productive output unchanged or higher. -/
def StepOutputNondecreasing (M : MarketSystem σ) (A : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → A s ≤ A t

/-- Productive output per unit of positive circulating supply. -/
def outputPerToken (A S : σ → Rat) (s : σ) : Rat :=
  A s / S s

/-- Terminal supply removed over a length-indexed trace. -/
def traceSupplyDrop {M : MarketSystem σ} (S : σ → Rat)
    {n : Nat} {s t : σ} (_hTrace : TraceN M n s t) : Rat :=
  S s - S t

theorem supply_le_of_traceN_stepSupplyNonincreasing
    (M : MarketSystem σ) (S : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ S s := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact (hSupply hStep).trans ih

theorem traceSupplyDrop_nonneg_of_stepSupplyNonincreasing
    (M : MarketSystem σ) (S : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace := by
  have hLe := supply_le_of_traceN_stepSupplyNonincreasing M S hSupply hTrace
  unfold traceSupplyDrop
  exact sub_nonneg.mpr hLe

theorem factor_pow_le_one
    {q : Rat} (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (n : Nat) :
    q ^ n ≤ 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        q ^ (n + 1) = q ^ n * q := by rw [pow_succ]
        _ ≤ 1 * 1 := mul_le_mul ih hqLeOne hqNonneg (by norm_num)
        _ = 1 := by norm_num

theorem factor_pow_mul_le_initial
    {q initial : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hInitial : 0 ≤ initial)
    (n : Nat) :
    q ^ n * initial ≤ initial := by
  have hPow : q ^ n ≤ 1 := factor_pow_le_one hqNonneg hqLeOne n
  calc
    q ^ n * initial ≤ 1 * initial := mul_le_mul_of_nonneg_right hPow hInitial
    _ = initial := by ring

theorem supply_le_factor_pow_of_traceN
    (M : MarketSystem σ) (S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q)
    (hFactor : StepSupplyLeFactor M S q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ q ^ n * S s := by
  induction hTrace with
  | nil =>
      simp
  | snoc hTrace hStep ih =>
      calc
        S _ ≤ q * S _ := hFactor hStep
        _ ≤ q * (q ^ _ * S _) := mul_le_mul_of_nonneg_left ih hqNonneg
        _ = q ^ (_ + 1) * S _ := by
          rw [pow_succ]
          ring

theorem supply_le_initial_of_traceN_factor
    (M : MarketSystem σ) (S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hFactor : StepSupplyLeFactor M S q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : 0 ≤ S s) :
    S t ≤ S s :=
  (supply_le_factor_pow_of_traceN M S hqNonneg hFactor hTrace).trans
    (factor_pow_mul_le_initial hqNonneg hqLeOne hInitial n)

theorem traceSupplyDrop_le_treasuryDrop_of_stepBurnFunded
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s - T t := by
  induction hTrace with
  | nil =>
      simp [traceSupplyDrop]
  | snoc hTrace hStep ih =>
      have hStepFunded := hFunded hStep
      unfold traceSupplyDrop at ih hStepFunded ⊢
      linarith

theorem traceSupplyDrop_le_initialTreasury_of_stepBurnFunded
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hTerminalTreasury : 0 ≤ T t) :
    traceSupplyDrop S hTrace ≤ T s := by
  have hDrop :=
    traceSupplyDrop_le_treasuryDrop_of_stepBurnFunded
      M S T hFunded hTrace
  unfold traceSupplyDrop at hDrop ⊢
  linarith

theorem traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s :=
  traceSupplyDrop_le_initialTreasury_of_stepBurnFunded
    M S T hFunded hTrace (hTreasury t)

theorem traceSupplyDrop_between_zero_and_initialTreasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ T s :=
  ⟨traceSupplyDrop_nonneg_of_stepSupplyNonincreasing M S hSupply hTrace,
    traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
      M S T hFunded hTreasury hTrace⟩

theorem terminalSupply_ge_initial_minus_treasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S s - T s ≤ S t := by
  have hDrop :=
    traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
      M S T hFunded hTreasury hTrace
  unfold traceSupplyDrop at hDrop
  linarith

theorem output_le_of_traceN_stepOutputNondecreasing
    (M : MarketSystem σ) (A : σ → Rat)
    (hOutput : StepOutputNondecreasing M A)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    A s ≤ A t := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hOutput hStep)

theorem outputPerToken_le_of_output_nondec_supply_noninc
    {A S : σ → Rat} {s t : σ}
    (hOutput : A s ≤ A t)
    (hOutputNonneg : 0 ≤ A s)
    (hTerminalSupplyPos : 0 < S t)
    (hSupply : S t ≤ S s) :
    outputPerToken A S s ≤ outputPerToken A S t := by
  have hInitialSupplyPos : 0 < S s :=
    hTerminalSupplyPos.trans_le hSupply
  unfold outputPerToken
  rw [div_le_div_iff₀ hInitialSupplyPos hTerminalSupplyPos]
  calc
    A s * S t ≤ A s * S s :=
      mul_le_mul_of_nonneg_left hSupply hOutputNonneg
    _ ≤ A t * S s :=
      mul_le_mul_of_nonneg_right hOutput hInitialSupplyPos.le

theorem outputPerToken_le_of_traceN_output_nondec_supply_factor
    (M : MarketSystem σ) (A S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hOutput : StepOutputNondecreasing M A)
    (hFactor : StepSupplyLeFactor M S q)
    (hOutputNonneg : ∀ s : σ, 0 ≤ A s)
    (hSupplyPos : ∀ s : σ, 0 < S s)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t := by
  have hOutputTrace :=
    output_le_of_traceN_stepOutputNondecreasing M A hOutput hTrace
  have hSupplyTrace :=
    supply_le_initial_of_traceN_factor
      M S hqNonneg hqLeOne hFactor hTrace (hSupplyPos s).le
  exact outputPerToken_le_of_output_nondec_supply_noninc
    hOutputTrace (hOutputNonneg s) (hSupplyPos t) hSupplyTrace

/--
Controller certificate: the controller may be arbitrary, but admission requires
these replayable facts before ZenoDEX can claim trace-level tokenomics safety.
-/
structure TokenomicsControllerGuard
    (M : MarketSystem σ) (A S T : σ → Rat) (q : Rat) : Prop where
  supplyFactor : StepSupplyLeFactor M S q
  burnFunded : StepBurnFundedByTreasury M S T
  outputNondecreasing : StepOutputNondecreasing M A
  treasuryNonnegative : TreasuryNonnegative T
  outputNonnegative : ∀ s : σ, 0 ≤ A s
  supplyPositive : ∀ s : σ, 0 < S s

namespace TokenomicsControllerGuard

theorem stepSupplyNonincreasing
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqLeOne : q ≤ 1) :
    StepSupplyNonincreasing M S := by
  intro s t hStep
  have hFactor := hGuard.supplyFactor hStep
  have hScale : q * S s ≤ 1 * S s :=
    mul_le_mul_of_nonneg_right hqLeOne (hGuard.supplyPositive s).le
  exact hFactor.trans (by simpa using hScale)

theorem traceSupplyDrop_between_zero_and_initialTreasury
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ T s :=
  _root_.Proofs.TokenomicsTraceSafety.MarketSystem.traceSupplyDrop_between_zero_and_initialTreasury
    M S T (hGuard.stepSupplyNonincreasing hqLeOne)
    hGuard.burnFunded hGuard.treasuryNonnegative hTrace

theorem terminalSupply_ge_initial_minus_treasury
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S s - T s ≤ S t :=
  _root_.Proofs.TokenomicsTraceSafety.MarketSystem.terminalSupply_ge_initial_minus_treasury
    M S T hGuard.burnFunded hGuard.treasuryNonnegative hTrace

theorem outputPerToken_le
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t :=
  outputPerToken_le_of_traceN_output_nondec_supply_factor
    M A S hqNonneg hqLeOne hGuard.outputNondecreasing
    hGuard.supplyFactor hGuard.outputNonnegative hGuard.supplyPositive hTrace

end TokenomicsControllerGuard

end MarketSystem

end TokenomicsTraceSafety
end Proofs
