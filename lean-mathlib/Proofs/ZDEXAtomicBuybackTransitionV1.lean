import Init.Omega

/-!
Total abstract transition semantics for one same-occurrence ZDEX buy-and-burn.

The model deliberately contains only the observations needed by the safety
claim: closed semantic gates, exact integer amounts, replay state, terminal
state, four accounting locations, and the canonical economic effect summary.
Every input has exactly one result. Rejection carries only a closed code; its
post-state and empty effect summary are derived from the explicit input state.
Acceptance moves quote atoms into the
selected pool, removes purchased ZDEX from that pool, burns exactly that
amount from live supply, consumes the occurrence, and closes the transient
burn obligation.

Nonclaims: this file does not prove that Python, Rust, RISC0, Tau, a profile,
an Oracle, or a deployed verifier establishes these abstract gates. It does
not prove CPMM pricing, route optimality, liveness, MEV resistance, migration,
or atomic durable publication. Those require explicit refinement theorems and
runtime evidence.
-/

namespace Proofs
namespace ZDEXAtomicBuybackTransitionV1

/-- Closed semantic gates checked before arithmetic state construction. -/
structure Gates where
  routeBound : Bool
  authorityBound : Bool
  oracleFinal : Bool
  budgetBound : Bool
  priceSafe : Bool
  deriving DecidableEq, Repr

/-- Minimum sufficient accounting state for the atomic transition theorem. -/
structure State where
  quoteSource : Nat
  quotePool : Nat
  zdexPool : Nat
  liveSupply : Nat
  occurrenceConsumed : Bool
  burnPending : Bool
  deriving DecidableEq, Repr

structure Command where
  quoteSpend : Nat
  purchasedZdex : Nat
  deriving DecidableEq, Repr

/-- Canonical observations emitted by the accepted abstract transition. -/
structure Effects where
  quoteMoved : Nat
  zdexPurchased : Nat
  zdexBurned : Nat
  occurrenceConsumed : Bool
  terminalClosed : Bool
  deriving DecidableEq, Repr

def Effects.empty : Effects where
  quoteMoved := 0
  zdexPurchased := 0
  zdexBurned := 0
  occurrenceConsumed := false
  terminalClosed := false

inductive RejectCode where
  | routeMismatch
  | authorityMismatch
  | oracleMismatch
  | budgetMismatch
  | priceUnsafe
  | replay
  | terminalConflict
  | invalidAmount
  deriving DecidableEq, Repr

/-- Rejection cannot represent a distinct post-state or nonempty effects. -/
inductive Result where
  | accepted (postState : State) (effects : Effects)
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

def Result.postState (preState : State) : Result → State
  | .accepted postState _ => postState
  | .rejected _ => preState

def Result.effects : Result → Effects
  | .accepted _ effects => effects
  | .rejected _ => Effects.empty

/-- Exact precedence for all non-arithmetic rejection gates. -/
def firstReject (state : State) (gates : Gates) : Option RejectCode :=
  if !gates.routeBound then some .routeMismatch
  else if !gates.authorityBound then some .authorityMismatch
  else if !gates.oracleFinal then some .oracleMismatch
  else if !gates.budgetBound then some .budgetMismatch
  else if !gates.priceSafe then some .priceUnsafe
  else if state.occurrenceConsumed then some .replay
  else if state.burnPending then some .terminalConflict
  else none

def ValidAmounts (state : State) (command : Command) : Prop :=
  0 < command.quoteSpend ∧
    0 < command.purchasedZdex ∧
    command.quoteSpend ≤ state.quoteSource ∧
    command.purchasedZdex ≤ state.zdexPool ∧
    command.purchasedZdex ≤ state.liveSupply

instance validAmountsDecidable (state : State) (command : Command) :
    Decidable (ValidAmounts state command) := by
  unfold ValidAmounts
  infer_instance

def acceptedPost (state : State) (command : Command) : State where
  quoteSource := state.quoteSource - command.quoteSpend
  quotePool := state.quotePool + command.quoteSpend
  zdexPool := state.zdexPool - command.purchasedZdex
  liveSupply := state.liveSupply - command.purchasedZdex
  occurrenceConsumed := true
  burnPending := false

def acceptedEffects (command : Command) : Effects where
  quoteMoved := command.quoteSpend
  zdexPurchased := command.purchasedZdex
  zdexBurned := command.purchasedZdex
  occurrenceConsumed := true
  terminalClosed := true

/-- Total deterministic transition with explicit reject precedence. -/
def transition (state : State) (command : Command) (gates : Gates) : Result :=
  match firstReject state gates with
  | some code => .rejected code
  | none =>
      if ValidAmounts state command then
        .accepted (acceptedPost state command) (acceptedEffects command)
      else
        .rejected .invalidAmount

theorem firstReject_none_iff
    (state : State) (gates : Gates) :
    firstReject state gates = none ↔
      gates.routeBound = true ∧
      gates.authorityBound = true ∧
      gates.oracleFinal = true ∧
      gates.budgetBound = true ∧
      gates.priceSafe = true ∧
      state.occurrenceConsumed = false ∧
      state.burnPending = false := by
  cases hRoute : gates.routeBound <;>
    cases hAuthority : gates.authorityBound <;>
    cases hOracle : gates.oracleFinal <;>
    cases hBudget : gates.budgetBound <;>
    cases hPrice : gates.priceSafe <;>
    cases hReplay : state.occurrenceConsumed <;>
    cases hTerminal : state.burnPending <;>
    simp [firstReject, hRoute, hAuthority, hOracle, hBudget, hPrice,
      hReplay, hTerminal]

theorem transition_is_total
    (state : State) (command : Command) (gates : Gates) :
    (∃ post effects, transition state command gates = .accepted post effects) ∨
      (∃ code, transition state command gates = .rejected code) := by
  unfold transition
  cases hReject : firstReject state gates with
  | some code => exact Or.inr ⟨code, rfl⟩
  | none =>
      by_cases hAmounts : ValidAmounts state command
      · exact Or.inl ⟨acceptedPost state command, acceptedEffects command, by simp [hAmounts]⟩
      · exact Or.inr ⟨.invalidAmount, by simp [hAmounts]⟩

theorem rejected_is_exact_noop
    (state : State) (command : Command) (gates : Gates) (code : RejectCode)
    (hRejected : transition state command gates = .rejected code) :
    (transition state command gates).postState state = state ∧
      (transition state command gates).effects = Effects.empty := by
  rw [hRejected]
  constructor <;> rfl

theorem duplicate_occurrence_rejects_replay
    (state : State) (command : Command) (gates : Gates)
    (hRoute : gates.routeBound = true)
    (hAuthority : gates.authorityBound = true)
    (hOracle : gates.oracleFinal = true)
    (hBudget : gates.budgetBound = true)
    (hPrice : gates.priceSafe = true)
    (hReplay : state.occurrenceConsumed = true) :
    transition state command gates = .rejected .replay := by
  simp [transition, firstReject, hRoute, hAuthority, hOracle, hBudget,
    hPrice, hReplay]

theorem accepted_iff
    (state post : State) (command : Command) (gates : Gates) (effects : Effects) :
    transition state command gates = .accepted post effects ↔
      firstReject state gates = none ∧
      ValidAmounts state command ∧
      post = acceptedPost state command ∧
      effects = acceptedEffects command := by
  unfold transition
  cases hReject : firstReject state gates with
  | some code => simp
  | none =>
      by_cases hAmounts : ValidAmounts state command <;>
        simp [hAmounts, eq_comm]

/-- Every accepted result satisfies the complete represented safety contract. -/
theorem accepted_safety
    (state post : State) (command : Command) (gates : Gates) (effects : Effects)
    (hAccepted : transition state command gates = .accepted post effects) :
    firstReject state gates = none ∧
      ValidAmounts state command ∧
      (gates.routeBound = true ∧
        gates.authorityBound = true ∧
        gates.oracleFinal = true ∧
        gates.budgetBound = true ∧
        gates.priceSafe = true ∧
        state.occurrenceConsumed = false ∧
        state.burnPending = false) ∧
      state.quoteSource + state.quotePool = post.quoteSource + post.quotePool ∧
      post.zdexPool + command.purchasedZdex = state.zdexPool ∧
      post.liveSupply + command.purchasedZdex = state.liveSupply ∧
      effects.quoteMoved = command.quoteSpend ∧
      effects.zdexPurchased = effects.zdexBurned ∧
      effects.zdexBurned = command.purchasedZdex ∧
      post.occurrenceConsumed = true ∧
      post.burnPending = false ∧
      effects.occurrenceConsumed = true ∧
      effects.terminalClosed = true := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨hGates, hAmounts, rfl, rfl⟩
  have hGateFacts := (firstReject_none_iff state gates).mp hGates
  rcases hAmounts with ⟨_hQuotePositive, _hZdexPositive,
    hQuoteFits, hPoolFits, hSupplyFits⟩
  refine ⟨hGates, ?_, hGateFacts, ?_⟩
  · exact ⟨_hQuotePositive, _hZdexPositive, hQuoteFits, hPoolFits, hSupplyFits⟩
  simp [acceptedPost, acceptedEffects]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- One concrete positive case proves that the accepted branch is reachable. -/
def nonvacuityState : State where
  quoteSource := 7
  quotePool := 20
  zdexPool := 13
  liveSupply := 100
  occurrenceConsumed := false
  burnPending := false

def nonvacuityCommand : Command where
  quoteSpend := 3
  purchasedZdex := 3

def nonvacuityGates : Gates where
  routeBound := true
  authorityBound := true
  oracleFinal := true
  budgetBound := true
  priceSafe := true

theorem nonvacuity_accepts :
    transition nonvacuityState nonvacuityCommand nonvacuityGates =
      .accepted
        (acceptedPost nonvacuityState nonvacuityCommand)
        (acceptedEffects nonvacuityCommand) := by
  decide

end ZDEXAtomicBuybackTransitionV1
end Proofs
