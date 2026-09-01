import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# GlobalSettlementABI V1 claimant/custody relation

This file isolates a bounded-cardinality accounting model for the additional
`GlobalSettlementABI V1` claimant/custody checks.  It has one asset, two
claimants, two accounting-domain labels, natural-number atom counts, and one
aggregate OPEN-terminal amount per claimant.

The necessary relation has two parts:

* liabilities in each accounting domain fit inside the custody column for that
  same domain; and
* each claimant's aggregate OPEN-terminal amount fits inside that claimant's
  liabilities across both domains.

`ExactAllocationWitness` records stronger, certificate-side partition
equalities.  Its first theorem establishes that the two inequalities are
necessary consequences of exact partitions.  The deposit and drain theorems
then show that exact coordinate updates preserve the necessary relation under
their stated arithmetic premises.

The counterexamples are part of the result.  They show that total-only backing,
claimant-erased terminal coverage, and reserve-inclusive backing are strictly
weaker.  The final theorems show that removing `liability_domain` from a
terminal record is non-injective, so no function of the projected V1 record can
recover the domain for every domain-bound source record.

## Claim boundary

`Domain` values are uninterpreted accounting labels.  The words custody,
liability, reserve, claimant, and lane root name ledger fields only.  This file
does not model canonical bytes, hashes, roots, lane execution, effects, replay,
u128 overflow, runtime refinement, verifier admission, settlement authority,
release status, legal custody, or production safety.  It proves only the
bounded statements written below.
-/

namespace Proofs
namespace GlobalClaimantCustodyRelationV1

/-! ## Bounded state and necessary relation -/

inductive Claimant where
  | alice
  | bob
  deriving DecidableEq, Repr

inductive Domain where
  | hot
  | cold
  deriving DecidableEq, Repr

/-- A one-asset accounting state with exactly two claimants and two domains. -/
structure State where
  custody : Domain → Nat
  liabilities : Claimant → Domain → Nat
  reserves : Domain → Nat
  openTerminal : Claimant → Nat

def liabilityInDomain (state : State) (domain : Domain) : Nat :=
  state.liabilities .alice domain + state.liabilities .bob domain

def liabilityForClaimant (state : State) (claimant : Claimant) : Nat :=
  state.liabilities claimant .hot + state.liabilities claimant .cold

def totalLiabilities (state : State) : Nat :=
  liabilityInDomain state .hot + liabilityInDomain state .cold

def totalCustody (state : State) : Nat :=
  state.custody .hot + state.custody .cold

/-- R1: every domain's liabilities fit inside custody in that same domain. -/
def SameDomainLiabilitiesBacked (state : State) : Prop :=
  ∀ domain, liabilityInDomain state domain ≤ state.custody domain

/-- R2: every claimant's OPEN-terminal total fits inside that claimant's
liabilities across the two domains.  Zero OPEN totals are permitted. -/
def OpenTerminalClaimsCovered (state : State) : Prop :=
  ∀ claimant, state.openTerminal claimant ≤ liabilityForClaimant state claimant

def NecessaryRelation (state : State) : Prop :=
  SameDomainLiabilitiesBacked state ∧ OpenTerminalClaimsCovered state

/-- Certificate-side slack values turn the two necessary inequalities into
exact partition equalities.  These values are evidence, not V1 wire fields. -/
structure ExactAllocationWitness (state : State) where
  unencumberedCustody : Domain → Nat
  nonOpenLiability : Claimant → Nat
  custodyPartition : ∀ domain,
    state.custody domain =
      liabilityInDomain state domain + unencumberedCustody domain
  liabilityPartition : ∀ claimant,
    liabilityForClaimant state claimant =
      state.openTerminal claimant + nonOpenLiability claimant

/-- Exact certificate-side partitions imply both necessary V1 inequalities. -/
theorem exactAllocation_implies_necessaryRelation
    {state : State} (witness : ExactAllocationWitness state) :
    NecessaryRelation state := by
  constructor
  · intro domain
    rw [witness.custodyPartition domain]
    omega
  · intro claimant
    rw [witness.liabilityPartition claimant]
    omega

def balancedState : State where
  custody
    | .hot => 10
    | .cold => 8
  liabilities
    | .alice, .hot => 6
    | .alice, .cold => 2
    | .bob, .hot => 4
    | .bob, .cold => 6
  reserves _ := 0
  openTerminal
    | .alice => 8
    | .bob => 10

/-- Exact zero-slack allocation evidence for `balancedState`. -/
def balancedAllocation : ExactAllocationWitness balancedState where
  unencumberedCustody _ := 0
  nonOpenLiability _ := 0
  custodyPartition := by
    intro domain
    cases domain <;> norm_num [balancedState, liabilityInDomain]
  liabilityPartition := by
    intro claimant
    cases claimant <;> norm_num [balancedState, liabilityForClaimant]

/-- Concrete non-vacuity witness for the necessary relation. -/
theorem necessaryRelation_nonvacuous : NecessaryRelation balancedState := by
  exact exactAllocation_implies_necessaryRelation balancedAllocation

/-! ## Exact coordinate transitions -/

/-- Deposit adds the same amount to one domain's custody, one claimant/domain
liability coordinate, and that claimant's OPEN-terminal total. -/
def deposit (state : State) (claimant : Claimant) (domain : Domain)
    (amount : Nat) : State where
  custody observedDomain :=
    if observedDomain = domain then state.custody observedDomain + amount
    else state.custody observedDomain
  liabilities observedClaimant observedDomain :=
    if observedClaimant = claimant ∧ observedDomain = domain then
      state.liabilities observedClaimant observedDomain + amount
    else
      state.liabilities observedClaimant observedDomain
  reserves := state.reserves
  openTerminal observedClaimant :=
    if observedClaimant = claimant then
      state.openTerminal observedClaimant + amount
    else
      state.openTerminal observedClaimant

/-- An exact same-domain deposit preserves both necessary inequalities. -/
theorem deposit_preserves_necessaryRelation
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : NecessaryRelation state) :
    NecessaryRelation (deposit state claimant domain amount) := by
  rcases admitted with ⟨domainBacking, claimantCoverage⟩
  constructor
  · intro observedDomain
    specialize domainBacking observedDomain
    cases claimant <;> cases domain <;> cases observedDomain <;>
      simp only [liabilityInDomain, deposit, reduceCtorEq, and_true, and_false,
        if_true, if_false] at domainBacking ⊢ <;> omega
  · intro observedClaimant
    specialize claimantCoverage observedClaimant
    cases claimant <;> cases domain <;> cases observedClaimant <;>
      simp only [liabilityForClaimant, deposit, reduceCtorEq, and_true, and_false,
        if_true, if_false] at claimantCoverage ⊢ <;>
        omega

/-- Drain subtracts the same amount from one domain's custody, one
claimant/domain liability coordinate, and that claimant's OPEN-terminal total.
The theorem below requires the amount to be available in all three fields. -/
def drain (state : State) (claimant : Claimant) (domain : Domain)
    (amount : Nat) : State where
  custody observedDomain :=
    if observedDomain = domain then state.custody observedDomain - amount
    else state.custody observedDomain
  liabilities observedClaimant observedDomain :=
    if observedClaimant = claimant ∧ observedDomain = domain then
      state.liabilities observedClaimant observedDomain - amount
    else
      state.liabilities observedClaimant observedDomain
  reserves := state.reserves
  openTerminal observedClaimant :=
    if observedClaimant = claimant then
      state.openTerminal observedClaimant - amount
    else
      state.openTerminal observedClaimant

/-- An exact drain preserves the necessary relation when subtraction cannot
truncate any of the three updated coordinates. -/
theorem drain_preserves_necessaryRelation
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : NecessaryRelation state)
    (amountWithinCustody : amount ≤ state.custody domain)
    (amountWithinLiability : amount ≤ state.liabilities claimant domain)
    (amountWithinOpenTerminal : amount ≤ state.openTerminal claimant) :
    NecessaryRelation (drain state claimant domain amount) := by
  rcases admitted with ⟨domainBacking, claimantCoverage⟩
  constructor
  · intro observedDomain
    specialize domainBacking observedDomain
    cases claimant <;> cases domain <;> cases observedDomain <;>
      simp only [liabilityInDomain, drain, reduceCtorEq, and_true, and_false,
        if_true, if_false] at domainBacking ⊢ <;> omega
  · intro observedClaimant
    specialize claimantCoverage observedClaimant
    cases claimant <;> cases domain <;> cases observedClaimant <;>
      simp only [liabilityForClaimant, drain, reduceCtorEq, and_true, and_false,
        if_true, if_false] at claimantCoverage ⊢ <;> omega

/-! ## Minimized weaker-relation counterexamples -/

def AggregateLiabilitiesBacked (state : State) : Prop :=
  totalLiabilities state ≤ totalCustody state

def crossDomainBackingState : State where
  custody
    | .hot => 0
    | .cold => 1
  liabilities
    | .alice, .hot => 1
    | _, _ => 0
  reserves _ := 0
  openTerminal _ := 0

/-- Total-only backing accepts one hot-domain liability atom backed only by one
cold-domain custody atom; same-domain backing rejects the state. -/
theorem aggregateOnly_permits_crossDomainBacking :
    AggregateLiabilitiesBacked crossDomainBackingState ∧
      ¬ SameDomainLiabilitiesBacked crossDomainBackingState := by
  constructor
  · norm_num [AggregateLiabilitiesBacked, totalLiabilities, totalCustody,
      liabilityInDomain, crossDomainBackingState]
  · intro sameDomain
    have hotBacking := sameDomain .hot
    norm_num [liabilityInDomain, crossDomainBackingState] at hotBacking

def AggregateOpenClaimsCovered (state : State) : Prop :=
  state.openTerminal .alice + state.openTerminal .bob ≤ totalLiabilities state

def claimantSwapState : State where
  custody
    | .hot => 1
    | .cold => 0
  liabilities
    | .alice, .hot => 1
    | _, _ => 0
  reserves _ := 0
  openTerminal
    | .alice => 0
    | .bob => 1

/-- Claimant-erased aggregate coverage accepts Bob's OPEN claim against only
Alice's liability.  Claimant-specific coverage rejects the substitution. -/
theorem aggregateClaimants_permit_claimantSwap :
    SameDomainLiabilitiesBacked claimantSwapState ∧
      AggregateOpenClaimsCovered claimantSwapState ∧
      ¬ OpenTerminalClaimsCovered claimantSwapState := by
  refine ⟨?_, ?_, ?_⟩
  · intro domain
    cases domain <;> norm_num [liabilityInDomain, claimantSwapState]
  · norm_num [AggregateOpenClaimsCovered, totalLiabilities, liabilityInDomain,
      claimantSwapState]
  · intro claimantCoverage
    have bobCoverage := claimantCoverage .bob
    norm_num [liabilityForClaimant, claimantSwapState] at bobCoverage

def CustodyOrReserveBacked (state : State) : Prop :=
  ∀ domain,
    liabilityInDomain state domain ≤ state.custody domain + state.reserves domain

def reserveMaskingState : State where
  custody _ := 0
  liabilities
    | .alice, .hot => 1
    | _, _ => 0
  reserves
    | .hot => 1
    | .cold => 0
  openTerminal _ := 0

/-- Reserve-inclusive backing accepts a state with zero custody behind one
hot-domain liability atom; custody-only same-domain backing rejects it. -/
theorem reservesCanMaskMissingCustody :
    CustodyOrReserveBacked reserveMaskingState ∧
      ¬ SameDomainLiabilitiesBacked reserveMaskingState := by
  constructor
  · intro domain
    cases domain <;> norm_num [CustodyOrReserveBacked, liabilityInDomain,
      reserveMaskingState]
  · intro sameDomain
    have hotBacking := sameDomain .hot
    norm_num [liabilityInDomain, reserveMaskingState] at hotBacking

/-! ## V1 terminal domain-erasure boundary -/

inductive TerminalStatus where
  | open
  | drained
  | tombstoned
  deriving DecidableEq, Repr

/-- A certificate-side terminal record carrying the exact liability domain. -/
structure DomainBoundTerminal where
  obligationId : Nat
  claimant : Claimant
  laneRoot : Nat
  liabilityDomain : Domain
  amount : Nat
  status : TerminalStatus
  deriving DecidableEq, Repr

/-- The relevant V1 terminal projection, which has no liability-domain field. -/
structure TerminalProjectionV1 where
  obligationId : Nat
  claimant : Claimant
  laneRoot : Nat
  amount : Nat
  status : TerminalStatus
  deriving DecidableEq, Repr

def eraseLiabilityDomain (terminal : DomainBoundTerminal) : TerminalProjectionV1 where
  obligationId := terminal.obligationId
  claimant := terminal.claimant
  laneRoot := terminal.laneRoot
  amount := terminal.amount
  status := terminal.status

def hotTerminal : DomainBoundTerminal where
  obligationId := 7
  claimant := .alice
  laneRoot := 19
  liabilityDomain := .hot
  amount := 10
  status := .open

def coldTerminal : DomainBoundTerminal where
  obligationId := 7
  claimant := .alice
  laneRoot := 19
  liabilityDomain := .cold
  amount := 10
  status := .open

/-- Two records differing only in liability domain have the same V1
projection. -/
theorem terminalProjection_domainErasure_witness :
    hotTerminal ≠ coldTerminal ∧
      eraseLiabilityDomain hotTerminal = eraseLiabilityDomain coldTerminal := by
  constructor
  · decide
  · rfl

/-- Erasing `liabilityDomain` is non-injective even with claimant, lane root,
identity, amount, and status fixed. -/
theorem terminalProjection_domainErasure_notInjective :
    ¬ Function.Injective eraseLiabilityDomain := by
  intro injective
  exact terminalProjection_domainErasure_witness.1
    (injective terminalProjection_domainErasure_witness.2)

/-- No deterministic function of the V1 projection can recover every erased
domain-bound terminal record. -/
theorem terminalProjection_hasNoUniversalDomainRecovery :
    ¬ ∃ recover : TerminalProjectionV1 → DomainBoundTerminal,
      Function.LeftInverse recover eraseLiabilityDomain := by
  rintro ⟨recover, recoversEverySource⟩
  exact terminalProjection_domainErasure_notInjective recoversEverySource.injective

end GlobalClaimantCustodyRelationV1
end Proofs
