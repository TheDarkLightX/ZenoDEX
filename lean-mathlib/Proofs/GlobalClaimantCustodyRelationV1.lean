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

The stronger exact current-profile relation requires custody to equal visible
claimant liabilities in each domain.  `State.reserves` is excluded from that
relation: `necessaryRelation_independent_of_reserves` and
`exactCurrentProfileCustody_independent_of_reserves` state that exclusion as
definitional equivalences.  The reserve column remains in this bounded state
only to express and refute the reserve-inclusive weaker relation below.  The
exact equality is scoped to the current profile, whose V1 bytes have no
asset/amount representation for a pending registered external obligation.

`ExactAllocationWitness` records stronger, certificate-side partition
equalities.  Its first theorem establishes that the two inequalities are
necessary consequences of exact partitions; `noUnclassified_premise_is_necessary`
shows that the zero-unclassified-custody premise of the exact current-profile
consequence cannot be dropped.  The deposit and drain theorems then show that
exact coordinate updates preserve the necessary relation and the exact
current-profile relation.  Deposit needs no arithmetic premise.  Only drain
requires the amount to fit inside each of the three updated coordinates, so that
natural-number subtraction cannot truncate (the exact-custody drain lemma alone
needs just the custody and liability bounds).  Neither transition changes
`State.reserves`; `deposit_preserves_reserves` and `drain_preserves_reserves`
record that by `rfl`.

The counterexamples are part of the result.  Total-only backing,
claimant-erased terminal coverage, and reserve-inclusive backing are strictly
weaker than the same-domain and claimant-specific checks: the forward
implications are proved by `sameDomainBacked_implies_aggregateBacked`,
`openTerminalCovered_implies_aggregateCovered`, and
`sameDomainBacked_implies_reserveInclusiveBacking`, and the minimized
counterexamples refute each converse.  `overCollateralised_isBacked_notExact`
exhibits a state that satisfies same-domain backing but not exact
current-profile custody, so the exact relation is not a consequence of the
necessary inequalities.  The final theorems show that removing
`liability_domain` from a terminal record is non-injective, so no function of
the projected V1 record can recover the domain for every domain-bound source
record.

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

/-- R3: current-profile custody is exactly the sum of visible claimant
liabilities in the same domain.  `State.reserves` is deliberately excluded. -/
def ExactCurrentProfileCustody (state : State) : Prop :=
  ∀ domain, state.custody domain = liabilityInDomain state domain

def ExactCurrentProfileRelation (state : State) : Prop :=
  NecessaryRelation state ∧ ExactCurrentProfileCustody state

/-- Reserve independence of the necessary relation: replacing the reserve
column by any other column leaves `NecessaryRelation` unchanged.  The proof is
`Iff.rfl` because neither R1 nor R2 reads `State.reserves`, so both sides are
definitionally the same proposition.  This is the formal statement, cited by
the packet, that reserves do not influence the necessary relation. -/
theorem necessaryRelation_independent_of_reserves
    (state : State) (reserves : Domain → Nat) :
    NecessaryRelation { state with reserves := reserves } ↔
      NecessaryRelation state :=
  Iff.rfl

/-- Reserve independence of exact current-profile custody: replacing the
reserve column by any other column leaves `ExactCurrentProfileCustody`
unchanged.  The proof is `Iff.rfl` because R3 compares custody with visible
liabilities only and never reads `State.reserves`.  This is the formal
statement, cited by the packet, that reserves are excluded from the exact
current-profile relation. -/
theorem exactCurrentProfileCustody_independent_of_reserves
    (state : State) (reserves : Domain → Nat) :
    ExactCurrentProfileCustody { state with reserves := reserves } ↔
      ExactCurrentProfileCustody state :=
  Iff.rfl

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

/-- With no unclassified custody bucket, exact allocation evidence implies the
exact current-profile custody relation as well as the necessary checks. -/
theorem exactAllocation_noUnclassified_implies_exactCurrentProfileRelation
    {state : State} (witness : ExactAllocationWitness state)
    (noUnclassified : ∀ domain, witness.unencumberedCustody domain = 0) :
    ExactCurrentProfileRelation state := by
  constructor
  · exact exactAllocation_implies_necessaryRelation witness
  · intro domain
    rw [witness.custodyPartition domain, noUnclassified domain]
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

/-- Concrete non-vacuity witness for the exact current-profile relation. -/
theorem exactCurrentProfileRelation_nonvacuous :
    ExactCurrentProfileRelation balancedState := by
  apply exactAllocation_noUnclassified_implies_exactCurrentProfileRelation balancedAllocation
  intro domain
  cases domain <;> rfl

/-- Hot custody of ten atoms behind six atoms of hot liability: same-domain
backed, with four atoms of unclassified hot custody. -/
def overCollateralisedState : State where
  custody
    | .hot => 10
    | .cold => 0
  liabilities
    | .alice, .hot => 6
    | _, _ => 0
  reserves _ := 0
  openTerminal _ := 0

/-- `overCollateralisedState` satisfies same-domain backing (R1) and violates
exact current-profile custody (R3): hot custody strictly exceeds hot
liabilities.  R3 is therefore not a consequence of R1. -/
theorem overCollateralised_isBacked_notExact :
    SameDomainLiabilitiesBacked overCollateralisedState ∧
      ¬ ExactCurrentProfileCustody overCollateralisedState := by
  constructor
  · intro domain
    cases domain <;> norm_num [liabilityInDomain, overCollateralisedState]
  · intro exactCustody
    have hotCustody := exactCustody .hot
    norm_num [liabilityInDomain, overCollateralisedState] at hotCustody

/-- Exact allocation evidence for `overCollateralisedState` whose hot
unencumbered-custody bucket holds the four surplus atoms. -/
def overCollateralisedAllocation : ExactAllocationWitness overCollateralisedState where
  unencumberedCustody
    | .hot => 4
    | .cold => 0
  nonOpenLiability
    | .alice => 6
    | .bob => 0
  custodyPartition := by
    intro domain
    cases domain <;> norm_num [overCollateralisedState, liabilityInDomain]
  liabilityPartition := by
    intro claimant
    cases claimant <;> norm_num [overCollateralisedState, liabilityForClaimant]

/-- The `noUnclassified` premise of
`exactAllocation_noUnclassified_implies_exactCurrentProfileRelation` cannot be
dropped: `overCollateralisedAllocation` is a well-formed exact allocation
witness whose hot unencumbered-custody bucket is four, not zero, and
`overCollateralised_isBacked_notExact` shows its state fails exact
current-profile custody. -/
theorem noUnclassified_premise_is_necessary :
    ¬ ∀ domain, overCollateralisedAllocation.unencumberedCustody domain = 0 := by
  intro allZero
  have hotUnclassified :
      overCollateralisedAllocation.unencumberedCustody .hot = 4 := rfl
  have hotZero := allZero .hot
  omega

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

/-- `deposit` copies the reserve column unchanged: reserves are not a deposit
coordinate, so the post-state reserve column is definitionally the pre-state
column. -/
theorem deposit_preserves_reserves
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat) :
    (deposit state claimant domain amount).reserves = state.reserves :=
  rfl

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

/-- The exact same-domain deposit also preserves exact current-profile
custody. -/
theorem deposit_preserves_exactCurrentProfileCustody
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : ExactCurrentProfileCustody state) :
    ExactCurrentProfileCustody (deposit state claimant domain amount) := by
  intro observedDomain
  specialize admitted observedDomain
  cases claimant <;> cases domain <;> cases observedDomain <;>
    simp only [liabilityInDomain, deposit,
      reduceCtorEq, and_true, and_false, if_true, if_false] at admitted ⊢ <;>
      omega

/-- The exact same-domain deposit preserves the full exact current-profile
relation. -/
theorem deposit_preserves_exactCurrentProfileRelation
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : ExactCurrentProfileRelation state) :
    ExactCurrentProfileRelation (deposit state claimant domain amount) := by
  exact ⟨deposit_preserves_necessaryRelation state claimant domain amount admitted.1,
    deposit_preserves_exactCurrentProfileCustody state claimant domain amount
      admitted.2⟩

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

/-- `drain` copies the reserve column unchanged: reserves are not a drain
coordinate, so the post-state reserve column is definitionally the pre-state
column. -/
theorem drain_preserves_reserves
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat) :
    (drain state claimant domain amount).reserves = state.reserves :=
  rfl

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

/-- An exact drain preserves exact current-profile custody when both affected
custody and liability coordinates contain the drained amount. -/
theorem drain_preserves_exactCurrentProfileCustody
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : ExactCurrentProfileCustody state)
    (amountWithinCustody : amount ≤ state.custody domain)
    (amountWithinLiability : amount ≤ state.liabilities claimant domain) :
    ExactCurrentProfileCustody (drain state claimant domain amount) := by
  intro observedDomain
  specialize admitted observedDomain
  cases claimant <;> cases domain <;> cases observedDomain <;>
    simp only [liabilityInDomain, drain,
      reduceCtorEq, and_true, and_false, if_true, if_false] at admitted ⊢ <;>
      omega

/-- An exact drain preserves the full exact current-profile relation. -/
theorem drain_preserves_exactCurrentProfileRelation
    (state : State) (claimant : Claimant) (domain : Domain) (amount : Nat)
    (admitted : ExactCurrentProfileRelation state)
    (amountWithinCustody : amount ≤ state.custody domain)
    (amountWithinLiability : amount ≤ state.liabilities claimant domain)
    (amountWithinOpenTerminal : amount ≤ state.openTerminal claimant) :
    ExactCurrentProfileRelation (drain state claimant domain amount) := by
  constructor
  · exact drain_preserves_necessaryRelation state claimant domain amount admitted.1
      amountWithinCustody amountWithinLiability amountWithinOpenTerminal
  · exact drain_preserves_exactCurrentProfileCustody state claimant domain amount
      admitted.2 amountWithinCustody amountWithinLiability

/-! ## Minimized weaker-relation counterexamples -/

def AggregateLiabilitiesBacked (state : State) : Prop :=
  totalLiabilities state ≤ totalCustody state

/-- Same-domain backing implies total-only backing: adding the hot and cold
instances of R1 bounds total liabilities by total custody.  Together with
`aggregateOnly_permits_crossDomainBacking`, this makes total-only backing
strictly weaker than R1. -/
theorem sameDomainBacked_implies_aggregateBacked
    (state : State) (backed : SameDomainLiabilitiesBacked state) :
    AggregateLiabilitiesBacked state := by
  have hotBacking := backed .hot
  have coldBacking := backed .cold
  unfold AggregateLiabilitiesBacked totalLiabilities totalCustody
  omega

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

/-- Claimant-specific coverage implies claimant-erased aggregate coverage:
adding the Alice and Bob instances of R2 bounds the total OPEN amount by total
liabilities.  Together with `aggregateClaimants_permit_claimantSwap`, this
makes claimant-erased coverage strictly weaker than R2. -/
theorem openTerminalCovered_implies_aggregateCovered
    (state : State) (covered : OpenTerminalClaimsCovered state) :
    AggregateOpenClaimsCovered state := by
  have aliceCoverage := covered .alice
  have bobCoverage := covered .bob
  unfold liabilityForClaimant at aliceCoverage bobCoverage
  unfold AggregateOpenClaimsCovered totalLiabilities liabilityInDomain
  omega

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

def ReserveInclusiveBacking (state : State) : Prop :=
  ∀ domain,
    liabilityInDomain state domain ≤ state.custody domain + state.reserves domain

/-- Same-domain backing implies reserve-inclusive backing: enlarging the
right-hand side of R1 by the reserve column can only loosen the bound.
Together with `reserveInclusiveBacking_permits_missingExactCustody`, this makes
reserve-inclusive backing strictly weaker than R1. -/
theorem sameDomainBacked_implies_reserveInclusiveBacking
    (state : State) (backed : SameDomainLiabilitiesBacked state) :
    ReserveInclusiveBacking state := by
  intro domain
  have domainBacking := backed domain
  omega

def reserveInclusiveMaskingState : State where
  custody _ := 0
  liabilities
    | .alice, .hot => 1
    | _, _ => 0
  reserves
    | .hot => 1
    | .cold => 0
  openTerminal _ := 0

/-- Reserve-inclusive backing accepts a state with zero custody behind one
hot-domain liability atom.  Both same-domain backing and exact current-profile
custody reject it. -/
theorem reserveInclusiveBacking_permits_missingExactCustody :
    ReserveInclusiveBacking reserveInclusiveMaskingState ∧
      ¬ SameDomainLiabilitiesBacked reserveInclusiveMaskingState ∧
      ¬ ExactCurrentProfileCustody reserveInclusiveMaskingState := by
  refine ⟨?_, ?_, ?_⟩
  · intro domain
    cases domain <;> norm_num [ReserveInclusiveBacking, liabilityInDomain,
      reserveInclusiveMaskingState]
  · intro sameDomain
    have hotBacking := sameDomain .hot
    norm_num [liabilityInDomain, reserveInclusiveMaskingState] at hotBacking
  · intro exactCustody
    have hotCustody := exactCustody .hot
    norm_num [liabilityInDomain, reserveInclusiveMaskingState] at hotCustody

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
