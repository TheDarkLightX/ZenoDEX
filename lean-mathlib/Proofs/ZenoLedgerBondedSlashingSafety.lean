/-!
ZenoLedger bonded-slashing safety boundary.

The runtime policy consumes a hash-bound equivocation evidence packet, an active
bond registry entry, and a bounded slashing policy. This model captures the
narrow safety fact for an accepted receipt: the evidence was admissible, the
bond was active, the evidence hash was fresh for that bond, the event height was
inside the slashability window, the slash is capped by available bond, and the
burn plus treasury split conserves the slashed amount.
-/

namespace Proofs.ZenoLedgerBondedSlashingSafety

structure BondedSlashingAdmission where
  evidenceValid : Bool
  policyActive : Bool
  subjectBondActive : Bool
  evidenceHashFresh : Bool
  insideSlashabilityWindow : Bool
  slashAmountPositive : Bool
  slashAmountLeAvailableBond : Bool
  burnAmountLeSlashAmount : Bool
  burnPlusTreasuryEqSlashAmount : Bool
  receiptHashMatches : Bool
deriving DecidableEq, Repr

def Safe (a : BondedSlashingAdmission) : Prop :=
  a.evidenceValid = true ∧
  a.policyActive = true ∧
  a.subjectBondActive = true ∧
  a.evidenceHashFresh = true ∧
  a.insideSlashabilityWindow = true ∧
  a.slashAmountPositive = true ∧
  a.slashAmountLeAvailableBond = true ∧
  a.burnAmountLeSlashAmount = true ∧
  a.burnPlusTreasuryEqSlashAmount = true ∧
  a.receiptHashMatches = true

def Admitted (a : BondedSlashingAdmission) : Prop :=
  Safe a

theorem admitted_safe
    (a : BondedSlashingAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_slash_le_available_bond
    (a : BondedSlashingAdmission)
    (hadmit : Admitted a) :
    a.slashAmountLeAvailableBond = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.1

theorem admitted_evidence_hash_fresh
    (a : BondedSlashingAdmission)
    (hadmit : Admitted a) :
    a.evidenceHashFresh = true := by
  exact (admitted_safe a hadmit).2.2.2.1

theorem admitted_inside_slashability_window
    (a : BondedSlashingAdmission)
    (hadmit : Admitted a) :
    a.insideSlashabilityWindow = true := by
  exact (admitted_safe a hadmit).2.2.2.2.1

theorem admitted_burn_treasury_conservation
    (a : BondedSlashingAdmission)
    (hadmit : Admitted a) :
    a.burnPlusTreasuryEqSlashAmount = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.2.2.1

theorem rejects_slash_over_available_bond
    (a : BondedSlashingAdmission)
    (hover : a.slashAmountLeAvailableBond = false) :
    ¬ Admitted a := by
  intro hadmit
  have hbounded := admitted_slash_le_available_bond a hadmit
  rw [hover] at hbounded
  cases hbounded

theorem rejects_replayed_evidence_hash
    (a : BondedSlashingAdmission)
    (hreplay : a.evidenceHashFresh = false) :
    ¬ Admitted a := by
  intro hadmit
  have hfresh := admitted_evidence_hash_fresh a hadmit
  rw [hreplay] at hfresh
  cases hfresh

theorem rejects_expired_slashability_window
    (a : BondedSlashingAdmission)
    (hexpired : a.insideSlashabilityWindow = false) :
    ¬ Admitted a := by
  intro hadmit
  have hwindow := admitted_inside_slashability_window a hadmit
  rw [hexpired] at hwindow
  cases hwindow

theorem admits_safe_receipt
    (a : BondedSlashingAdmission)
    (hevidence : a.evidenceValid = true)
    (hpolicy : a.policyActive = true)
    (hbond : a.subjectBondActive = true)
    (hfresh : a.evidenceHashFresh = true)
    (hwindow : a.insideSlashabilityWindow = true)
    (hpositive : a.slashAmountPositive = true)
    (hbounded : a.slashAmountLeAvailableBond = true)
    (hburnBound : a.burnAmountLeSlashAmount = true)
    (hconserve : a.burnPlusTreasuryEqSlashAmount = true)
    (hhash : a.receiptHashMatches = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨
    hevidence,
    hpolicy,
    hbond,
    hfresh,
    hwindow,
    hpositive,
    hbounded,
    hburnBound,
    hconserve,
    hhash
  ⟩

end Proofs.ZenoLedgerBondedSlashingSafety
