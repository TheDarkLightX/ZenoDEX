/-!
ZenoLedger block-gossip admission boundary.

The runtime `/gossip/block` route is opt-in. A pushed block is admitted only
after its envelope is hash-bound, the header/body/checkpoint agree, the block
extends the local tip by exactly one height, local replay reproduces the
gossiped header and checkpoint, and any required live checkpoint quorum is
satisfied.
-/

namespace Proofs.ZenoLedgerBlockGossipAdmission

structure BlockGossipAdmission where
  routeEnabled : Bool
  envelopeHashMatches : Bool
  headerBodyBindingValid : Bool
  checkpointBindsHeader : Bool
  extendsLocalTipByOne : Bool
  prevHashMatchesLocalTip : Bool
  localReplayMatchesHeader : Bool
  localReplayMatchesCheckpoint : Bool
  quorumSatisfiedIfRequired : Bool
deriving DecidableEq, Repr

def Safe (a : BlockGossipAdmission) : Prop :=
  a.routeEnabled = true ∧
  a.envelopeHashMatches = true ∧
  a.headerBodyBindingValid = true ∧
  a.checkpointBindsHeader = true ∧
  a.extendsLocalTipByOne = true ∧
  a.prevHashMatchesLocalTip = true ∧
  a.localReplayMatchesHeader = true ∧
  a.localReplayMatchesCheckpoint = true ∧
  a.quorumSatisfiedIfRequired = true

def Admitted (a : BlockGossipAdmission) : Prop :=
  Safe a

theorem admitted_safe
    (a : BlockGossipAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_extends_local_tip
    (a : BlockGossipAdmission)
    (hadmit : Admitted a) :
    a.extendsLocalTipByOne = true := by
  exact (admitted_safe a hadmit).2.2.2.2.1

theorem admitted_replay_matches_header
    (a : BlockGossipAdmission)
    (hadmit : Admitted a) :
    a.localReplayMatchesHeader = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.1

theorem admitted_checkpoint_binds_header
    (a : BlockGossipAdmission)
    (hadmit : Admitted a) :
    a.checkpointBindsHeader = true := by
  exact (admitted_safe a hadmit).2.2.2.1

theorem rejects_disabled_route
    (a : BlockGossipAdmission)
    (hdisabled : a.routeEnabled = false) :
    ¬ Admitted a := by
  intro hadmit
  have henabled := (admitted_safe a hadmit).1
  rw [hdisabled] at henabled
  cases henabled

theorem rejects_non_extending_block
    (a : BlockGossipAdmission)
    (hnotNext : a.extendsLocalTipByOne = false) :
    ¬ Admitted a := by
  intro hadmit
  have hnext := admitted_extends_local_tip a hadmit
  rw [hnotNext] at hnext
  cases hnext

theorem rejects_replay_header_mismatch
    (a : BlockGossipAdmission)
    (hmismatch : a.localReplayMatchesHeader = false) :
    ¬ Admitted a := by
  intro hadmit
  have hmatches := admitted_replay_matches_header a hadmit
  rw [hmismatch] at hmatches
  cases hmatches

theorem admits_safe_gossip_block
    (a : BlockGossipAdmission)
    (henabled : a.routeEnabled = true)
    (henvelope : a.envelopeHashMatches = true)
    (hbody : a.headerBodyBindingValid = true)
    (hcheckpoint : a.checkpointBindsHeader = true)
    (hnext : a.extendsLocalTipByOne = true)
    (hprev : a.prevHashMatchesLocalTip = true)
    (hreplayHeader : a.localReplayMatchesHeader = true)
    (hreplayCheckpoint : a.localReplayMatchesCheckpoint = true)
    (hquorum : a.quorumSatisfiedIfRequired = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨
    henabled,
    henvelope,
    hbody,
    hcheckpoint,
    hnext,
    hprev,
    hreplayHeader,
    hreplayCheckpoint,
    hquorum
  ⟩

end Proofs.ZenoLedgerBlockGossipAdmission
