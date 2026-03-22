---- MODULE SettlementAttestationGovernance ----
EXTENDS Naturals, FiniteSets

(*
Settlement attestation governance — bounded protocol model.

Purpose:
- model the protocol-level control flow for governed signer/source policy updates,
- separate local safety from temporal governance behavior,
- make the decentralization claim explicit: settlement admission binds to an active,
  approved, timelocked, multisig-backed policy snapshot.

Scope:
- abstracts away BLS signatures and packet hashing,
- abstracts away on-chain execution details into control events,
- uses bounded signer/source sets and policy epochs.

What it does model:
- proposal approval,
- timelock progression,
- activation of a pending policy,
- settlement acceptance only under the active policy epoch,
- revocation blocking future acceptance,
- liveness under weak fairness of policy activation.

What it does not model:
- real-world signer independence,
- disagreement/median logic across multiple attestation bundles,
- economics of bribery or capture beyond the control surface.
*)

CONSTANTS SIGNERS, SOURCES

PolicyEpochs == 0..3
Thresholds == 1..2
TimelockCountdowns == 0..2

VARIABLES
  activePolicyEpoch,
  activeApproved,
  activeTimelockElapsed,
  activeMultisigApproved,
  activeRevoked,
  activeAllowedSigners,
  activeAllowedSources,
  activeMinSigners,
  activeMinSources,
  pendingPolicyEpoch,
  pendingApproved,
  pendingMultisigApproved,
  pendingCountdown,
  pendingAllowedSigners,
  pendingAllowedSources,
  pendingMinSigners,
  pendingMinSources,
  observedPolicyEpoch,
  observedSigners,
  observedSources,
  settlementAccepted,
  lastAction

TypeOK ==
  /\ activePolicyEpoch \in PolicyEpochs
  /\ activeApproved \in BOOLEAN
  /\ activeTimelockElapsed \in BOOLEAN
  /\ activeMultisigApproved \in BOOLEAN
  /\ activeRevoked \in BOOLEAN
  /\ activeAllowedSigners \subseteq SIGNERS
  /\ activeAllowedSources \subseteq SOURCES
  /\ activeMinSigners \in Thresholds
  /\ activeMinSources \in Thresholds
  /\ pendingPolicyEpoch \in PolicyEpochs
  /\ pendingApproved \in BOOLEAN
  /\ pendingMultisigApproved \in BOOLEAN
  /\ pendingCountdown \in TimelockCountdowns
  /\ pendingAllowedSigners \subseteq SIGNERS
  /\ pendingAllowedSources \subseteq SOURCES
  /\ pendingMinSigners \in Thresholds
  /\ pendingMinSources \in Thresholds
  /\ observedPolicyEpoch \in PolicyEpochs
  /\ observedSigners \subseteq SIGNERS
  /\ observedSources \subseteq SOURCES
  /\ settlementAccepted \in BOOLEAN
  /\ lastAction \in {
      "init",
      "propose_policy",
      "tick_timelock",
      "activate_policy",
      "revoke_active_policy",
      "accept_settlement",
      "reject_settlement"
     }

PolicyCanActivate ==
  /\ pendingApproved
  /\ pendingMultisigApproved
  /\ pendingCountdown = 0
  /\ Cardinality(pendingAllowedSigners) >= pendingMinSigners
  /\ Cardinality(pendingAllowedSources) >= pendingMinSources

ActivePolicyOK ==
  /\ activeApproved
  /\ activeTimelockElapsed
  /\ activeMultisigApproved
  /\ ~activeRevoked
  /\ Cardinality(activeAllowedSigners) >= activeMinSigners
  /\ Cardinality(activeAllowedSources) >= activeMinSources

ObservedBundleOK ==
  /\ observedPolicyEpoch = activePolicyEpoch
  /\ observedSigners \subseteq activeAllowedSigners
  /\ observedSources \subseteq activeAllowedSources
  /\ Cardinality(observedSigners) >= activeMinSigners
  /\ Cardinality(observedSources) >= activeMinSources

Init ==
  /\ activePolicyEpoch = 0
  /\ activeApproved = TRUE
  /\ activeTimelockElapsed = TRUE
  /\ activeMultisigApproved = TRUE
  /\ activeRevoked = FALSE
  /\ activeAllowedSigners = {0}
  /\ activeAllowedSources = {0}
  /\ activeMinSigners = 1
  /\ activeMinSources = 1
  /\ pendingPolicyEpoch = 0
  /\ pendingApproved = FALSE
  /\ pendingMultisigApproved = FALSE
  /\ pendingCountdown = 0
  /\ pendingAllowedSigners = {}
  /\ pendingAllowedSources = {}
  /\ pendingMinSigners = 1
  /\ pendingMinSources = 1
  /\ observedPolicyEpoch = 0
  /\ observedSigners = {}
  /\ observedSources = {}
  /\ settlementAccepted = FALSE
  /\ lastAction = "init"

ProposePolicy ==
  /\ pendingPolicyEpoch < 3
  /\ pendingPolicyEpoch' = pendingPolicyEpoch + 1
  /\ pendingApproved' = TRUE
  /\ pendingMultisigApproved' = TRUE
  /\ pendingCountdown' = 2
  /\ pendingAllowedSigners' \in { s \in SUBSET SIGNERS : Cardinality(s) >= 1 }
  /\ pendingAllowedSources' \in { s \in SUBSET SOURCES : Cardinality(s) >= 1 }
  /\ pendingMinSigners' \in Thresholds
  /\ pendingMinSources' \in Thresholds
  /\ Cardinality(pendingAllowedSigners') >= pendingMinSigners'
  /\ Cardinality(pendingAllowedSources') >= pendingMinSources'
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources
     >>
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "propose_policy"

TickTimelock ==
  /\ pendingApproved
  /\ pendingCountdown > 0
  /\ pendingCountdown' = pendingCountdown - 1
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources
     >>
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "tick_timelock"

ActivatePolicy ==
  /\ PolicyCanActivate
  /\ activePolicyEpoch' = pendingPolicyEpoch
  /\ activeApproved' = pendingApproved
  /\ activeTimelockElapsed' = TRUE
  /\ activeMultisigApproved' = pendingMultisigApproved
  /\ activeRevoked' = FALSE
  /\ activeAllowedSigners' = pendingAllowedSigners
  /\ activeAllowedSources' = pendingAllowedSources
  /\ activeMinSigners' = pendingMinSigners
  /\ activeMinSources' = pendingMinSources
  /\ UNCHANGED <<
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources
     >>
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "activate_policy"

RevokeActivePolicy ==
  /\ ~activeRevoked
  /\ activeRevoked' = TRUE
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources
     >>
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "revoke_active_policy"

AcceptSettlement ==
  /\ ActivePolicyOK
  /\ observedPolicyEpoch' = activePolicyEpoch
  /\ observedSigners' = activeAllowedSigners
  /\ observedSources' = activeAllowedSources
  /\ settlementAccepted' = TRUE
  /\ lastAction' = "accept_settlement"
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources
     >>

RejectWrongEpoch ==
  /\ observedPolicyEpoch' =
      IF activePolicyEpoch = 3 THEN 0 ELSE activePolicyEpoch + 1
  /\ observedSigners' = activeAllowedSigners
  /\ observedSources' = activeAllowedSources
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "reject_settlement"
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources
     >>

RejectInsufficientSigners ==
  /\ observedPolicyEpoch' = activePolicyEpoch
  /\ observedSigners' = {}
  /\ observedSources' = activeAllowedSources
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "reject_settlement"
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources
     >>

RejectInsufficientSources ==
  /\ observedPolicyEpoch' = activePolicyEpoch
  /\ observedSigners' = activeAllowedSigners
  /\ observedSources' = {}
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "reject_settlement"
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources
     >>

RejectRevokedPolicy ==
  /\ activeRevoked
  /\ observedPolicyEpoch' = activePolicyEpoch
  /\ observedSigners' = activeAllowedSigners
  /\ observedSources' = activeAllowedSources
  /\ settlementAccepted' = FALSE
  /\ lastAction' = "reject_settlement"
  /\ UNCHANGED <<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources
     >>

RejectSettlement ==
  RejectWrongEpoch
  \/ RejectInsufficientSigners
  \/ RejectInsufficientSources
  \/ RejectRevokedPolicy

Next ==
  ProposePolicy
  \/ TickTimelock
  \/ ActivatePolicy
  \/ RevokeActivePolicy
  \/ AcceptSettlement
  \/ RejectSettlement

Spec ==
  Init /\ [][Next]_<<
    activePolicyEpoch,
    activeApproved,
    activeTimelockElapsed,
    activeMultisigApproved,
    activeRevoked,
    activeAllowedSigners,
    activeAllowedSources,
    activeMinSigners,
    activeMinSources,
    pendingPolicyEpoch,
    pendingApproved,
    pendingMultisigApproved,
    pendingCountdown,
    pendingAllowedSigners,
    pendingAllowedSources,
    pendingMinSigners,
    pendingMinSources,
    observedPolicyEpoch,
    observedSigners,
    observedSources,
    settlementAccepted,
    lastAction
  >>

Fair ==
  /\ WF_<<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources,
      settlementAccepted,
      lastAction
     >>(TickTimelock)
  /\ WF_<<
      activePolicyEpoch,
      activeApproved,
      activeTimelockElapsed,
      activeMultisigApproved,
      activeRevoked,
      activeAllowedSigners,
      activeAllowedSources,
      activeMinSigners,
      activeMinSources,
      pendingPolicyEpoch,
      pendingApproved,
      pendingMultisigApproved,
      pendingCountdown,
      pendingAllowedSigners,
      pendingAllowedSources,
      pendingMinSigners,
      pendingMinSources,
      observedPolicyEpoch,
      observedSigners,
      observedSources,
      settlementAccepted,
      lastAction
     >>(ActivatePolicy)

AcceptedSettlementRequiresActiveGovernedPolicy ==
  settlementAccepted => /\ ActivePolicyOK /\ ObservedBundleOK

RevokedPolicyRejectsFutureSettlement ==
  activeRevoked => ~settlementAccepted

NoRetroactiveEpochDriftOnAcceptedSettlement ==
  settlementAccepted => observedPolicyEpoch = activePolicyEpoch

FairImpliesApprovedPolicyEventuallyActivates ==
  Fair =>
    []((pendingApproved /\ pendingMultisigApproved) => <> (activePolicyEpoch = pendingPolicyEpoch))

====
