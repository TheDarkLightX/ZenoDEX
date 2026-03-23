---- MODULE SettlementSignerRegistryTauBridge ----
EXTENDS Naturals

(***********************************************************************
Tau-native signer-registry bridge — bounded protocol model.

Purpose:
- model the control flow for a settlement request that must bind to both a
  registry snapshot and a chain anchor,
- make the Tau-native bridge claim explicit rather than implicit in adapter code,
- separate local data/proof decoding from temporal accept/reject behavior.
***********************************************************************)

Epochs == 0..2

VARIABLES
  requestIssued,
  execReq,
  requestEpoch,
  snapshotPresent,
  snapshotEpoch,
  anchorPresent,
  anchorEpoch,
  policyBindingChecked,
  requestBindingOk,
  anchorBindingOk,
  policyBindingOk,
  policyBindingActualOk,
  proofPathChecked,
  proofPathAvailable,
  proofPathActualAvailable,
  proofOk,
  accepted,
  rejected,
  lastAction

Vars == <<
  requestIssued,
  execReq,
  requestEpoch,
  snapshotPresent,
  snapshotEpoch,
  anchorPresent,
  anchorEpoch,
  policyBindingChecked,
  requestBindingOk,
  anchorBindingOk,
  policyBindingOk,
  policyBindingActualOk,
  proofPathChecked,
  proofPathAvailable,
  proofPathActualAvailable,
  proofOk,
  accepted,
  rejected,
  lastAction
>>

TypeOK ==
  /\ requestIssued \in BOOLEAN
  /\ execReq \in BOOLEAN
  /\ requestEpoch \in Epochs
  /\ snapshotPresent \in BOOLEAN
  /\ snapshotEpoch \in Epochs
  /\ anchorPresent \in BOOLEAN
  /\ anchorEpoch \in Epochs
  /\ policyBindingChecked \in BOOLEAN
  /\ requestBindingOk \in BOOLEAN
  /\ anchorBindingOk \in BOOLEAN
  /\ policyBindingOk \in BOOLEAN
  /\ policyBindingActualOk \in BOOLEAN
  /\ proofPathChecked \in BOOLEAN
  /\ proofPathAvailable \in BOOLEAN
  /\ proofPathActualAvailable \in BOOLEAN
  /\ proofOk \in BOOLEAN
  /\ accepted \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ lastAction \in {
      "init",
      "issue_request",
      "load_clean_snapshot",
      "load_drifted_snapshot",
      "load_clean_anchor",
      "load_drifted_anchor",
      "verify_clean_policy_binding",
      "verify_drifted_policy_binding",
      "check_proof_path_available",
      "check_proof_path_unavailable",
      "grant_proof",
      "accept",
      "reject"
     }

BridgeReady ==
  /\ requestIssued
  /\ execReq
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ snapshotEpoch = requestEpoch
  /\ anchorEpoch = requestEpoch

TauNativeRegistryBindingOK ==
  /\ BridgeReady
  /\ policyBindingChecked
  /\ policyBindingOk
  /\ proofPathChecked
  /\ proofPathAvailable
  /\ proofOk

BindingMismatchVisible ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ (
       /\ snapshotPresent
       /\ (snapshotEpoch # requestEpoch \/ ~requestBindingOk)
     \/ /\ anchorPresent
        /\ (anchorEpoch # requestEpoch \/ ~anchorBindingOk)
     \/ /\ snapshotPresent
        /\ anchorPresent
        /\ requestBindingOk
        /\ anchorBindingOk
        /\ policyBindingChecked
        /\ ~policyBindingOk
     )

ProofPathUnavailableVisible ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ policyBindingChecked
  /\ policyBindingOk
  /\ proofPathChecked
  /\ ~proofPathAvailable

ProofPathPending ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ policyBindingChecked
  /\ policyBindingOk
  /\ ~proofOk

Init ==
  /\ requestIssued = FALSE
  /\ execReq = FALSE
  /\ requestEpoch = 0
  /\ snapshotPresent = FALSE
  /\ snapshotEpoch = 0
  /\ anchorPresent = FALSE
  /\ anchorEpoch = 0
  /\ policyBindingChecked = FALSE
  /\ requestBindingOk = FALSE
  /\ anchorBindingOk = FALSE
  /\ policyBindingOk = FALSE
  /\ policyBindingActualOk = FALSE
  /\ proofPathChecked = FALSE
  /\ proofPathAvailable = FALSE
  /\ proofPathActualAvailable = FALSE
  /\ proofOk = FALSE
  /\ accepted = FALSE
  /\ rejected = FALSE
  /\ lastAction = "init"

IssueRequest ==
  /\ ~requestIssued
  /\ requestIssued' = TRUE
  /\ execReq' = TRUE
  /\ requestEpoch' \in 1..2
  /\ snapshotPresent' = FALSE
  /\ snapshotEpoch' = 0
  /\ anchorPresent' = FALSE
  /\ anchorEpoch' = 0
  /\ policyBindingChecked' = FALSE
  /\ requestBindingOk' = FALSE
  /\ anchorBindingOk' = FALSE
  /\ policyBindingOk' = FALSE
  /\ policyBindingActualOk' \in BOOLEAN
  /\ proofPathChecked' = FALSE
  /\ proofPathAvailable' = FALSE
  /\ proofPathActualAvailable' \in BOOLEAN
  /\ proofOk' = FALSE
  /\ accepted' = FALSE
  /\ rejected' = FALSE
  /\ lastAction' = "issue_request"

LoadCleanSnapshot ==
  /\ requestIssued
  /\ ~snapshotPresent
  /\ snapshotPresent' = TRUE
  /\ snapshotEpoch' = requestEpoch
  /\ requestBindingOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "load_clean_snapshot"

LoadDriftedSnapshot ==
  /\ requestIssued
  /\ ~snapshotPresent
  /\ snapshotPresent' = TRUE
  /\ snapshotEpoch' \in Epochs
  /\ snapshotEpoch' # requestEpoch
  /\ requestBindingOk' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "load_drifted_snapshot"

LoadCleanAnchor ==
  /\ requestIssued
  /\ ~anchorPresent
  /\ anchorPresent' = TRUE
  /\ anchorEpoch' = requestEpoch
  /\ anchorBindingOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      policyBindingChecked,
      requestBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "load_clean_anchor"

LoadDriftedAnchor ==
  /\ requestIssued
  /\ ~anchorPresent
  /\ anchorPresent' = TRUE
  /\ anchorEpoch' \in Epochs
  /\ anchorEpoch' # requestEpoch
  /\ policyBindingChecked' = FALSE
  /\ anchorBindingOk' = FALSE
  /\ policyBindingOk' = FALSE
  /\ proofPathChecked' = FALSE
  /\ proofPathAvailable' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      policyBindingActualOk,
      requestBindingOk,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "load_drifted_anchor"

VerifyPolicyBinding ==
  /\ requestIssued
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ ~policyBindingChecked
  /\ policyBindingChecked' = TRUE
  /\ policyBindingOk' = policyBindingActualOk
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      requestBindingOk,
      anchorBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = IF policyBindingActualOk THEN "verify_clean_policy_binding" ELSE "verify_drifted_policy_binding"

CheckProofPath ==
  /\ requestIssued
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ policyBindingChecked
  /\ policyBindingOk
  /\ ~proofPathChecked
  /\ proofPathChecked' = TRUE
  /\ proofPathAvailable' = proofPathActualAvailable
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathActualAvailable,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = IF proofPathActualAvailable THEN "check_proof_path_available" ELSE "check_proof_path_unavailable"

GrantProof ==
  /\ requestIssued
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ policyBindingChecked
  /\ policyBindingOk
  /\ proofPathChecked
  /\ proofPathAvailable
  /\ ~proofOk
  /\ proofOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      accepted,
      rejected
     >>
  /\ lastAction' = "grant_proof"

Accept ==
  /\ ~accepted
  /\ ~rejected
  /\ TauNativeRegistryBindingOK
  /\ accepted' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      rejected
     >>
  /\ lastAction' = "accept"

Reject ==
  /\ ~accepted
  /\ ~rejected
  /\ BindingMismatchVisible \/ ProofPathUnavailableVisible
  /\ rejected' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      policyBindingChecked,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      policyBindingActualOk,
      proofPathChecked,
      proofPathAvailable,
      proofPathActualAvailable,
      proofOk,
      accepted
     >>
  /\ lastAction' = "reject"

TerminalStutter ==
  /\ accepted \/ rejected
  /\ UNCHANGED Vars

Next ==
  \/ IssueRequest
  \/ LoadCleanSnapshot
  \/ LoadDriftedSnapshot
  \/ LoadCleanAnchor
  \/ LoadDriftedAnchor
  \/ VerifyPolicyBinding
  \/ CheckProofPath
  \/ GrantProof
  \/ Accept
  \/ Reject
  \/ TerminalStutter

Spec ==
  Init
  /\ [][Next]_Vars
  /\ WF_Vars(Accept)
  /\ WF_Vars(VerifyPolicyBinding)
  /\ WF_Vars(CheckProofPath)
  /\ WF_Vars(GrantProof)
  /\ WF_Vars(Reject)

AcceptedRequiresBoundSnapshot == accepted => TauNativeRegistryBindingOK

DriftedSnapshotBlocksAcceptance == accepted => snapshotEpoch = requestEpoch

DriftedAnchorBlocksAcceptance == accepted => anchorEpoch = requestEpoch

FairReadyRequestEventuallyAccepts ==
  (requestIssued /\ ~accepted /\ ~rejected /\ TauNativeRegistryBindingOK) ~> accepted

FairBridgeReadyEventuallyChecksPolicyBinding ==
  (requestIssued /\ ~accepted /\ ~rejected /\ BridgeReady /\ ~policyBindingChecked) ~> policyBindingChecked

FairPolicyBoundArtifactsEventuallyCheckProofPath ==
  (requestIssued /\ ~accepted /\ ~rejected /\ BridgeReady /\ policyBindingChecked /\ policyBindingOk /\ ~proofPathChecked) ~> proofPathChecked

FairBindingMismatchEventuallyRejects ==
  BindingMismatchVisible ~> rejected

FairProofPathEventuallyResolves ==
  ProofPathPending ~> (rejected \/ proofOk)

FairCleanArtifactsEventuallyCheckPolicyBinding ==
  /\ requestIssued
  /\ snapshotPresent
  /\ anchorPresent
  /\ requestBindingOk
  /\ anchorBindingOk
  /\ ~policyBindingChecked
  /\ ~accepted
  /\ ~rejected
  ~> policyBindingChecked

====
