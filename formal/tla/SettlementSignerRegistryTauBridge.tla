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
  requestBindingOk,
  anchorBindingOk,
  policyBindingOk,
  proofOk,
  accepted,
  rejected,
  lastAction

TypeOK ==
  /\ requestIssued \in BOOLEAN
  /\ execReq \in BOOLEAN
  /\ requestEpoch \in Epochs
  /\ snapshotPresent \in BOOLEAN
  /\ snapshotEpoch \in Epochs
  /\ anchorPresent \in BOOLEAN
  /\ anchorEpoch \in Epochs
  /\ requestBindingOk \in BOOLEAN
  /\ anchorBindingOk \in BOOLEAN
  /\ policyBindingOk \in BOOLEAN
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
  /\ policyBindingOk
  /\ proofOk
  /\ snapshotEpoch = requestEpoch
  /\ anchorEpoch = requestEpoch

DriftVisible ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ (
       /\ snapshotPresent
       /\ (snapshotEpoch # requestEpoch \/ ~requestBindingOk)
     \/ /\ anchorPresent
        /\ (anchorEpoch # requestEpoch \/ ~anchorBindingOk \/ ~policyBindingOk)
     )

Init ==
  /\ requestIssued = FALSE
  /\ execReq = FALSE
  /\ requestEpoch = 0
  /\ snapshotPresent = FALSE
  /\ snapshotEpoch = 0
  /\ anchorPresent = FALSE
  /\ anchorEpoch = 0
  /\ requestBindingOk = FALSE
  /\ anchorBindingOk = FALSE
  /\ policyBindingOk = FALSE
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
  /\ requestBindingOk' = FALSE
  /\ anchorBindingOk' = FALSE
  /\ policyBindingOk' = FALSE
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
      anchorBindingOk,
      policyBindingOk,
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
      anchorBindingOk,
      policyBindingOk,
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
  /\ policyBindingOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      requestBindingOk,
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
  /\ anchorBindingOk' = FALSE
  /\ policyBindingOk' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      requestBindingOk,
      proofOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "load_drifted_anchor"

GrantProof ==
  /\ requestIssued
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
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "grant_proof"

Accept ==
  /\ ~accepted
  /\ ~rejected
  /\ BridgeReady
  /\ accepted' = TRUE
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
      policyBindingOk,
      proofOk,
      rejected
     >>
  /\ lastAction' = "accept"

Reject ==
  /\ ~accepted
  /\ ~rejected
  /\ DriftVisible
  /\ rejected' = TRUE
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
      policyBindingOk,
      proofOk,
      accepted
     >>
  /\ lastAction' = "reject"

TerminalStutter ==
  /\ accepted \/ rejected
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
      policyBindingOk,
      proofOk,
      accepted,
      rejected,
      lastAction
     >>

Next ==
  \/ IssueRequest
  \/ LoadCleanSnapshot
  \/ LoadDriftedSnapshot
  \/ LoadCleanAnchor
  \/ LoadDriftedAnchor
  \/ GrantProof
  \/ Accept
  \/ Reject
  \/ TerminalStutter

Spec ==
  Init
  /\ [][Next]_<<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      proofOk,
      accepted,
      rejected,
      lastAction
     >>
  /\ WF_<<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      proofOk,
      accepted,
      rejected,
      lastAction
     >>(Accept)
  /\ WF_<<
      requestIssued,
      execReq,
      requestEpoch,
      snapshotPresent,
      snapshotEpoch,
      anchorPresent,
      anchorEpoch,
      requestBindingOk,
      anchorBindingOk,
      policyBindingOk,
      proofOk,
      accepted,
      rejected,
      lastAction
     >>(Reject)

AcceptedRequiresBoundSnapshot == accepted => BridgeReady

DriftedSnapshotBlocksAcceptance == accepted => snapshotEpoch = requestEpoch

DriftedAnchorBlocksAcceptance == accepted => anchorEpoch = requestEpoch

FairReadyRequestEventuallyAccepts ==
  (requestIssued /\ ~accepted /\ ~rejected /\ BridgeReady) ~> accepted

FairDriftedRequestEventuallyRejects ==
  DriftVisible ~> rejected

====
