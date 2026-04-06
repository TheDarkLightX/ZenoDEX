---- MODULE TauStateAppHashProvenanceBridge ----
EXTENDS Naturals

(***********************************************************************
Tau-state/app-hash provenance bridge — bounded control model.

Purpose:
- make the loader acceptance relation explicit at the control level,
- separate baseline app-state provenance from the optional stronger Tau-state
  app-hash binding,
- force explicit reject behavior when strong binding is required but the
  Tau-state transport is unavailable or drifted.
***********************************************************************)

VARIABLES
  requestIssued,
  execReq,
  strongBindingRequired,
  bridgePayloadChecked,
  bridgePayloadOk,
  bridgePayloadObjectOk,
  bridgeSchemaOk,
  bridgeSnapshotPresent,
  bridgePayloadActualOk,
  bridgePayloadObjectActualOk,
  bridgeSchemaActualOk,
  bridgeSnapshotActualPresent,
  baselineChecked,
  baselineOk,
  stateProofErrorFree,
  baselineActualOk,
  stateProofActualErrorFree,
  tauTransportChecked,
  tauTransportAvailable,
  tauTransportActualAvailable,
  tauBindingChecked,
  tauBindingOk,
  tauBindingActualOk,
  accepted,
  rejected,
  lastAction

Vars == <<
  requestIssued,
  execReq,
  strongBindingRequired,
  bridgePayloadChecked,
  bridgePayloadOk,
  bridgePayloadObjectOk,
  bridgeSchemaOk,
  bridgeSnapshotPresent,
  bridgePayloadActualOk,
  bridgePayloadObjectActualOk,
  bridgeSchemaActualOk,
  bridgeSnapshotActualPresent,
  baselineChecked,
  baselineOk,
  stateProofErrorFree,
  baselineActualOk,
  stateProofActualErrorFree,
  tauTransportChecked,
  tauTransportAvailable,
  tauTransportActualAvailable,
  tauBindingChecked,
  tauBindingOk,
  tauBindingActualOk,
  accepted,
  rejected,
  lastAction
>>

TypeOK ==
  /\ requestIssued \in BOOLEAN
  /\ execReq \in BOOLEAN
  /\ strongBindingRequired \in BOOLEAN
  /\ bridgePayloadChecked \in BOOLEAN
  /\ bridgePayloadOk \in BOOLEAN
  /\ bridgePayloadObjectOk \in BOOLEAN
  /\ bridgeSchemaOk \in BOOLEAN
  /\ bridgeSnapshotPresent \in BOOLEAN
  /\ bridgePayloadActualOk \in BOOLEAN
  /\ bridgePayloadObjectActualOk \in BOOLEAN
  /\ bridgeSchemaActualOk \in BOOLEAN
  /\ bridgeSnapshotActualPresent \in BOOLEAN
  /\ baselineChecked \in BOOLEAN
  /\ baselineOk \in BOOLEAN
  /\ stateProofErrorFree \in BOOLEAN
  /\ baselineActualOk \in BOOLEAN
  /\ stateProofActualErrorFree \in BOOLEAN
  /\ tauTransportChecked \in BOOLEAN
  /\ tauTransportAvailable \in BOOLEAN
  /\ tauTransportActualAvailable \in BOOLEAN
  /\ tauBindingChecked \in BOOLEAN
  /\ tauBindingOk \in BOOLEAN
  /\ tauBindingActualOk \in BOOLEAN
  /\ accepted \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ lastAction \in {
      "init",
      "issue_request",
      "check_clean_bridge_payload",
      "check_drifted_bridge_payload",
      "check_clean_baseline",
      "check_drifted_baseline",
      "check_tau_transport_available",
      "check_tau_transport_unavailable",
      "check_clean_tau_binding",
      "check_drifted_tau_binding",
      "accept",
      "reject"
     }

BridgePayloadReady ==
  /\ bridgePayloadChecked
  /\ bridgePayloadOk
  /\ bridgePayloadObjectOk
  /\ bridgeSchemaOk
  /\ bridgeSnapshotPresent

BaselineProvenanceOK ==
  /\ baselineChecked
  /\ baselineOk
  /\ stateProofErrorFree

StrongTauStateBindingOK ==
  /\ tauTransportChecked
  /\ tauTransportAvailable
  /\ tauBindingChecked
  /\ tauBindingOk

LoaderOK ==
  /\ requestIssued
  /\ execReq
  /\ BridgePayloadReady
  /\ BaselineProvenanceOK
  /\ (~strongBindingRequired \/ StrongTauStateBindingOK)

VisibleRejectReason ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ (
       /\ bridgePayloadChecked
       /\ ~(bridgePayloadOk /\ bridgePayloadObjectOk /\ bridgeSchemaOk /\ bridgeSnapshotPresent)
     \/ /\ baselineChecked
        /\ ~(baselineOk /\ stateProofErrorFree)
     \/ /\ strongBindingRequired
        /\ tauTransportChecked
        /\ ~tauTransportAvailable
     \/ /\ strongBindingRequired
        /\ tauTransportChecked
        /\ tauTransportAvailable
        /\ tauBindingChecked
        /\ ~tauBindingOk
     )

CleanReadyPending ==
  /\ requestIssued
  /\ ~accepted
  /\ ~rejected
  /\ BridgePayloadReady
  /\ BaselineProvenanceOK
  /\ (
       /\ ~strongBindingRequired
     \/ /\ tauTransportChecked
        /\ tauTransportAvailable
        /\ tauBindingChecked
        /\ tauBindingOk
     )

Init ==
  /\ requestIssued = FALSE
  /\ execReq = FALSE
  /\ strongBindingRequired = FALSE
  /\ bridgePayloadChecked = FALSE
  /\ bridgePayloadOk = FALSE
  /\ bridgePayloadObjectOk = FALSE
  /\ bridgeSchemaOk = FALSE
  /\ bridgeSnapshotPresent = FALSE
  /\ bridgePayloadActualOk = FALSE
  /\ bridgePayloadObjectActualOk = FALSE
  /\ bridgeSchemaActualOk = FALSE
  /\ bridgeSnapshotActualPresent = FALSE
  /\ baselineChecked = FALSE
  /\ baselineOk = FALSE
  /\ stateProofErrorFree = FALSE
  /\ baselineActualOk = FALSE
  /\ stateProofActualErrorFree = FALSE
  /\ tauTransportChecked = FALSE
  /\ tauTransportAvailable = FALSE
  /\ tauTransportActualAvailable = FALSE
  /\ tauBindingChecked = FALSE
  /\ tauBindingOk = FALSE
  /\ tauBindingActualOk = FALSE
  /\ accepted = FALSE
  /\ rejected = FALSE
  /\ lastAction = "init"

IssueRequest ==
  /\ ~requestIssued
  /\ requestIssued' = TRUE
  /\ execReq' = TRUE
  /\ strongBindingRequired' \in BOOLEAN
  /\ bridgePayloadChecked' = FALSE
  /\ bridgePayloadOk' = FALSE
  /\ bridgePayloadObjectOk' = FALSE
  /\ bridgeSchemaOk' = FALSE
  /\ bridgeSnapshotPresent' = FALSE
  /\ bridgePayloadActualOk' \in BOOLEAN
  /\ bridgePayloadObjectActualOk' \in BOOLEAN
  /\ bridgeSchemaActualOk' \in BOOLEAN
  /\ bridgeSnapshotActualPresent' \in BOOLEAN
  /\ baselineChecked' = FALSE
  /\ baselineOk' = FALSE
  /\ stateProofErrorFree' = FALSE
  /\ baselineActualOk' \in BOOLEAN
  /\ stateProofActualErrorFree' \in BOOLEAN
  /\ tauTransportChecked' = FALSE
  /\ tauTransportAvailable' = FALSE
  /\ tauTransportActualAvailable' \in BOOLEAN
  /\ tauBindingChecked' = FALSE
  /\ tauBindingOk' = FALSE
  /\ tauBindingActualOk' \in BOOLEAN
  /\ accepted' = FALSE
  /\ rejected' = FALSE
  /\ lastAction' = "issue_request"

CheckCleanBridgePayload ==
  /\ requestIssued
  /\ ~bridgePayloadChecked
  /\ bridgePayloadActualOk
  /\ bridgePayloadObjectActualOk
  /\ bridgeSchemaActualOk
  /\ bridgeSnapshotActualPresent
  /\ bridgePayloadChecked' = TRUE
  /\ bridgePayloadOk' = TRUE
  /\ bridgePayloadObjectOk' = TRUE
  /\ bridgeSchemaOk' = TRUE
  /\ bridgeSnapshotPresent' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_clean_bridge_payload"

CheckDriftedBridgePayload ==
  /\ requestIssued
  /\ ~bridgePayloadChecked
  /\ ~(
       bridgePayloadActualOk
       /\ bridgePayloadObjectActualOk
       /\ bridgeSchemaActualOk
       /\ bridgeSnapshotActualPresent
      )
  /\ bridgePayloadChecked' = TRUE
  /\ bridgePayloadOk' = bridgePayloadActualOk
  /\ bridgePayloadObjectOk' = bridgePayloadObjectActualOk
  /\ bridgeSchemaOk' = bridgeSchemaActualOk
  /\ bridgeSnapshotPresent' = bridgeSnapshotActualPresent
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_drifted_bridge_payload"

CheckCleanBaseline ==
  /\ requestIssued
  /\ bridgePayloadChecked
  /\ BridgePayloadReady
  /\ ~baselineChecked
  /\ baselineActualOk
  /\ stateProofActualErrorFree
  /\ baselineChecked' = TRUE
  /\ baselineOk' = TRUE
  /\ stateProofErrorFree' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_clean_baseline"

CheckDriftedBaseline ==
  /\ requestIssued
  /\ BridgePayloadReady
  /\ ~baselineChecked
  /\ ~(baselineActualOk /\ stateProofActualErrorFree)
  /\ baselineChecked' = TRUE
  /\ baselineOk' = baselineActualOk
  /\ stateProofErrorFree' = stateProofActualErrorFree
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_drifted_baseline"

CheckTauTransportAvailable ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ BridgePayloadReady
  /\ BaselineProvenanceOK
  /\ ~tauTransportChecked
  /\ tauTransportActualAvailable
  /\ tauTransportChecked' = TRUE
  /\ tauTransportAvailable' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_tau_transport_available"

CheckTauTransportUnavailable ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ BridgePayloadReady
  /\ BaselineProvenanceOK
  /\ ~tauTransportChecked
  /\ ~tauTransportActualAvailable
  /\ tauTransportChecked' = TRUE
  /\ tauTransportAvailable' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_tau_transport_unavailable"

CheckCleanTauBinding ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ tauTransportChecked
  /\ tauTransportAvailable
  /\ ~tauBindingChecked
  /\ tauBindingActualOk
  /\ tauBindingChecked' = TRUE
  /\ tauBindingOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_clean_tau_binding"

CheckDriftedTauBinding ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ tauTransportChecked
  /\ tauTransportAvailable
  /\ ~tauBindingChecked
  /\ ~tauBindingActualOk
  /\ tauBindingChecked' = TRUE
  /\ tauBindingOk' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingActualOk,
      accepted,
      rejected
     >>
  /\ lastAction' = "check_drifted_tau_binding"

Accept ==
  /\ LoaderOK
  /\ ~accepted
  /\ ~rejected
  /\ accepted' = TRUE
  /\ rejected' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk
     >>
  /\ lastAction' = "accept"

Reject ==
  /\ VisibleRejectReason
  /\ rejected' = TRUE
  /\ accepted' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadObjectOk,
      bridgeSchemaOk,
      bridgeSnapshotPresent,
      bridgePayloadActualOk,
      bridgePayloadObjectActualOk,
      bridgeSchemaActualOk,
      bridgeSnapshotActualPresent,
      baselineChecked,
      baselineOk,
      stateProofErrorFree,
      baselineActualOk,
      stateProofActualErrorFree,
      tauTransportChecked,
      tauTransportAvailable,
      tauTransportActualAvailable,
      tauBindingChecked,
      tauBindingOk,
      tauBindingActualOk
     >>
  /\ lastAction' = "reject"

TerminalStutter ==
  /\ (accepted \/ rejected)
  /\ UNCHANGED Vars

Next ==
  \/ IssueRequest
  \/ CheckCleanBridgePayload
  \/ CheckDriftedBridgePayload
  \/ CheckCleanBaseline
  \/ CheckDriftedBaseline
  \/ CheckTauTransportAvailable
  \/ CheckTauTransportUnavailable
  \/ CheckCleanTauBinding
  \/ CheckDriftedTauBinding
  \/ Accept
  \/ Reject
  \/ TerminalStutter

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(CheckCleanBridgePayload)
  /\ WF_Vars(CheckDriftedBridgePayload)
  /\ WF_Vars(CheckCleanBaseline)
  /\ WF_Vars(CheckDriftedBaseline)
  /\ WF_Vars(CheckTauTransportAvailable)
  /\ WF_Vars(CheckTauTransportUnavailable)
  /\ WF_Vars(CheckCleanTauBinding)
  /\ WF_Vars(CheckDriftedTauBinding)
  /\ WF_Vars(Accept)
  /\ WF_Vars(Reject)

AcceptedStateRequiresLoaderOK ==
  accepted => LoaderOK

StrongBindingMismatchStateBlocksAcceptance ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ tauTransportChecked
  /\ tauTransportAvailable
  /\ tauBindingChecked
  /\ ~tauBindingOk
  => ~accepted

MissingTauTransportStateBlocksAcceptance ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ tauTransportChecked
  /\ ~tauTransportAvailable
  => ~accepted

AcceptedRequiresLoaderOK ==
  [](accepted => LoaderOK)

StrongBindingMismatchBlocksAcceptance ==
  [](
    /\ requestIssued
    /\ strongBindingRequired
    /\ tauTransportChecked
    /\ tauTransportAvailable
    /\ tauBindingChecked
    /\ ~tauBindingOk
    => ~accepted
  )

MissingTauTransportBlocksAcceptance ==
  [](
    /\ requestIssued
    /\ strongBindingRequired
    /\ tauTransportChecked
    /\ ~tauTransportAvailable
    => ~accepted
  )

FairCleanReadyStateEventuallyAccepts ==
  [](CleanReadyPending => <> accepted)

FairVisibleStrongBindingFailureEventuallyRejects ==
  [](
    /\ requestIssued
    /\ strongBindingRequired
    /\ tauTransportChecked
    /\ tauTransportAvailable
    /\ tauBindingChecked
    /\ ~tauBindingOk
    => <> rejected
  )

FairMissingTauTransportEventuallyRejects ==
  [](
    /\ requestIssued
    /\ strongBindingRequired
    /\ tauTransportChecked
    /\ ~tauTransportAvailable
    => <> rejected
  )

=============================================================================
