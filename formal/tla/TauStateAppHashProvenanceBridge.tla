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
  bridgePayloadActualOk,
  baselineChecked,
  baselineOk,
  baselineActualOk,
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
  bridgePayloadActualOk,
  baselineChecked,
  baselineOk,
  baselineActualOk,
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
  /\ bridgePayloadActualOk \in BOOLEAN
  /\ baselineChecked \in BOOLEAN
  /\ baselineOk \in BOOLEAN
  /\ baselineActualOk \in BOOLEAN
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

BaselineProvenanceOK ==
  /\ baselineChecked
  /\ baselineOk

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
       /\ ~bridgePayloadOk
     \/ /\ baselineChecked
        /\ ~baselineOk
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
  /\ bridgePayloadChecked
  /\ bridgePayloadOk
  /\ baselineChecked
  /\ baselineOk
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
  /\ bridgePayloadActualOk = FALSE
  /\ baselineChecked = FALSE
  /\ baselineOk = FALSE
  /\ baselineActualOk = FALSE
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
  /\ bridgePayloadActualOk' \in BOOLEAN
  /\ baselineChecked' = FALSE
  /\ baselineOk' = FALSE
  /\ baselineActualOk' \in BOOLEAN
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
  /\ bridgePayloadChecked' = TRUE
  /\ bridgePayloadOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
  /\ ~bridgePayloadActualOk
  /\ bridgePayloadChecked' = TRUE
  /\ bridgePayloadOk' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
  /\ bridgePayloadOk
  /\ ~baselineChecked
  /\ baselineActualOk
  /\ baselineChecked' = TRUE
  /\ baselineOk' = TRUE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadActualOk,
      baselineActualOk,
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
  /\ bridgePayloadChecked
  /\ bridgePayloadOk
  /\ ~baselineChecked
  /\ ~baselineActualOk
  /\ baselineChecked' = TRUE
  /\ baselineOk' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      execReq,
      strongBindingRequired,
      bridgePayloadChecked,
      bridgePayloadOk,
      bridgePayloadActualOk,
      baselineActualOk,
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
  /\ bridgePayloadChecked
  /\ bridgePayloadOk
  /\ baselineChecked
  /\ baselineOk
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
  /\ bridgePayloadChecked
  /\ bridgePayloadOk
  /\ baselineChecked
  /\ baselineOk
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
      bridgePayloadActualOk,
      baselineChecked,
      baselineOk,
      baselineActualOk,
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
