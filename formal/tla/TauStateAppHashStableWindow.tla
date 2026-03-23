---- MODULE TauStateAppHashStableWindow ----
EXTENDS Naturals

(***********************************************************************
Bounded control model for the stable-read window used by the Tau-state
app-hash provenance loader.
***********************************************************************)

Attempts == 0..2

VARIABLES
  requestIssued,
  strongBindingRequired,
  attemptsLeft,
  proofMayStabilize,
  appMayStabilize,
  tauMayStabilize,
  stableWindowFound,
  returned,
  rejected,
  lastAction

Vars == <<
  requestIssued,
  strongBindingRequired,
  attemptsLeft,
  proofMayStabilize,
  appMayStabilize,
  tauMayStabilize,
  stableWindowFound,
  returned,
  rejected,
  lastAction
>>

TypeOK ==
  /\ requestIssued \in BOOLEAN
  /\ strongBindingRequired \in BOOLEAN
  /\ attemptsLeft \in Attempts
  /\ proofMayStabilize \in BOOLEAN
  /\ appMayStabilize \in BOOLEAN
  /\ tauMayStabilize \in BOOLEAN
  /\ stableWindowFound \in BOOLEAN
  /\ returned \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ lastAction \in {
      "init",
      "issue_request",
      "observe_stable_window",
      "observe_unstable_window",
      "reject_exhausted",
      "stutter"
     }

StableWindowPossible ==
  /\ proofMayStabilize
  /\ appMayStabilize
  /\ (~strongBindingRequired \/ tauMayStabilize)

Init ==
  /\ requestIssued = FALSE
  /\ strongBindingRequired = FALSE
  /\ attemptsLeft = 0
  /\ proofMayStabilize = FALSE
  /\ appMayStabilize = FALSE
  /\ tauMayStabilize = FALSE
  /\ stableWindowFound = FALSE
  /\ returned = FALSE
  /\ rejected = FALSE
  /\ lastAction = "init"

IssueRequest ==
  /\ ~requestIssued
  /\ requestIssued' = TRUE
  /\ strongBindingRequired' \in BOOLEAN
  /\ attemptsLeft' = 2
  /\ proofMayStabilize' \in BOOLEAN
  /\ appMayStabilize' \in BOOLEAN
  /\ tauMayStabilize' \in BOOLEAN
  /\ stableWindowFound' = FALSE
  /\ returned' = FALSE
  /\ rejected' = FALSE
  /\ lastAction' = "issue_request"

ObserveStableWindow ==
  /\ requestIssued
  /\ ~returned
  /\ ~rejected
  /\ attemptsLeft > 0
  /\ StableWindowPossible
  /\ stableWindowFound' = TRUE
  /\ returned' = TRUE
  /\ rejected' = FALSE
  /\ attemptsLeft' = attemptsLeft
  /\ UNCHANGED <<
      requestIssued,
      strongBindingRequired,
      proofMayStabilize,
      appMayStabilize,
      tauMayStabilize
     >>
  /\ lastAction' = "observe_stable_window"

ObserveUnstableWindow ==
  /\ requestIssued
  /\ ~returned
  /\ ~rejected
  /\ attemptsLeft > 0
  /\ ~StableWindowPossible
  /\ stableWindowFound' = FALSE
  /\ returned' = FALSE
  /\ rejected' = FALSE
  /\ attemptsLeft' = attemptsLeft - 1
  /\ UNCHANGED <<
      requestIssued,
      strongBindingRequired,
      proofMayStabilize,
      appMayStabilize,
      tauMayStabilize
     >>
  /\ lastAction' = "observe_unstable_window"

RejectExhausted ==
  /\ requestIssued
  /\ ~returned
  /\ ~rejected
  /\ attemptsLeft = 0
  /\ ~StableWindowPossible
  /\ rejected' = TRUE
  /\ returned' = FALSE
  /\ stableWindowFound' = FALSE
  /\ attemptsLeft' = attemptsLeft
  /\ UNCHANGED <<
      requestIssued,
      strongBindingRequired,
      proofMayStabilize,
      appMayStabilize,
      tauMayStabilize
     >>
  /\ lastAction' = "reject_exhausted"

TerminalStutter ==
  /\ (returned \/ rejected)
  /\ UNCHANGED Vars

Next ==
  \/ IssueRequest
  \/ ObserveStableWindow
  \/ ObserveUnstableWindow
  \/ RejectExhausted
  \/ TerminalStutter

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(ObserveStableWindow)
  /\ WF_Vars(ObserveUnstableWindow)
  /\ WF_Vars(RejectExhausted)

ReturnedRequiresStableWindow ==
  returned => stableWindowFound

StrongBindingWithoutTauStabilityBlocksReturn ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ ~tauMayStabilize
  => ~returned

FairStabilizableWindowEventuallyReturns ==
  [](
    /\ requestIssued
    /\ ~returned
    /\ ~rejected
    /\ StableWindowPossible
    => <> returned
  )

FairUnstabilizableWindowEventuallyRejects ==
  [](
    /\ requestIssued
    /\ ~returned
    /\ ~rejected
    /\ ~StableWindowPossible
    => <> rejected
  )

=============================================================================
