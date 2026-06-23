---- MODULE TauStateAppHashStableWindow ----
EXTENDS Naturals

(***********************************************************************
Bounded control model for the stable-read window used by the Tau-state
app-hash provenance loader.

The runtime loader retries up to three times by default. Each retry is a fresh
transport observation; it is not forced to reuse the same "stable/unstable"
outcome from a previous attempt.
***********************************************************************)

Attempts == 0..3

VARIABLES
  requestIssued,
  strongBindingRequired,
  attemptsLeft,
  proofMayStabilize,
  appMayStabilize,
  tauMayStabilize,
  proofStableObserved,
  appStableObserved,
  tauStableObserved,
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
  proofStableObserved,
  appStableObserved,
  tauStableObserved,
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
  /\ proofStableObserved \in BOOLEAN
  /\ appStableObserved \in BOOLEAN
  /\ tauStableObserved \in BOOLEAN
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

StableWindowObserved ==
  /\ proofStableObserved
  /\ appStableObserved
  /\ (~strongBindingRequired \/ tauStableObserved)

Init ==
  /\ requestIssued = FALSE
  /\ strongBindingRequired = FALSE
  /\ attemptsLeft = 0
  /\ proofMayStabilize = FALSE
  /\ appMayStabilize = FALSE
  /\ tauMayStabilize = FALSE
  /\ proofStableObserved = FALSE
  /\ appStableObserved = FALSE
  /\ tauStableObserved = FALSE
  /\ stableWindowFound = FALSE
  /\ returned = FALSE
  /\ rejected = FALSE
  /\ lastAction = "init"

IssueRequest ==
  /\ ~requestIssued
  /\ requestIssued' = TRUE
  /\ strongBindingRequired' \in BOOLEAN
  /\ attemptsLeft' = 3
  /\ proofMayStabilize' \in BOOLEAN
  /\ appMayStabilize' \in BOOLEAN
  /\ tauMayStabilize' \in BOOLEAN
  /\ proofStableObserved' = FALSE
  /\ appStableObserved' = FALSE
  /\ tauStableObserved' = FALSE
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
  /\ proofStableObserved' = TRUE
  /\ appStableObserved' = TRUE
  /\ tauStableObserved' = IF strongBindingRequired THEN TRUE ELSE FALSE
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
  /\ proofStableObserved' \in BOOLEAN
  /\ appStableObserved' \in BOOLEAN
  /\ tauStableObserved' \in BOOLEAN
  /\ proofStableObserved' => proofMayStabilize
  /\ appStableObserved' => appMayStabilize
  /\ tauStableObserved' => tauMayStabilize
  /\ ~(
       proofStableObserved'
       /\ appStableObserved'
       /\ (~strongBindingRequired \/ tauStableObserved')
      )
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
  /\ rejected' = TRUE
  /\ returned' = FALSE
  /\ stableWindowFound' = FALSE
  /\ UNCHANGED <<
      requestIssued,
      strongBindingRequired,
      attemptsLeft,
      proofMayStabilize,
      appMayStabilize,
      tauMayStabilize,
      proofStableObserved,
      appStableObserved,
      tauStableObserved
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

StableWindowFoundRequiresReturned ==
  stableWindowFound => returned

StrongBindingWithoutTauStabilityBlocksReturn ==
  /\ requestIssued
  /\ strongBindingRequired
  /\ ~tauMayStabilize
  => ~returned

FairUnstabilizableWindowEventuallyRejects ==
  [](
    /\ requestIssued
    /\ ~returned
    /\ ~rejected
    /\ ~StableWindowPossible
    => <> rejected
  )

=============================================================================
