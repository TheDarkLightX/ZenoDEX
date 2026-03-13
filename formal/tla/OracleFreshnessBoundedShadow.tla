---- MODULE OracleFreshnessBoundedShadow ----
EXTENDS Naturals

(*
Independent shadow semantics for a bounded oracle freshness guard.

The modeled claim is small and explicit:
- a quote timestamp cannot be in the future,
- accepted freshness requires age <= configured bound,
- future or stale quotes are rejected.
*)

VARIABLES currentEpoch, quoteEpoch, maxStaleness, accepted, lastAction

TypeOK ==
  /\ currentEpoch \in Nat
  /\ quoteEpoch \in Nat
  /\ maxStaleness \in Nat
  /\ accepted \in BOOLEAN
  /\ lastAction \in {"init", "accept_fresh", "reject_future_quote", "reject_stale"}

QuoteNotFuture ==
  quoteEpoch <= currentEpoch

WithinBound ==
  QuoteNotFuture /\ ((currentEpoch - quoteEpoch) <= maxStaleness)

Init ==
  /\ currentEpoch = 0
  /\ quoteEpoch = 0
  /\ maxStaleness = 0
  /\ accepted = FALSE
  /\ lastAction = "init"

AcceptFresh ==
  /\ currentEpoch' = 10
  /\ quoteEpoch' = 8
  /\ maxStaleness' = 3
  /\ accepted' = TRUE
  /\ lastAction' = "accept_fresh"

RejectFutureQuote ==
  /\ currentEpoch' = 8
  /\ quoteEpoch' = 10
  /\ maxStaleness' = 3
  /\ accepted' = FALSE
  /\ lastAction' = "reject_future_quote"

RejectStale ==
  /\ currentEpoch' = 10
  /\ quoteEpoch' = 5
  /\ maxStaleness' = 3
  /\ accepted' = FALSE
  /\ lastAction' = "reject_stale"

Next ==
  AcceptFresh \/ RejectFutureQuote \/ RejectStale

Spec ==
  Init /\ [][Next]_<<currentEpoch, quoteEpoch, maxStaleness, accepted, lastAction>>

AcceptedRequiresQuoteNotFuture ==
  accepted => QuoteNotFuture

AcceptedRequiresBoundedAge ==
  accepted => WithinBound

FutureQuoteRejected ==
  (lastAction = "reject_future_quote") =>
    /\ quoteEpoch > currentEpoch
    /\ ~accepted

StaleQuoteRejected ==
  (lastAction = "reject_stale") =>
    /\ quoteEpoch <= currentEpoch
    /\ (currentEpoch - quoteEpoch) > maxStaleness
    /\ ~accepted

====
