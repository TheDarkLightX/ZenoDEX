---- MODULE AutoTraderNonceGuardShadow ----
EXTENDS Naturals

(*
Independent shadow semantics for the AutoTrader nonce guard.

This model intentionally does not reuse Tau syntax. It captures the intended
transition semantics for strict sequential nonces:
- only nonce = lastUsedNonce + 1 may be accepted,
- rejected nonce attempts must not advance state,
- lastUsedNonce never decreases.
*)

CONSTANTS NONCES

VARIABLES lastUsedNonce, prevLastUsedNonce, requestedNonce, accepted, lastAction

TypeOK ==
  /\ lastUsedNonce \in NONCES
  /\ prevLastUsedNonce \in NONCES
  /\ requestedNonce \in NONCES
  /\ accepted \in BOOLEAN
  /\ lastAction \in {"init", "accept", "reject_stale", "reject_gap"}

Init ==
  /\ lastUsedNonce = 0
  /\ prevLastUsedNonce = 0
  /\ requestedNonce = 0
  /\ accepted = FALSE
  /\ lastAction = "init"

Accept ==
  \E n \in NONCES:
    /\ n = lastUsedNonce + 1
    /\ requestedNonce' = n
    /\ prevLastUsedNonce' = lastUsedNonce
    /\ lastUsedNonce' = n
    /\ accepted' = TRUE
    /\ lastAction' = "accept"

RejectStale ==
  \E n \in NONCES:
    /\ n <= lastUsedNonce
    /\ requestedNonce' = n
    /\ prevLastUsedNonce' = lastUsedNonce
    /\ lastUsedNonce' = lastUsedNonce
    /\ accepted' = FALSE
    /\ lastAction' = "reject_stale"

RejectGap ==
  \E n \in NONCES:
    /\ n > lastUsedNonce + 1
    /\ requestedNonce' = n
    /\ prevLastUsedNonce' = lastUsedNonce
    /\ lastUsedNonce' = lastUsedNonce
    /\ accepted' = FALSE
    /\ lastAction' = "reject_gap"

Next ==
  Accept \/ RejectStale \/ RejectGap

Spec ==
  Init /\ [][Next]_<<lastUsedNonce, prevLastUsedNonce, requestedNonce, accepted, lastAction>>

AcceptedOnlySequential ==
  accepted => /\ lastAction = "accept"
              /\ requestedNonce = prevLastUsedNonce + 1
              /\ lastUsedNonce = requestedNonce

RejectedDoesNotAdvance ==
  ~accepted => lastUsedNonce = prevLastUsedNonce

NonceNeverDecreases ==
  lastUsedNonce >= prevLastUsedNonce

====
