---- MODULE PerpEpochScheduler ----
EXTENDS Integers, FiniteSets

(*
Perp epoch scheduler (liveness-first) — abstract model.

Purpose:
- Capture the *scheduler* obligations around an epoch-based perp:
  publish a clearing price for the current epoch, then settle it.
- Model the v1.1 "breaker" reduce-only posture at the *control* level.

This is intentionally an abstraction:
- It does not model fixed-point arithmetic.
- It does not model PnL; instead it focuses on phase progression / deadlock freedom.

If you want a more concrete model later, refine this by adding:
- bounded integer arithmetic for collateral and prices,
- liquidation transitions,
- oracle staleness + bounded-move clamp/breaker triggers.
*)

ACCOUNTS == {0, 1}   \* finite set of trader accounts
POS_SET == {-2, -1, 0, 1, 2}
EPOCH_MAX == 3

VARIABLES
  nowEpoch,
  oracleLastUpdateEpoch,
  clearingSeen,
  breakerActive,
  pos

\* Helpers
Abs(x) == IF x < 0 THEN -x ELSE x

TypeOK ==
  /\ nowEpoch \in 0..EPOCH_MAX
  /\ oracleLastUpdateEpoch \in 0..EPOCH_MAX
  /\ oracleLastUpdateEpoch <= nowEpoch
  /\ clearingSeen \in BOOLEAN
  /\ breakerActive \in BOOLEAN
  /\ pos \in [ACCOUNTS -> POS_SET]

\* Reduce-only constraint (v1.1 posture):
\* When breakerActive, positions may only decrease in absolute value.
ReduceOnlyOK(a, newPos) ==
  IF breakerActive
    THEN Abs(newPos) <= Abs(pos[a])
    ELSE TRUE

Init ==
  /\ nowEpoch = 0
  /\ oracleLastUpdateEpoch = 0
  /\ clearingSeen = FALSE
  /\ breakerActive = FALSE
  /\ pos = [a \in ACCOUNTS |-> 0]

AdvanceEpoch ==
  /\ ~clearingSeen
  /\ oracleLastUpdateEpoch = nowEpoch
  /\ nowEpoch < EPOCH_MAX
  /\ nowEpoch' = nowEpoch + 1
  /\ UNCHANGED <<oracleLastUpdateEpoch, clearingSeen, breakerActive, pos>>

PublishClearing ==
  /\ ~clearingSeen
  /\ oracleLastUpdateEpoch < nowEpoch
  /\ clearingSeen' = TRUE
  /\ UNCHANGED <<nowEpoch, oracleLastUpdateEpoch, breakerActive, pos>>

SettleEpoch ==
  /\ clearingSeen
  /\ oracleLastUpdateEpoch < nowEpoch
  /\ oracleLastUpdateEpoch' = nowEpoch
  /\ clearingSeen' = FALSE
  \* The breaker may toggle based on an out-of-bounds move in the concrete engine.
  /\ breakerActive' \in BOOLEAN
  /\ UNCHANGED <<nowEpoch, pos>>

ClearBreaker ==
  /\ breakerActive
  /\ \A a \in ACCOUNTS: pos[a] = 0
  /\ breakerActive' = FALSE
  /\ UNCHANGED <<nowEpoch, oracleLastUpdateEpoch, clearingSeen, pos>>

SetPosition ==
  \E a \in ACCOUNTS:
    \E newPos \in POS_SET:
      /\ ReduceOnlyOK(a, newPos)
      /\ pos' = [pos EXCEPT ![a] = newPos]
      /\ UNCHANGED <<nowEpoch, oracleLastUpdateEpoch, clearingSeen, breakerActive>>

Next ==
  AdvanceEpoch
  \/ PublishClearing
  \/ SettleEpoch
  \/ ClearBreaker
  \/ SetPosition

Spec ==
  Init /\ [][Next]_<<nowEpoch, oracleLastUpdateEpoch, clearingSeen, breakerActive, pos>>

PendingEpoch ==
  oracleLastUpdateEpoch < nowEpoch

PendingPublish ==
  PendingEpoch /\ ~clearingSeen

\* Liveness: under weak fairness of settling, we never get stuck with a pending clearing price.
EventuallySettles ==
  [](PendingEpoch => <> (oracleLastUpdateEpoch = nowEpoch))

EventuallyPublishes ==
  [](PendingPublish => <> clearingSeen)

PublishedEventuallySettles ==
  [](clearingSeen => <> (oracleLastUpdateEpoch = nowEpoch /\ ~clearingSeen))

\* Typical fairness assumption for the operator path:
Fair ==
  /\ WF_<<nowEpoch, oracleLastUpdateEpoch, clearingSeen, breakerActive, pos>>(PublishClearing)
  /\ WF_<<nowEpoch, oracleLastUpdateEpoch, clearingSeen, breakerActive, pos>>(SettleEpoch)

FairImpliesEventuallySettles ==
  Fair => EventuallySettles

FairImpliesEventuallyPublishes ==
  Fair => EventuallyPublishes

FairImpliesPublishedEventuallySettles ==
  Fair => PublishedEventuallySettles

==== 
