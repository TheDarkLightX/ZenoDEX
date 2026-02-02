---- MODULE PerpEpochScheduler ----
EXTENDS Naturals, FiniteSets

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

CONSTANTS
  ACCOUNTS,     \* finite set of trader accounts
  POS_SET,      \* finite set of allowed positions (ints)
  EPOCH_MAX     \* small bound for TLC exploration

VARIABLES
  nowEpoch,
  clearingSeen,
  breakerActive,
  pos

\* Helpers
Abs(x) == IF x < 0 THEN -x ELSE x

TypeOK ==
  /\ nowEpoch \in 0..EPOCH_MAX
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
  /\ clearingSeen = FALSE
  /\ breakerActive = FALSE
  /\ pos = [a \in ACCOUNTS |-> 0]

AdvanceEpoch ==
  /\ ~clearingSeen
  /\ nowEpoch < EPOCH_MAX
  /\ nowEpoch' = nowEpoch + 1
  /\ UNCHANGED <<clearingSeen, breakerActive, pos>>

PublishClearing ==
  /\ ~clearingSeen
  /\ nowEpoch > 0
  /\ clearingSeen' = TRUE
  /\ UNCHANGED <<nowEpoch, breakerActive, pos>>

SettleEpoch ==
  /\ clearingSeen
  /\ clearingSeen' = FALSE
  \* The breaker may toggle based on an out-of-bounds move in the concrete engine.
  /\ breakerActive' \in BOOLEAN
  /\ UNCHANGED <<nowEpoch, pos>>

ClearBreaker ==
  /\ breakerActive
  /\ \A a \in ACCOUNTS: pos[a] = 0
  /\ breakerActive' = FALSE
  /\ UNCHANGED <<nowEpoch, clearingSeen, pos>>

SetPosition ==
  \E a \in ACCOUNTS:
    \E newPos \in POS_SET:
      /\ ReduceOnlyOK(a, newPos)
      /\ pos' = [pos EXCEPT ![a] = newPos]
      /\ UNCHANGED <<nowEpoch, clearingSeen, breakerActive>>

Next ==
  AdvanceEpoch
  \/ PublishClearing
  \/ SettleEpoch
  \/ ClearBreaker
  \/ SetPosition

Spec ==
  Init /\ [][Next]_<<nowEpoch, clearingSeen, breakerActive, pos>>

\* Liveness: under weak fairness of settling, we never get stuck with a pending clearing price.
EventuallySettles ==
  [](clearingSeen => <> ~clearingSeen)

\* Typical fairness assumption for the operator path:
Fair ==
  WF_<<nowEpoch, clearingSeen, breakerActive, pos>>(SettleEpoch)

==== 

