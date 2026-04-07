---- MODULE OracleRecoveryLifecycle ----
EXTENDS Integers

(*
Bounded TLA+ model for the oracle-recovery lifecycle.

Purpose:
- Capture the temporal control obligations behind the zUSD oracle recovery lane.
- Model stale/diverged oracle state, explicit sync repair, and fail-closed blocking.
- Check that weakly fair recovery actions eventually re-enable risky ops once the
  oracle world is healthy again, or else permanently block.

This is intentionally abstract:
- no real prices or basis points,
- no TCR/recovery policy arithmetic,
- only the control-level recovery progression.
*)

EPOCH_MAX == 4
MAX_STALE == 1

VARIABLES
  nowEpoch,
  oracleEpoch,
  syncAligned,
  permanentlyBlocked,
  riskyActionRequested,
  riskyOpsAllowed

OracleFresh ==
  nowEpoch - oracleEpoch <= MAX_STALE

HealthyNow ==
  OracleFresh /\ syncAligned /\ ~permanentlyBlocked

Quiescent ==
  permanentlyBlocked \/ (HealthyNow /\ (~riskyActionRequested \/ riskyOpsAllowed))

TypeOK ==
  /\ nowEpoch \in 0..EPOCH_MAX
  /\ oracleEpoch \in 0..EPOCH_MAX
  /\ oracleEpoch <= nowEpoch
  /\ syncAligned \in BOOLEAN
  /\ permanentlyBlocked \in BOOLEAN
  /\ riskyActionRequested \in BOOLEAN
  /\ riskyOpsAllowed \in BOOLEAN

BlockedAbsorbing ==
  permanentlyBlocked => ~riskyOpsAllowed

StaleBlocksRisky ==
  (~OracleFresh /\ ~permanentlyBlocked) => ~riskyOpsAllowed

Init ==
  /\ nowEpoch = 0
  /\ oracleEpoch = 0
  /\ syncAligned = TRUE
  /\ permanentlyBlocked = FALSE
  /\ riskyActionRequested = FALSE
  /\ riskyOpsAllowed = FALSE

AdvanceTime ==
  /\ nowEpoch < EPOCH_MAX
  /\ ~permanentlyBlocked
  /\ nowEpoch' = nowEpoch + 1
  /\ oracleEpoch' = oracleEpoch
  /\ syncAligned' = syncAligned
  /\ permanentlyBlocked' = permanentlyBlocked
  /\ riskyActionRequested' = riskyActionRequested
  /\ riskyOpsAllowed' =
       IF ((nowEpoch + 1) - oracleEpoch <= MAX_STALE) /\ syncAligned
         THEN riskyOpsAllowed
         ELSE FALSE

BreakSync ==
  /\ ~permanentlyBlocked
  /\ syncAligned
  /\ syncAligned' = FALSE
  /\ UNCHANGED <<nowEpoch, oracleEpoch, permanentlyBlocked, riskyActionRequested>>
  /\ riskyOpsAllowed' = FALSE

RequestRiskyAction ==
  /\ ~riskyActionRequested
  /\ ~permanentlyBlocked
  /\ riskyActionRequested' = TRUE
  /\ UNCHANGED <<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyOpsAllowed>>

UpdateOracle ==
  /\ ~permanentlyBlocked
  /\ ~OracleFresh
  /\ oracleEpoch' = nowEpoch
  /\ UNCHANGED <<nowEpoch, syncAligned, permanentlyBlocked, riskyActionRequested>>
  /\ riskyOpsAllowed' = FALSE

RepairSync ==
  /\ ~permanentlyBlocked
  /\ OracleFresh
  /\ ~syncAligned
  /\ syncAligned' = TRUE
  /\ UNCHANGED <<nowEpoch, oracleEpoch, permanentlyBlocked, riskyActionRequested>>
  /\ riskyOpsAllowed' = FALSE

ReenableRiskyOps ==
  /\ riskyActionRequested
  /\ HealthyNow
  /\ ~riskyOpsAllowed
  /\ riskyOpsAllowed' = TRUE
  /\ UNCHANGED <<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested>>

BlockPermanently ==
  /\ ~permanentlyBlocked
  /\ ~OracleFresh
  /\ permanentlyBlocked' = TRUE
  /\ UNCHANGED <<nowEpoch, oracleEpoch, syncAligned, riskyActionRequested>>
  /\ riskyOpsAllowed' = FALSE

Idle ==
  /\ Quiescent
  /\ UNCHANGED <<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested, riskyOpsAllowed>>

Next ==
  AdvanceTime
  \/ BreakSync
  \/ RequestRiskyAction
  \/ UpdateOracle
  \/ RepairSync
  \/ ReenableRiskyOps
  \/ BlockPermanently
  \/ Idle

Spec ==
  Init /\ [][Next]_<<
    nowEpoch,
    oracleEpoch,
    syncAligned,
    permanentlyBlocked,
    riskyActionRequested,
    riskyOpsAllowed
  >>

EventuallyFreshOrBlocked ==
  []((~OracleFresh /\ ~permanentlyBlocked) => <> (OracleFresh \/ permanentlyBlocked))

HealthyRequestEventuallyResolved ==
  []((riskyActionRequested /\ HealthyNow) => <> (riskyOpsAllowed \/ permanentlyBlocked))

Fair ==
  /\ WF_<<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested, riskyOpsAllowed>>(UpdateOracle)
  /\ WF_<<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested, riskyOpsAllowed>>(RepairSync)
  /\ SF_<<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested, riskyOpsAllowed>>(ReenableRiskyOps)
  /\ WF_<<nowEpoch, oracleEpoch, syncAligned, permanentlyBlocked, riskyActionRequested, riskyOpsAllowed>>(BlockPermanently)

FairImpliesEventuallyFreshOrBlocked ==
  Fair => EventuallyFreshOrBlocked

FairImpliesHealthyRequestEventuallyResolved ==
  Fair => HealthyRequestEventuallyResolved

====
