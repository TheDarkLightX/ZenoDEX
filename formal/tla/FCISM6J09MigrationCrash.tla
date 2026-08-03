---- MODULE FCISM6J09MigrationCrash ----
EXTENDS Integers

(*
Bounded control model for the FCIS M6 J09 migration/crash campaign.

The Python model carries complete rows and roots. This TLA+ shadow retains
the same control obligations as bounded counts and version labels so TLC can
independently check the phase/crash relation.

This is a control model. It does not model cryptographic authenticity, SQL
isolation, process scheduling, or a production datastore.
*)

CONSTANTS PhaseMax, EpochMax, HistoryMax, GenerationMax

Phases == 0..PhaseMax
Writers == {"NONE", "LEGACY", "TARGET"}
EvidenceVersions == {"V1", "V2"}
Observations == {"NONE", "PRE", "POST"}

AllowedWriterFor(p) ==
  IF p <= 2 THEN "LEGACY"
  ELSE IF p = 4 \/ p = 6 THEN "TARGET"
  ELSE "NONE"

ExpectedEvidenceFor(p) == IF p <= 3 THEN "V1" ELSE "V2"
ExpectedEpochFor(p) == IF p <= 3 THEN 0 ELSE 1

VARIABLES
  phase,
  epoch,
  allowedWriter,
  activeWriter,
  authorized,
  restartGeneration,
  authorizedGeneration,
  evidence,
  historyEvidence,
  head,
  residualCount,
  nullifierCount,
  outboxCount,
  deliveredCount,
  acknowledgedCount,
  pending,
  pendingSequence,
  pendingEvidence,
  crashed,
  observation

vars == <<
  phase,
  epoch,
  allowedWriter,
  activeWriter,
  authorized,
  restartGeneration,
  authorizedGeneration,
  evidence,
  historyEvidence,
  head,
  residualCount,
  nullifierCount,
  outboxCount,
  deliveredCount,
  acknowledgedCount,
  pending,
  pendingSequence,
  pendingEvidence,
  crashed,
  observation
>>

Init ==
  /\ phase = 0
  /\ epoch = 0
  /\ allowedWriter = "LEGACY"
  /\ activeWriter = "LEGACY"
  /\ authorized = TRUE
  /\ restartGeneration = 0
  /\ authorizedGeneration = 0
  /\ evidence = "V1"
  /\ historyEvidence = "V1"
  /\ head = 0
  /\ residualCount = 0
  /\ nullifierCount = 0
  /\ outboxCount = 0
  /\ deliveredCount = 0
  /\ acknowledgedCount = 0
  /\ pending = FALSE
  /\ pendingSequence = 0
  /\ pendingEvidence = "V1"
  /\ crashed = FALSE
  /\ observation = "NONE"

TypeOK ==
  /\ phase \in Phases
  /\ epoch \in 0..EpochMax
  /\ allowedWriter \in Writers
  /\ activeWriter \in Writers
  /\ authorized \in BOOLEAN
  /\ restartGeneration \in 0..GenerationMax
  /\ authorizedGeneration \in 0..GenerationMax
  /\ evidence \in EvidenceVersions
  /\ historyEvidence \in EvidenceVersions
  /\ head \in 0..HistoryMax
  /\ residualCount \in 0..HistoryMax
  /\ nullifierCount \in 0..HistoryMax
  /\ outboxCount \in 0..HistoryMax
  /\ deliveredCount \in 0..HistoryMax
  /\ acknowledgedCount \in 0..HistoryMax
  /\ pending \in BOOLEAN
  /\ pendingSequence \in 0..(HistoryMax + 1)
  /\ pendingEvidence \in EvidenceVersions
  /\ crashed \in BOOLEAN
  /\ observation \in Observations

PhaseShape ==
  /\ allowedWriter = AllowedWriterFor(phase)
  /\ epoch = ExpectedEpochFor(phase)
  /\ evidence = ExpectedEvidenceFor(phase)
  /\ historyEvidence = evidence

OneWriter == allowedWriter \in Writers

CompleteHistory ==
  /\ head = residualCount
  /\ head = nullifierCount
  /\ head = outboxCount
  /\ head <= HistoryMax

CompletePublicationAtom ==
  /\ pending =>
       /\ pendingSequence = head + 1
       /\ pendingEvidence = evidence
  /\ ~pending => pendingSequence \in 0..(HistoryMax + 1)

NoMixedEvidence ==
  /\ historyEvidence = evidence
  /\ pending => pendingEvidence = evidence

CrashObservationClosed ==
  /\ crashed =>
       /\ observation \in {"PRE", "POST"}
       /\ ~pending
       /\ ~authorized
       /\ activeWriter = "NONE"
  /\ ~crashed => observation = "NONE"

FreshAuthorizationLatch ==
  /\ activeWriter # "NONE" =>
       /\ authorized
       /\ authorizedGeneration = restartGeneration
       /\ activeWriter = allowedWriter
  /\ ~authorized => activeWriter = "NONE"

DeliveryAckProvenance ==
  /\ acknowledgedCount <= deliveredCount
  /\ deliveredCount <= outboxCount

VarsBounded ==
  /\ restartGeneration <= GenerationMax
  /\ authorizedGeneration <= restartGeneration

AdvancePhase ==
  /\ phase < PhaseMax
  /\ ~crashed
  /\ ~pending
  /\ phase' = phase + 1
  /\ epoch' = ExpectedEpochFor(phase + 1)
  /\ allowedWriter' = AllowedWriterFor(phase + 1)
  /\ activeWriter' = "NONE"
  /\ authorized' = FALSE
  /\ evidence' = ExpectedEvidenceFor(phase + 1)
  /\ historyEvidence' = ExpectedEvidenceFor(phase + 1)
  /\ UNCHANGED <<
       restartGeneration,
       authorizedGeneration,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       acknowledgedCount,
       pending,
       pendingSequence,
       pendingEvidence,
       crashed,
       observation
     >>

FreshAuthorize ==
  /\ ~crashed
  /\ ~pending
  /\ authorized' = TRUE
  /\ authorizedGeneration' = restartGeneration
  /\ activeWriter' = allowedWriter
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       restartGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       acknowledgedCount,
       pending,
       pendingSequence,
       pendingEvidence,
       crashed,
       observation
     >>

Prepare(w) ==
  /\ w \in {"LEGACY", "TARGET"}
  /\ ~crashed
  /\ ~pending
  /\ authorized
  /\ activeWriter = w
  /\ allowedWriter = w
  /\ head < HistoryMax
  /\ pending' = TRUE
  /\ pendingSequence' = head + 1
  /\ pendingEvidence' = evidence
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       activeWriter,
       authorized,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       acknowledgedCount,
       crashed,
       observation
     >>

PublishPending ==
  /\ pending
  /\ ~crashed
  /\ authorized
  /\ activeWriter = allowedWriter
  /\ allowedWriter # "NONE"
  /\ head < HistoryMax
  /\ head' = head + 1
  /\ residualCount' = residualCount + 1
  /\ nullifierCount' = nullifierCount + 1
  /\ outboxCount' = outboxCount + 1
  /\ pending' = FALSE
  /\ authorized' = FALSE
  /\ activeWriter' = "NONE"
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       deliveredCount,
       acknowledgedCount,
       pendingSequence,
       pendingEvidence,
       crashed,
       observation
     >>

CrashPre ==
  /\ ~crashed
  /\ pending' = FALSE
  /\ crashed' = TRUE
  /\ observation' = "PRE"
  /\ authorized' = FALSE
  /\ activeWriter' = "NONE"
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       acknowledgedCount,
       pendingSequence,
       pendingEvidence
     >>

CrashPost ==
  /\ ~crashed
  /\ head' = IF pending THEN head + 1 ELSE head
  /\ residualCount' = IF pending THEN residualCount + 1 ELSE residualCount
  /\ nullifierCount' = IF pending THEN nullifierCount + 1 ELSE nullifierCount
  /\ outboxCount' = IF pending THEN outboxCount + 1 ELSE outboxCount
  /\ pending' = FALSE
  /\ crashed' = TRUE
  /\ observation' = "POST"
  /\ authorized' = FALSE
  /\ activeWriter' = "NONE"
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       deliveredCount,
       acknowledgedCount,
       pendingSequence,
       pendingEvidence
     >>

Restart ==
  /\ crashed
  /\ restartGeneration < GenerationMax
  /\ crashed' = FALSE
  /\ observation' = "NONE"
  /\ pending' = FALSE
  /\ authorized' = FALSE
  /\ activeWriter' = "NONE"
  /\ restartGeneration' = restartGeneration + 1
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       authorizedGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       acknowledgedCount,
       pendingSequence,
       pendingEvidence
     >>

Deliver ==
  /\ ~crashed
  /\ deliveredCount < outboxCount
  /\ deliveredCount' = deliveredCount + 1
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       activeWriter,
       authorized,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       acknowledgedCount,
       pending,
       pendingSequence,
       pendingEvidence,
       crashed,
       observation
     >>

Ack ==
  /\ ~crashed
  /\ acknowledgedCount < deliveredCount
  /\ acknowledgedCount' = acknowledgedCount + 1
  /\ UNCHANGED <<
       phase,
       epoch,
       allowedWriter,
       activeWriter,
       authorized,
       restartGeneration,
       authorizedGeneration,
       evidence,
       historyEvidence,
       head,
       residualCount,
       nullifierCount,
       outboxCount,
       deliveredCount,
       pending,
       pendingSequence,
       pendingEvidence,
       crashed,
       observation
     >>

Reject == UNCHANGED vars

Next ==
  AdvancePhase
  \/ FreshAuthorize
  \/ (\E w \in {"LEGACY", "TARGET"}: Prepare(w))
  \/ PublishPending
  \/ CrashPre
  \/ CrashPost
  \/ Restart
  \/ Deliver
  \/ Ack
  \/ Reject

Spec == Init /\ [][Next]_vars

====
