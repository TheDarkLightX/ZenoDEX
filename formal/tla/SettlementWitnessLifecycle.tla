---- MODULE SettlementWitnessLifecycle ----
EXTENDS Integers

(*
Bounded TLA+ model for the settlement witness lifecycle.

Purpose:
- Capture the temporal control obligations behind the settlement witness lifecycle lane.
- Model acceptance before expiry, possible witness invalidation, time progression,
  and total resolution via settle or reject-with-reason.
- Check that accepted witnesses do not remain unresolved forever on the modeled control path.

This is intentionally abstract:
- no balances, pools, or price arithmetic,
- no scheduler throughput guarantee,
- only lifecycle progression and total resolution.
*)

TIME_MAX == 4
EXPIRY == 2

VARIABLES
  now,
  accepted,
  acceptTime,
  witnessValid,
  resolved,
  settled,
  rejected,
  reasonPresent

BeforeExpiry ==
  now <= EXPIRY

AcceptedBeforeExpiry ==
  accepted /\ acceptTime >= 0 /\ acceptTime <= EXPIRY

TypeOK ==
  /\ now \in 0..TIME_MAX
  /\ acceptTime \in -1..TIME_MAX
  /\ accepted \in BOOLEAN
  /\ witnessValid \in BOOLEAN
  /\ resolved \in BOOLEAN
  /\ settled \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN

ResolutionConsistent ==
  /\ resolved = (settled \/ rejected)
  /\ ~(settled /\ rejected)
  /\ rejected => reasonPresent
  /\ settled => ~reasonPresent

Init ==
  /\ now = 0
  /\ accepted = FALSE
  /\ acceptTime = -1
  /\ witnessValid = TRUE
  /\ resolved = FALSE
  /\ settled = FALSE
  /\ rejected = FALSE
  /\ reasonPresent = FALSE

AdvanceTime ==
  /\ now < TIME_MAX
  /\ now' = now + 1
  /\ UNCHANGED <<accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>

AcceptWitness ==
  /\ ~accepted
  /\ BeforeExpiry
  /\ accepted' = TRUE
  /\ acceptTime' = now
  /\ UNCHANGED <<now, witnessValid, resolved, settled, rejected, reasonPresent>>

LoseValidity ==
  /\ accepted
  /\ ~resolved
  /\ witnessValid
  /\ witnessValid' = FALSE
  /\ UNCHANGED <<now, accepted, acceptTime, resolved, settled, rejected, reasonPresent>>

Settle ==
  /\ accepted
  /\ AcceptedBeforeExpiry
  /\ witnessValid
  /\ BeforeExpiry
  /\ ~resolved
  /\ resolved' = TRUE
  /\ settled' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<now, accepted, acceptTime, witnessValid>>

RejectInvalid ==
  /\ accepted
  /\ ~resolved
  /\ ~witnessValid
  /\ resolved' = TRUE
  /\ settled' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<now, accepted, acceptTime, witnessValid>>

RejectExpired ==
  /\ accepted
  /\ AcceptedBeforeExpiry
  /\ ~resolved
  /\ ~BeforeExpiry
  /\ resolved' = TRUE
  /\ settled' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<now, accepted, acceptTime, witnessValid>>

Idle ==
  /\ resolved \/ (~accepted /\ now = TIME_MAX)
  /\ UNCHANGED <<now, accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>

Next ==
  AdvanceTime
  \/ AcceptWitness
  \/ LoseValidity
  \/ Settle
  \/ RejectInvalid
  \/ RejectExpired
  \/ Idle

Spec ==
  Init /\ [][Next]_<<now, accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>

AcceptedBeforeExpiryEventuallyResolved ==
  []((AcceptedBeforeExpiry /\ ~resolved) => <> (settled \/ (rejected /\ reasonPresent)))

Fair ==
  /\ WF_<<now, accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>(Settle)
  /\ WF_<<now, accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>(RejectInvalid)
  /\ WF_<<now, accepted, acceptTime, witnessValid, resolved, settled, rejected, reasonPresent>>(RejectExpired)

FairImpliesAcceptedBeforeExpiryEventuallyResolved ==
  Fair => AcceptedBeforeExpiryEventuallyResolved

====
