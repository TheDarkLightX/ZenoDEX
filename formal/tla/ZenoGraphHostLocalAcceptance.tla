---- MODULE ZenoGraphHostLocalAcceptance ----
EXTENDS Naturals

(*
Bounded host/local shadow semantics for ZenoGraph fact acceptance.

The model separates:
- host-side proposal creation,
- local validation,
- local accept/reject,
- execution visibility.

It is intentionally small. The purpose is to make the governance boundary
explicit:
- proposed facts are not execution-visible,
- acceptance requires a valid validation state,
- reject and unknown-validation paths remain fail-closed.
*)

VARIABLES
  proposalPresent,
  validationState,
  acceptedVisible,
  rejectedVisible,
  executionFactVisible,
  lastAction

TypeOK ==
  /\ proposalPresent \in BOOLEAN
  /\ validationState \in {"unknown", "valid", "invalid"}
  /\ acceptedVisible \in BOOLEAN
  /\ rejectedVisible \in BOOLEAN
  /\ executionFactVisible \in BOOLEAN
  /\ lastAction \in {
      "init",
      "host_propose",
      "local_validate_valid",
      "local_validate_invalid",
      "local_accept",
      "local_reject"
     }

Init ==
  /\ proposalPresent = FALSE
  /\ validationState = "unknown"
  /\ acceptedVisible = FALSE
  /\ rejectedVisible = FALSE
  /\ executionFactVisible = FALSE
  /\ lastAction = "init"

HostPropose ==
  /\ proposalPresent' = TRUE
  /\ validationState' = "unknown"
  /\ acceptedVisible' = FALSE
  /\ rejectedVisible' = FALSE
  /\ executionFactVisible' = FALSE
  /\ lastAction' = "host_propose"

LocalValidateValid ==
  /\ proposalPresent
  /\ validationState = "unknown"
  /\ proposalPresent' = proposalPresent
  /\ validationState' = "valid"
  /\ acceptedVisible' = FALSE
  /\ rejectedVisible' = FALSE
  /\ executionFactVisible' = FALSE
  /\ lastAction' = "local_validate_valid"

LocalValidateInvalid ==
  /\ proposalPresent
  /\ validationState = "unknown"
  /\ proposalPresent' = proposalPresent
  /\ validationState' = "invalid"
  /\ acceptedVisible' = FALSE
  /\ rejectedVisible' = FALSE
  /\ executionFactVisible' = FALSE
  /\ lastAction' = "local_validate_invalid"

LocalAccept ==
  /\ proposalPresent
  /\ validationState = "valid"
  /\ proposalPresent' = proposalPresent
  /\ validationState' = validationState
  /\ acceptedVisible' = TRUE
  /\ rejectedVisible' = FALSE
  /\ executionFactVisible' = TRUE
  /\ lastAction' = "local_accept"

LocalReject ==
  /\ proposalPresent
  /\ validationState # "valid"
  /\ proposalPresent' = proposalPresent
  /\ validationState' = validationState
  /\ acceptedVisible' = FALSE
  /\ rejectedVisible' = TRUE
  /\ executionFactVisible' = FALSE
  /\ lastAction' = "local_reject"

Next ==
  HostPropose
  \/ LocalValidateValid
  \/ LocalValidateInvalid
  \/ LocalAccept
  \/ LocalReject

Spec ==
  Init /\ [][Next]_<<
    proposalPresent,
    validationState,
    acceptedVisible,
    rejectedVisible,
    executionFactVisible,
    lastAction
  >>

AcceptedRequiresValidValidation ==
  acceptedVisible => validationState = "valid"

ExecutionVisibleOnlyIfAccepted ==
  executionFactVisible => acceptedVisible

UnknownOrInvalidNeverVisible ==
  validationState # "valid" => ~executionFactVisible

RejectAndProposalFailClosed ==
  (lastAction = "host_propose" \/ lastAction = "local_validate_invalid" \/ lastAction = "local_reject")
    => ~executionFactVisible

====
