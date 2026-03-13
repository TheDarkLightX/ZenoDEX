---- MODULE PerpIngressSchemaShadow ----

(*
Independent shadow semantics for the outer perps Tau ingress schema guard.

This model keeps the host/Tau split explicit:
- the host projects structural facts and action decoding,
- the policy accepts only one supported auth mode,
- the selected mode must carry its corresponding auth bundle,
- all outer preconditions must hold.
*)

VARIABLES
  moduleOk,
  marketIdOk,
  versionOk,
  unknownFieldsOk,
  actionKnown,
  actionOneHot,
  signedSelected,
  oracleSelected,
  signedAuthOk,
  oracleAuthOk,
  hostProjectionOk,
  actionSelectionOk,
  authBundleOk,
  ingressPreconditionsOk,
  accepted,
  lastAction

TypeOK ==
  /\ moduleOk \in BOOLEAN
  /\ marketIdOk \in BOOLEAN
  /\ versionOk \in BOOLEAN
  /\ unknownFieldsOk \in BOOLEAN
  /\ actionKnown \in BOOLEAN
  /\ actionOneHot \in BOOLEAN
  /\ signedSelected \in BOOLEAN
  /\ oracleSelected \in BOOLEAN
  /\ signedAuthOk \in BOOLEAN
  /\ oracleAuthOk \in BOOLEAN
  /\ hostProjectionOk \in BOOLEAN
  /\ actionSelectionOk \in BOOLEAN
  /\ authBundleOk \in BOOLEAN
  /\ ingressPreconditionsOk \in BOOLEAN
  /\ accepted \in BOOLEAN
  /\ lastAction \in {
       "init",
       "accept_signed",
       "accept_oracle",
       "reject_missing_auth_bundle",
       "reject_bad_selection",
       "reject_bad_preconditions"
     }

ExactlyOneAuthMode ==
  (signedSelected /\ ~oracleSelected) \/ (~signedSelected /\ oracleSelected)

DerivedActionSelectionOk ==
  actionKnown /\ actionOneHot

DerivedAuthBundleOk ==
  ((signedSelected /\ ~oracleSelected) /\ signedAuthOk)
  \/ ((~signedSelected /\ oracleSelected) /\ oracleAuthOk)

DerivedIngressPreconditionsOk ==
  moduleOk /\ marketIdOk /\ versionOk /\ unknownFieldsOk /\ hostProjectionOk

Init ==
  /\ moduleOk = FALSE
  /\ marketIdOk = FALSE
  /\ versionOk = FALSE
  /\ unknownFieldsOk = FALSE
  /\ actionKnown = FALSE
  /\ actionOneHot = FALSE
  /\ signedSelected = FALSE
  /\ oracleSelected = FALSE
  /\ signedAuthOk = FALSE
  /\ oracleAuthOk = FALSE
  /\ hostProjectionOk = FALSE
  /\ actionSelectionOk = FALSE
  /\ authBundleOk = FALSE
  /\ ingressPreconditionsOk = FALSE
  /\ accepted = FALSE
  /\ lastAction = "init"

AcceptSigned ==
  /\ moduleOk' = TRUE
  /\ marketIdOk' = TRUE
  /\ versionOk' = TRUE
  /\ unknownFieldsOk' = TRUE
  /\ actionKnown' = TRUE
  /\ actionOneHot' = TRUE
  /\ signedSelected' = TRUE
  /\ oracleSelected' = FALSE
  /\ signedAuthOk' = TRUE
  /\ oracleAuthOk' = FALSE
  /\ hostProjectionOk' = TRUE
  /\ actionSelectionOk' = TRUE
  /\ authBundleOk' = TRUE
  /\ ingressPreconditionsOk' = TRUE
  /\ accepted' = TRUE
  /\ lastAction' = "accept_signed"

AcceptOracle ==
  /\ moduleOk' = TRUE
  /\ marketIdOk' = TRUE
  /\ versionOk' = TRUE
  /\ unknownFieldsOk' = TRUE
  /\ actionKnown' = TRUE
  /\ actionOneHot' = TRUE
  /\ signedSelected' = FALSE
  /\ oracleSelected' = TRUE
  /\ signedAuthOk' = FALSE
  /\ oracleAuthOk' = TRUE
  /\ hostProjectionOk' = TRUE
  /\ actionSelectionOk' = TRUE
  /\ authBundleOk' = TRUE
  /\ ingressPreconditionsOk' = TRUE
  /\ accepted' = TRUE
  /\ lastAction' = "accept_oracle"

RejectMissingAuthBundle ==
  /\ moduleOk' = TRUE
  /\ marketIdOk' = TRUE
  /\ versionOk' = TRUE
  /\ unknownFieldsOk' = TRUE
  /\ actionKnown' = TRUE
  /\ actionOneHot' = TRUE
  /\ signedSelected' = TRUE
  /\ oracleSelected' = FALSE
  /\ signedAuthOk' = FALSE
  /\ oracleAuthOk' = FALSE
  /\ hostProjectionOk' = TRUE
  /\ actionSelectionOk' = TRUE
  /\ authBundleOk' = FALSE
  /\ ingressPreconditionsOk' = TRUE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_missing_auth_bundle"

RejectBadSelection ==
  /\ moduleOk' = TRUE
  /\ marketIdOk' = TRUE
  /\ versionOk' = TRUE
  /\ unknownFieldsOk' = TRUE
  /\ actionKnown' = TRUE
  /\ actionOneHot' = FALSE
  /\ signedSelected' = TRUE
  /\ oracleSelected' = FALSE
  /\ signedAuthOk' = TRUE
  /\ oracleAuthOk' = FALSE
  /\ hostProjectionOk' = TRUE
  /\ actionSelectionOk' = FALSE
  /\ authBundleOk' = TRUE
  /\ ingressPreconditionsOk' = TRUE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_bad_selection"

RejectBadPreconditions ==
  /\ moduleOk' = TRUE
  /\ marketIdOk' = TRUE
  /\ versionOk' = TRUE
  /\ unknownFieldsOk' = TRUE
  /\ actionKnown' = TRUE
  /\ actionOneHot' = TRUE
  /\ signedSelected' = TRUE
  /\ oracleSelected' = FALSE
  /\ signedAuthOk' = TRUE
  /\ oracleAuthOk' = FALSE
  /\ hostProjectionOk' = FALSE
  /\ actionSelectionOk' = TRUE
  /\ authBundleOk' = TRUE
  /\ ingressPreconditionsOk' = FALSE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_bad_preconditions"

Next ==
  AcceptSigned
  \/ AcceptOracle
  \/ RejectMissingAuthBundle
  \/ RejectBadSelection
  \/ RejectBadPreconditions

Spec ==
  Init /\ [][Next]_<<
    moduleOk,
    marketIdOk,
    versionOk,
    unknownFieldsOk,
    actionKnown,
    actionOneHot,
    signedSelected,
    oracleSelected,
    signedAuthOk,
    oracleAuthOk,
    hostProjectionOk,
    actionSelectionOk,
    authBundleOk,
    ingressPreconditionsOk,
    accepted,
    lastAction
  >>

ActionSelectionMatchesDerived ==
  actionSelectionOk = DerivedActionSelectionOk

AuthBundleMatchesDerived ==
  authBundleOk = DerivedAuthBundleOk

IngressPreconditionsMatchDerived ==
  ingressPreconditionsOk = DerivedIngressPreconditionsOk

AcceptedRequiresSingleModeAndPreconditions ==
  accepted =>
    (
      /\ ExactlyOneAuthMode
      /\ actionSelectionOk
      /\ authBundleOk
      /\ ingressPreconditionsOk
    )

====
