---- MODULE ZenoSdkWalletSyncCheckpoint ----
EXTENDS Naturals

(*
Bounded shadow model for Zeno SDK wallet-sync checkpoint updates.

Purpose:
- model the browser/mobile wallet-sync reducer that consumes proof-carrying
  checkpoint bundles,
- keep hash parsing, signature verification, and bundle validation as
  host-computed predicates,
- prove the control rule that accepted sync updates cannot roll back, cannot
  change chain id, and cannot replace same-height app/checkpoint commitments.

This is intentionally abstract:
- no BLS arithmetic,
- no JSON parsing,
- no full ledger replay,
- no wallet signing or transaction execution authority.

Host predicates represented here:
- candidateValidBundle: the bundle hash, checkpoint hash, signer-registry root,
  and current trust profile have already been validated,
- currentStateHashValid: the existing wallet-sync state hash validates before it
  is used as a base state.
*)

CONSTANTS CHAINS, HEIGHTS, ROOTS, BUNDLES

VARIABLES
  statePresent,
  chain,
  height,
  appHash,
  checkpointHash,
  bundleHash,
  currentStateHashValid,
  candidateChain,
  candidateHeight,
  candidateAppHash,
  candidateCheckpointHash,
  candidateBundleHash,
  candidateValidBundle,
  prevStatePresent,
  prevChain,
  prevHeight,
  prevAppHash,
  prevCheckpointHash,
  prevBundleHash,
  accepted,
  lastAction

Vars ==
  <<statePresent, chain, height, appHash, checkpointHash, bundleHash,
    currentStateHashValid, candidateChain, candidateHeight, candidateAppHash,
    candidateCheckpointHash, candidateBundleHash, candidateValidBundle,
    prevStatePresent, prevChain, prevHeight, prevAppHash, prevCheckpointHash,
    prevBundleHash, accepted, lastAction>>

TypeOK ==
  /\ statePresent \in BOOLEAN
  /\ chain \in CHAINS
  /\ height \in HEIGHTS
  /\ appHash \in ROOTS
  /\ checkpointHash \in ROOTS
  /\ bundleHash \in BUNDLES
  /\ currentStateHashValid \in BOOLEAN
  /\ candidateChain \in CHAINS
  /\ candidateHeight \in HEIGHTS
  /\ candidateAppHash \in ROOTS
  /\ candidateCheckpointHash \in ROOTS
  /\ candidateBundleHash \in BUNDLES
  /\ candidateValidBundle \in BOOLEAN
  /\ prevStatePresent \in BOOLEAN
  /\ prevChain \in CHAINS
  /\ prevHeight \in HEIGHTS
  /\ prevAppHash \in ROOTS
  /\ prevCheckpointHash \in ROOTS
  /\ prevBundleHash \in BUNDLES
  /\ accepted \in BOOLEAN
  /\ lastAction \in {
       "init",
       "select_candidate",
       "accept_initial",
       "accept_advance",
       "accept_same",
       "reject_invalid_current",
       "reject_invalid_bundle",
       "reject_chain_mismatch",
       "reject_rollback",
       "reject_same_height_drift"
     }

RecordPrevious ==
  /\ prevStatePresent' = statePresent
  /\ prevChain' = chain
  /\ prevHeight' = height
  /\ prevAppHash' = appHash
  /\ prevCheckpointHash' = checkpointHash
  /\ prevBundleHash' = bundleHash

NoStateChange ==
  /\ statePresent' = statePresent
  /\ chain' = chain
  /\ height' = height
  /\ appHash' = appHash
  /\ checkpointHash' = checkpointHash
  /\ bundleHash' = bundleHash

ChooseCandidate ==
  /\ candidateChain' \in CHAINS
  /\ candidateHeight' \in HEIGHTS
  /\ candidateAppHash' \in ROOTS
  /\ candidateCheckpointHash' \in ROOTS
  /\ candidateBundleHash' \in BUNDLES
  /\ candidateValidBundle' \in BOOLEAN

KeepCandidate ==
  /\ candidateChain' = candidateChain
  /\ candidateHeight' = candidateHeight
  /\ candidateAppHash' = candidateAppHash
  /\ candidateCheckpointHash' = candidateCheckpointHash
  /\ candidateBundleHash' = candidateBundleHash
  /\ candidateValidBundle' = candidateValidBundle

Init ==
  /\ statePresent = FALSE
  /\ chain = "chain_a"
  /\ height = 0
  /\ appHash = "root_a"
  /\ checkpointHash = "root_a"
  /\ bundleHash = "bundle_a"
  /\ currentStateHashValid = TRUE
  /\ candidateChain = "chain_a"
  /\ candidateHeight = 0
  /\ candidateAppHash = "root_a"
  /\ candidateCheckpointHash = "root_a"
  /\ candidateBundleHash = "bundle_a"
  /\ candidateValidBundle = FALSE
  /\ prevStatePresent = FALSE
  /\ prevChain = chain
  /\ prevHeight = height
  /\ prevAppHash = appHash
  /\ prevCheckpointHash = checkpointHash
  /\ prevBundleHash = bundleHash
  /\ accepted = FALSE
  /\ lastAction = "init"

SelectCandidate ==
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ ChooseCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "select_candidate"

AcceptInitial ==
  /\ ~statePresent
  /\ candidateValidBundle
  /\ RecordPrevious
  /\ statePresent' = TRUE
  /\ chain' = candidateChain
  /\ height' = candidateHeight
  /\ appHash' = candidateAppHash
  /\ checkpointHash' = candidateCheckpointHash
  /\ bundleHash' = candidateBundleHash
  /\ currentStateHashValid' = TRUE
  /\ KeepCandidate
  /\ accepted' = TRUE
  /\ lastAction' = "accept_initial"

AcceptAdvance ==
  /\ statePresent
  /\ currentStateHashValid
  /\ candidateValidBundle
  /\ candidateChain = chain
  /\ candidateHeight > height
  /\ RecordPrevious
  /\ statePresent' = TRUE
  /\ chain' = chain
  /\ height' = candidateHeight
  /\ appHash' = candidateAppHash
  /\ checkpointHash' = candidateCheckpointHash
  /\ bundleHash' = candidateBundleHash
  /\ currentStateHashValid' = TRUE
  /\ KeepCandidate
  /\ accepted' = TRUE
  /\ lastAction' = "accept_advance"

AcceptSame ==
  /\ statePresent
  /\ currentStateHashValid
  /\ candidateValidBundle
  /\ candidateChain = chain
  /\ candidateHeight = height
  /\ candidateAppHash = appHash
  /\ candidateCheckpointHash = checkpointHash
  /\ RecordPrevious
  /\ statePresent' = TRUE
  /\ chain' = chain
  /\ height' = height
  /\ appHash' = appHash
  /\ checkpointHash' = checkpointHash
  /\ bundleHash' = candidateBundleHash
  /\ currentStateHashValid' = TRUE
  /\ KeepCandidate
  /\ accepted' = TRUE
  /\ lastAction' = "accept_same"

RejectInvalidCurrent ==
  /\ statePresent
  /\ ~currentStateHashValid
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ KeepCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "reject_invalid_current"

RejectInvalidBundle ==
  /\ ~candidateValidBundle
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ KeepCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "reject_invalid_bundle"

RejectChainMismatch ==
  /\ statePresent
  /\ currentStateHashValid
  /\ candidateValidBundle
  /\ candidateChain # chain
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ KeepCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "reject_chain_mismatch"

RejectRollback ==
  /\ statePresent
  /\ currentStateHashValid
  /\ candidateValidBundle
  /\ candidateChain = chain
  /\ candidateHeight < height
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ KeepCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "reject_rollback"

RejectSameHeightDrift ==
  /\ statePresent
  /\ currentStateHashValid
  /\ candidateValidBundle
  /\ candidateChain = chain
  /\ candidateHeight = height
  /\ (candidateAppHash # appHash \/ candidateCheckpointHash # checkpointHash)
  /\ RecordPrevious
  /\ NoStateChange
  /\ currentStateHashValid' \in BOOLEAN
  /\ KeepCandidate
  /\ accepted' = FALSE
  /\ lastAction' = "reject_same_height_drift"

Next ==
  SelectCandidate
  \/ AcceptInitial
  \/ AcceptAdvance
  \/ AcceptSame
  \/ RejectInvalidCurrent
  \/ RejectInvalidBundle
  \/ RejectChainMismatch
  \/ RejectRollback
  \/ RejectSameHeightDrift

Spec ==
  Init /\ [][Next]_Vars

RejectedDoesNotMutateState ==
  ~accepted =>
    /\ statePresent = prevStatePresent
    /\ chain = prevChain
    /\ height = prevHeight
    /\ appHash = prevAppHash
    /\ checkpointHash = prevCheckpointHash
    /\ bundleHash = prevBundleHash

AcceptedRequiresValidBundle ==
  accepted => candidateValidBundle

AcceptedRequiresValidPriorState ==
  accepted /\ prevStatePresent => currentStateHashValid

AcceptedNeverRollsBack ==
  accepted /\ prevStatePresent => height >= prevHeight

AcceptedKeepsChainStableAfterInitialSync ==
  accepted /\ prevStatePresent => chain = prevChain

AcceptedSameHeightCannotDrift ==
  accepted /\ prevStatePresent /\ height = prevHeight =>
    /\ appHash = prevAppHash
    /\ checkpointHash = prevCheckpointHash

AcceptedStateMatchesCandidate ==
  accepted =>
    /\ statePresent
    /\ height = candidateHeight
    /\ appHash = candidateAppHash
    /\ checkpointHash = candidateCheckpointHash
    /\ bundleHash = candidateBundleHash

====
