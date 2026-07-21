---- MODULE GenericTokenAuthorityComposition ----
EXTENDS Naturals

(*
Bounded composition model for two registered generic assets and two actors.

Committed registration binds each exact asset to one exact mint actor. Every
accepted state equates committed supply with wallet, AMM, perps, pending-stake,
and active-stake units. Staging is private in the runtime; exposing it here is
a safety over-approximation. No staged value becomes committed until the
global postcondition succeeds. Rejection preserves the exact committed world.

The tiny MaxSupply and MaxNonce bounds cover zero, ordinary, boundary,
overflow, underflow, nonce exhaustion, two-operation commit, and late failure.
Lean and executable refinement tests own the production u32 arithmetic claim.
*)

CONSTANTS AssetA, AssetB, UnknownAsset, ActorA, ActorB, MaxSupply, MaxNonce

ASSUME /\ AssetA # AssetB
       /\ UnknownAsset # AssetA
       /\ UnknownAsset # AssetB
       /\ ActorA # ActorB

Assets == {AssetA, AssetB}
AssetUniverse == Assets \cup {UnknownAsset}
Actors == {ActorA, ActorB}
TargetAsset == AssetA
TargetMintActor == ActorA

VARIABLES committed, staged, snapshot, phase, lastAction, lastOutcome,
          lastAsset, lastActor, stagedTokenOps, lastTokenOps

vars ==
  <<committed, staged, snapshot, phase, lastAction, lastOutcome,
    lastAsset, lastActor, stagedTokenOps, lastTokenOps>>

WorldType ==
  [ registered    : SUBSET Assets,
    mintAuthority : [Assets -> Actors],
    supply        : [Assets -> 0..MaxSupply],
    wallet        : [Assets -> [Actors -> 0..MaxSupply]],
    pool          : [Assets -> 0..MaxSupply],
    perps         : [Assets -> 0..MaxSupply],
    pendingStake  : [Assets -> 0..MaxSupply],
    activeStake   : [Assets -> 0..MaxSupply],
    nonce         : [Actors -> 0..MaxNonce] ]

InitialAuthority ==
  [asset \in Assets |-> IF asset = AssetA THEN ActorA ELSE ActorB]

ZeroWorld ==
  [ registered    |-> Assets,
    mintAuthority |-> InitialAuthority,
    supply        |-> [asset \in Assets |-> 0],
    wallet        |-> [asset \in Assets |-> [actor \in Actors |-> 0]],
    pool          |-> [asset \in Assets |-> 0],
    perps         |-> [asset \in Assets |-> 0],
    pendingStake  |-> [asset \in Assets |-> 0],
    activeStake   |-> [asset \in Assets |-> 0],
    nonce         |-> [actor \in Actors |-> 0] ]

AccountedUnits(world, asset) ==
  world.wallet[asset][ActorA]
    + world.wallet[asset][ActorB]
    + world.pool[asset]
    + world.perps[asset]
    + world.pendingStake[asset]
    + world.activeStake[asset]

AccountingOK(world) ==
  \A asset \in Assets:
    world.supply[asset] = AccountedUnits(world, asset)

RegistryOK(world) ==
  /\ world.registered = Assets
  /\ world.mintAuthority = InitialAuthority

AssetProjection(world, asset) ==
  <<world.supply[asset],
    world.wallet[asset][ActorA],
    world.wallet[asset][ActorB],
    world.pool[asset],
    world.perps[asset],
    world.pendingStake[asset],
    world.activeStake[asset]>>

TypeOK ==
  /\ committed \in WorldType
  /\ staged \in WorldType
  /\ snapshot \in WorldType
  /\ phase \in {"idle", "staged"}
  /\ lastAction \in {
       "init", "mint", "faucet_mint", "two_mints", "burn",
       "transfer", "wallet_to_pool", "pool_to_wallet",
       "wallet_to_perps", "perps_to_wallet",
       "wallet_to_pending_stake", "activate_stake", "unstake",
       "invalid_projection", "late_batch_failure", "unauthorized_mint",
       "unregistered_asset", "overflow_mint", "underflow_burn",
       "self_transfer", "nonce_exhausted"
     }
  /\ lastOutcome \in {
       "init", "staged", "committed", "reject_staged",
       "reject_authority", "reject_unregistered", "reject_bounds",
       "reject_self", "reject_nonce"
     }
  /\ lastAsset \in AssetUniverse
  /\ lastActor \in Actors
  /\ stagedTokenOps \in 0..2
  /\ lastTokenOps \in 0..2

Init ==
  /\ committed = ZeroWorld
  /\ staged = ZeroWorld
  /\ snapshot = ZeroWorld
  /\ phase = "idle"
  /\ lastAction = "init"
  /\ lastOutcome = "init"
  /\ lastAsset = AssetA
  /\ lastActor = ActorA
  /\ stagedTokenOps = 0
  /\ lastTokenOps = 0

StageCandidate(kind, asset, actor, candidate, tokenOps) ==
  /\ phase = "idle"
  /\ candidate \in WorldType
  /\ committed' = committed
  /\ staged' = candidate
  /\ snapshot' = committed
  /\ phase' = "staged"
  /\ lastAction' = kind
  /\ lastOutcome' = "staged"
  /\ lastAsset' = asset
  /\ lastActor' = actor
  /\ stagedTokenOps' = tokenOps
  /\ lastTokenOps' = 0

StageMint ==
  \E recipient \in Actors:
    /\ committed.mintAuthority[TargetAsset] = TargetMintActor
    /\ committed.supply[TargetAsset] < MaxSupply
    /\ committed.wallet[TargetAsset][recipient] < MaxSupply
    /\ committed.nonce[TargetMintActor] < MaxNonce
    /\ StageCandidate(
         "mint",
         TargetAsset,
         TargetMintActor,
         [committed EXCEPT
           !.supply[TargetAsset] = @ + 1,
           !.wallet[TargetAsset][recipient] = @ + 1,
           !.nonce[TargetMintActor] = @ + 1],
         1)

StageFaucetMint ==
  \E recipient \in Actors:
    /\ committed.mintAuthority[TargetAsset] = TargetMintActor
    /\ committed.supply[TargetAsset] < MaxSupply
    /\ committed.wallet[TargetAsset][recipient] < MaxSupply
    /\ StageCandidate(
         "faucet_mint",
         TargetAsset,
         TargetMintActor,
         [committed EXCEPT
           !.supply[TargetAsset] = @ + 1,
           !.wallet[TargetAsset][recipient] = @ + 1],
         0)

StageTwoMints ==
  \E recipient \in Actors:
    /\ committed.mintAuthority[TargetAsset] = TargetMintActor
    /\ committed.supply[TargetAsset] + 2 <= MaxSupply
    /\ committed.wallet[TargetAsset][recipient] + 2 <= MaxSupply
    /\ committed.nonce[TargetMintActor] + 2 <= MaxNonce
    /\ StageCandidate(
         "two_mints",
         TargetAsset,
         TargetMintActor,
         [committed EXCEPT
           !.supply[TargetAsset] = @ + 2,
           !.wallet[TargetAsset][recipient] = @ + 2,
           !.nonce[TargetMintActor] = @ + 2],
         2)

StageBurn ==
  \E actor \in Actors:
    /\ committed.wallet[TargetAsset][actor] > 0
    /\ committed.supply[TargetAsset] > 0
    /\ committed.nonce[actor] < MaxNonce
    /\ StageCandidate(
         "burn",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.supply[TargetAsset] = @ - 1,
           !.wallet[TargetAsset][actor] = @ - 1,
           !.nonce[actor] = @ + 1],
         1)

StageTransfer ==
  \E actor \in Actors, recipient \in Actors:
    /\ actor # recipient
    /\ committed.wallet[TargetAsset][actor] > 0
    /\ committed.wallet[TargetAsset][recipient] < MaxSupply
    /\ committed.nonce[actor] < MaxNonce
    /\ StageCandidate(
         "transfer",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.wallet[TargetAsset][actor] = @ - 1,
           !.wallet[TargetAsset][recipient] = @ + 1,
           !.nonce[actor] = @ + 1],
         1)

StageWalletToPool ==
  \E actor \in Actors:
    /\ committed.wallet[TargetAsset][actor] > 0
    /\ committed.pool[TargetAsset] < MaxSupply
    /\ StageCandidate(
         "wallet_to_pool",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.wallet[TargetAsset][actor] = @ - 1,
           !.pool[TargetAsset] = @ + 1],
         0)

StagePoolToWallet ==
  \E actor \in Actors:
    /\ committed.pool[TargetAsset] > 0
    /\ committed.wallet[TargetAsset][actor] < MaxSupply
    /\ StageCandidate(
         "pool_to_wallet",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.pool[TargetAsset] = @ - 1,
           !.wallet[TargetAsset][actor] = @ + 1],
         0)

StageWalletToPerps ==
  \E actor \in Actors:
    /\ committed.wallet[TargetAsset][actor] > 0
    /\ committed.perps[TargetAsset] < MaxSupply
    /\ StageCandidate(
         "wallet_to_perps",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.wallet[TargetAsset][actor] = @ - 1,
           !.perps[TargetAsset] = @ + 1],
         0)

StagePerpsToWallet ==
  \E actor \in Actors:
    /\ committed.perps[TargetAsset] > 0
    /\ committed.wallet[TargetAsset][actor] < MaxSupply
    /\ StageCandidate(
         "perps_to_wallet",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.perps[TargetAsset] = @ - 1,
           !.wallet[TargetAsset][actor] = @ + 1],
         0)

StageWalletToPendingStake ==
  \E actor \in Actors:
    /\ committed.wallet[TargetAsset][actor] > 0
    /\ committed.pendingStake[TargetAsset] < MaxSupply
    /\ StageCandidate(
         "wallet_to_pending_stake",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.wallet[TargetAsset][actor] = @ - 1,
           !.pendingStake[TargetAsset] = @ + 1],
         0)

StageActivateStake ==
  \E actor \in Actors:
    /\ committed.pendingStake[TargetAsset] > 0
    /\ committed.activeStake[TargetAsset] < MaxSupply
    /\ StageCandidate(
         "activate_stake",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.pendingStake[TargetAsset] = @ - 1,
           !.activeStake[TargetAsset] = @ + 1],
         0)

StageUnstake ==
  \E actor \in Actors:
    /\ committed.activeStake[TargetAsset] > 0
    /\ committed.wallet[TargetAsset][actor] < MaxSupply
    /\ StageCandidate(
         "unstake",
         TargetAsset,
         actor,
         [committed EXCEPT
           !.activeStake[TargetAsset] = @ - 1,
           !.wallet[TargetAsset][actor] = @ + 1],
         0)

StageInvalidProjection ==
  /\ committed.supply[TargetAsset] < MaxSupply
    /\ StageCandidate(
         "invalid_projection",
         TargetAsset,
         TargetMintActor,
         [committed EXCEPT !.supply[TargetAsset] = @ + 1],
         0)

StageLateBatchFailure ==
  \E recipient \in Actors:
    /\ committed.mintAuthority[TargetAsset] = TargetMintActor
    /\ committed.supply[TargetAsset] + 2 <= MaxSupply
    /\ committed.wallet[TargetAsset][recipient] < MaxSupply
    /\ committed.nonce[TargetMintActor] + 2 <= MaxNonce
    /\ StageCandidate(
         "late_batch_failure",
         TargetAsset,
         TargetMintActor,
         [committed EXCEPT
           !.supply[TargetAsset] = @ + 2,
           !.wallet[TargetAsset][recipient] = @ + 1,
           !.nonce[TargetMintActor] = @ + 2],
         2)

CommitStaged ==
  /\ phase = "staged"
  /\ AccountingOK(staged)
  /\ RegistryOK(staged)
  /\ committed' = staged
  /\ staged' = staged
  /\ snapshot' = snapshot
  /\ phase' = "idle"
  /\ lastAction' = lastAction
  /\ lastOutcome' = "committed"
  /\ lastAsset' = lastAsset
  /\ lastActor' = lastActor
  /\ stagedTokenOps' = stagedTokenOps
  /\ lastTokenOps' = stagedTokenOps

RejectStaged ==
  /\ phase = "staged"
  /\ (~AccountingOK(staged) \/ ~RegistryOK(staged))
  /\ committed' = committed
  /\ staged' = staged
  /\ snapshot' = snapshot
  /\ phase' = "idle"
  /\ lastAction' = lastAction
  /\ lastOutcome' = "reject_staged"
  /\ lastAsset' = lastAsset
  /\ lastActor' = lastActor
  /\ stagedTokenOps' = stagedTokenOps
  /\ lastTokenOps' = 0

ImmediateReject(kind, outcome, asset, actor) ==
  /\ phase = "idle"
  /\ committed' = committed
  /\ staged' = committed
  /\ snapshot' = committed
  /\ phase' = "idle"
  /\ lastAction' = kind
  /\ lastOutcome' = outcome
  /\ lastAsset' = asset
  /\ lastActor' = actor
  /\ stagedTokenOps' = 0
  /\ lastTokenOps' = 0

RejectUnauthorizedMint ==
  /\ committed.mintAuthority[TargetAsset] # ActorB
  /\ ImmediateReject(
       "unauthorized_mint", "reject_authority", TargetAsset, ActorB)

RejectUnregisteredAsset ==
  ImmediateReject(
    "unregistered_asset", "reject_unregistered", UnknownAsset, ActorA)

RejectOverflowMint ==
  /\ committed.mintAuthority[TargetAsset] = TargetMintActor
  /\ committed.supply[TargetAsset] = MaxSupply
  /\ ImmediateReject(
       "overflow_mint", "reject_bounds", TargetAsset, TargetMintActor)

RejectUnderflowBurn ==
  \E actor \in Actors:
    /\ committed.wallet[TargetAsset][actor] = 0
    /\ ImmediateReject(
         "underflow_burn", "reject_bounds", TargetAsset, actor)

RejectSelfTransfer ==
  \E actor \in Actors:
    ImmediateReject("self_transfer", "reject_self", TargetAsset, actor)

RejectNonceExhausted ==
  \E actor \in Actors:
    /\ committed.nonce[actor] = MaxNonce
    /\ ImmediateReject(
         "nonce_exhausted", "reject_nonce", TargetAsset, actor)

ResolveStage == CommitStaged \/ RejectStaged

Next ==
  \/ StageMint
  \/ StageFaucetMint
  \/ StageTwoMints
  \/ StageBurn
  \/ StageTransfer
  \/ StageWalletToPool
  \/ StagePoolToWallet
  \/ StageWalletToPerps
  \/ StagePerpsToWallet
  \/ StageWalletToPendingStake
  \/ StageActivateStake
  \/ StageUnstake
  \/ StageInvalidProjection
  \/ StageLateBatchFailure
  \/ ResolveStage
  \/ RejectUnauthorizedMint
  \/ RejectUnregisteredAsset
  \/ RejectOverflowMint
  \/ RejectUnderflowBurn
  \/ RejectSelfTransfer
  \/ RejectNonceExhausted

Spec == Init /\ [][Next]_vars /\ WF_vars(ResolveStage)

CommittedAccountingOK == AccountingOK(committed)

CommittedRegistryOK == RegistryOK(committed)

StagingDoesNotChangeCommittedState ==
  (phase = "staged") => (committed = snapshot)

RejectedOperationIsExactNoOp ==
  (lastOutcome \in {
     "reject_staged", "reject_authority", "reject_unregistered",
     "reject_bounds", "reject_self", "reject_nonce"
   }) => (committed = snapshot)

UnauthorizedMintIsExactNoOp ==
  (lastOutcome = "reject_authority") => (committed = snapshot)

UnregisteredAssetIsExactNoOp ==
  (lastOutcome = "reject_unregistered") => (committed = snapshot)

CommittedTokenNonceDeltaIsExact ==
  (lastOutcome = "committed") =>
    committed.nonce[lastActor] =
      snapshot.nonce[lastActor] + lastTokenOps

OtherActorNonceIsStable ==
  (lastOutcome = "committed") =>
    IF lastActor = ActorA
      THEN committed.nonce[ActorB] = snapshot.nonce[ActorB]
      ELSE committed.nonce[ActorA] = snapshot.nonce[ActorA]

OtherAssetIsStable ==
  (lastOutcome = "committed") =>
    IF lastAsset = AssetA
      THEN AssetProjection(committed, AssetB) =
             AssetProjection(snapshot, AssetB)
      ELSE AssetProjection(committed, AssetA) =
             AssetProjection(snapshot, AssetA)

AcceptedSupplyDeltaIsExact ==
  (lastOutcome = "committed") =>
    IF lastAction \in {"mint", "faucet_mint"}
      THEN committed.supply[lastAsset] = snapshot.supply[lastAsset] + 1
    ELSE IF lastAction = "two_mints"
      THEN committed.supply[lastAsset] = snapshot.supply[lastAsset] + 2
    ELSE IF lastAction = "burn"
      THEN committed.supply[lastAsset] + 1 = snapshot.supply[lastAsset]
    ELSE committed.supply[lastAsset] = snapshot.supply[lastAsset]

InvalidProjectionCannotCommit ==
  (lastAction \in {"invalid_projection", "late_batch_failure"}
    /\ lastOutcome = "committed") => FALSE

RejectedStageFailsValidation ==
  (lastOutcome = "reject_staged") =>
    (~AccountingOK(staged) \/ ~RegistryOK(staged))

NonceExhaustionDoesNotWrap ==
  (lastOutcome = "reject_nonce") =>
    /\ committed = snapshot
    /\ committed.nonce[lastActor] = MaxNonce

StagedOperationEventuallyResolves ==
  (phase = "staged") ~> (phase = "idle")

====
