import Mathlib

/-!
# ZenoProof Market Math

This file formalizes the narrow proof-market claim that ZenoDEX/ZenoProof can
safely make today.

The existing runtime surface supports a primary proof-demand market shape:
posted demand plus escrowed reward, verified proof supply, canonical work
identity, and first-valid settlement. A full secondary exchange where users
buy and sell transferable proof receipts needs extra receipt-transfer rules
outside this file.

These theorems do not prove legal compliance, verifier soundness,
cryptographic security, proof availability, market liquidity, or truth of a
mathematical statement without an explicit verifier-soundness assumption.
-/

namespace Proofs
namespace ZenoProofMarket

/-! ## Work identity -/

structure ProofWork where
  statementRoot : Nat
  assumptionRoot : Nat
  inputRoot : Nat
  outputRoot : Nat
  publicResultRoot : Nat
  deriving DecidableEq, Repr

def sameWork (a b : ProofWork) : Prop :=
  a.statementRoot = b.statementRoot ∧
    a.assumptionRoot = b.assumptionRoot ∧
    a.inputRoot = b.inputRoot ∧
    a.outputRoot = b.outputRoot ∧
    a.publicResultRoot = b.publicResultRoot

def canonicalizes (canon : ProofWork → Nat) : Prop :=
  ∀ a b, sameWork a b → canon a = canon b

def settleWork (canon : ProofWork → Nat) (work : ProofWork)
    (consumed : Finset Nat) : Bool × Finset Nat :=
  let claimId := canon work
  if claimId ∈ consumed then
    (false, consumed)
  else
    (true, consumed ∪ {claimId})

theorem same_work_settles_once_under_canonicalizer
    (canon : ProofWork → Nat)
    (hCanon : canonicalizes canon)
    (consumed : Finset Nat) (a b : ProofWork)
    (hFresh : canon a ∉ consumed)
    (hSame : sameWork a b) :
    (settleWork canon b (settleWork canon a consumed).2).1 = false := by
  have hEq : canon b = canon a := (hCanon a b hSame).symm
  have hMem : canon b ∈ consumed ∪ {canon a} := by
    rw [hEq]
    exact Finset.mem_union_right consumed (Finset.mem_singleton_self (canon a))
  have hCond : canon b = canon a ∨ canon b ∈ consumed := Or.inl hEq
  simp [settleWork, hFresh, hCond]

structure ProofArtifact where
  work : ProofWork
  rawDigest : Nat
  nonce : Nat
  auxData : Nat
  deriving DecidableEq, Repr

theorem raw_digest_inequality_is_not_work_uniqueness :
    ∃ a b : ProofArtifact, a ≠ b ∧ sameWork a.work b.work := by
  refine ⟨
    ⟨⟨1, 2, 3, 4, 5⟩, 10, 0, 0⟩,
    ⟨⟨1, 2, 3, 4, 5⟩, 11, 1, 99⟩,
    ?_, ?_⟩
  · decide
  · simp [sameWork]

/-! ## Demand, supply, and settlement -/

inductive FlowKind where
  | protocolBounty
  | postedBuyOrder
  | secondaryResale
  deriving DecidableEq, Repr

def FlowKind.isPrimaryDemand : FlowKind → Prop
  | .protocolBounty => True
  | .postedBuyOrder => True
  | .secondaryResale => False

def FlowKind.isSecondaryResale : FlowKind → Prop
  | .secondaryResale => True
  | _ => False

theorem protocol_bounty_is_primary_not_secondary :
    FlowKind.isPrimaryDemand .protocolBounty ∧
      ¬ FlowKind.isSecondaryResale .protocolBounty := by
  simp [FlowKind.isPrimaryDemand, FlowKind.isSecondaryResale]

structure BuyOrder where
  buyerId : Nat
  work : ProofWork
  maxPayment : Nat
  escrow : Nat
  expiryEpoch : Nat
  isOpen : Bool
  sourceVerified : Bool
  sourceBounded : Bool
  noPassiveYield : Bool
  noProfitShare : Bool
  noFutureEntrant : Bool
  disclosureMet : Bool
  deriving DecidableEq, Repr

structure BuyOrderAdmitted (order : BuyOrder) : Prop where
  openOk : order.isOpen = true
  sourceVerified : order.sourceVerified = true
  sourceBounded : order.sourceBounded = true
  noPassiveYield : order.noPassiveYield = true
  noProfitShare : order.noProfitShare = true
  noFutureEntrant : order.noFutureEntrant = true
  disclosureMet : order.disclosureMet = true
  maxPaymentEscrowed : order.maxPayment ≤ order.escrow

structure ProofOffer where
  sellerId : Nat
  work : ProofWork
  askPrice : Nat
  verified : Bool
  bindingOk : Bool
  policyOk : Bool
  nonceOk : Bool
  verifierAdmitted : Bool
  deriving DecidableEq, Repr

structure ProofOfferAccepted (offer : ProofOffer) : Prop where
  verified : offer.verified = true
  bindingOk : offer.bindingOk = true
  policyOk : offer.policyOk = true
  nonceOk : offer.nonceOk = true
  verifierAdmitted : offer.verifierAdmitted = true

structure SettlementCert where
  flow : FlowKind
  order : BuyOrder
  offer : ProofOffer
  canon : ProofWork → Nat
  canonicalId : Nat
  price : Nat
  escrowBefore : Nat
  escrowAfter : Nat
  sellerCreditBefore : Nat
  sellerCreditAfter : Nat
  consumedBefore : Finset Nat
  consumedAfter : Finset Nat
  nowEpoch : Nat
  hOrder : BuyOrderAdmitted order
  hOffer : ProofOfferAccepted offer
  hWorkMatch : sameWork order.work offer.work
  hPriceAtLeastAsk : offer.askPrice ≤ price
  hPriceAtMostMax : price ≤ order.maxPayment
  hEscrowBefore : escrowBefore = order.escrow
  hEscrowDelta : escrowAfter + price = escrowBefore
  hSellerDelta : sellerCreditAfter = sellerCreditBefore + price
  hFresh : nowEpoch ≤ order.expiryEpoch
  hCanonical : canon offer.work = canonicalId
  hUnconsumed : canonicalId ∉ consumedBefore
  hConsumedAfter : consumedAfter = consumedBefore ∪ {canonicalId}

theorem settled_trade_implies_verified_bound_and_source_safe
    (cert : SettlementCert) :
    cert.offer.verified = true ∧
      cert.offer.bindingOk = true ∧
      cert.offer.policyOk = true ∧
      cert.offer.verifierAdmitted = true ∧
      cert.order.sourceVerified = true ∧
      cert.order.sourceBounded = true ∧
      cert.order.noPassiveYield = true ∧
      cert.order.noProfitShare = true ∧
      cert.order.noFutureEntrant = true ∧
      cert.price ≤ cert.order.escrow ∧
      cert.price ≤ cert.escrowBefore ∧
      cert.escrowAfter ≤ cert.escrowBefore ∧
      cert.sellerCreditAfter = cert.sellerCreditBefore + cert.price := by
  have hPriceEscrow : cert.price ≤ cert.order.escrow :=
    le_trans cert.hPriceAtMostMax cert.hOrder.maxPaymentEscrowed
  have hPriceEscrowBefore : cert.price ≤ cert.escrowBefore := by
    rw [cert.hEscrowBefore]
    exact hPriceEscrow
  have hEscrowAfterLe : cert.escrowAfter ≤ cert.escrowBefore := by
    have hDelta := cert.hEscrowDelta
    omega
  exact ⟨cert.hOffer.verified, cert.hOffer.bindingOk, cert.hOffer.policyOk,
    cert.hOffer.verifierAdmitted, cert.hOrder.sourceVerified,
    cert.hOrder.sourceBounded, cert.hOrder.noPassiveYield,
    cert.hOrder.noProfitShare, cert.hOrder.noFutureEntrant, hPriceEscrow,
    hPriceEscrowBefore, hEscrowAfterLe, cert.hSellerDelta⟩

theorem unverified_offer_not_settled
    (order : BuyOrder) (offer : ProofOffer)
    (hBad : offer.verified = false) :
    ¬ ∃ cert : SettlementCert, cert.order = order ∧ cert.offer = offer := by
  intro h
  rcases h with ⟨cert, hOrderEq, hOfferEq⟩
  subst hOrderEq
  subst hOfferEq
  rw [cert.hOffer.verified] at hBad
  contradiction

theorem binding_bad_offer_not_settled
    (order : BuyOrder) (offer : ProofOffer)
    (hBad : offer.bindingOk = false) :
    ¬ ∃ cert : SettlementCert, cert.order = order ∧ cert.offer = offer := by
  intro h
  rcases h with ⟨cert, hOrderEq, hOfferEq⟩
  subst hOrderEq
  subst hOfferEq
  rw [cert.hOffer.bindingOk] at hBad
  contradiction

theorem over_escrow_price_not_settled
    (order : BuyOrder) (price : Nat)
    (hOver : order.escrow < price) :
    ¬ ∃ cert : SettlementCert, cert.order = order ∧ cert.price = price := by
  intro h
  rcases h with ⟨cert, hOrderEq, hPriceEq⟩
  subst hOrderEq
  subst hPriceEq
  have hPriceEscrow : cert.price ≤ cert.order.escrow :=
    le_trans cert.hPriceAtMostMax cert.hOrder.maxPaymentEscrowed
  omega

theorem stale_order_not_settled
    (order : BuyOrder) (nowEpoch : Nat)
    (hStale : order.expiryEpoch < nowEpoch) :
    ¬ ∃ cert : SettlementCert, cert.order = order ∧ cert.nowEpoch = nowEpoch := by
  intro h
  rcases h with ⟨cert, hOrderEq, hNowEq⟩
  subst hOrderEq
  subst hNowEq
  have hFresh := cert.hFresh
  omega

theorem settled_work_marked_consumed (cert : SettlementCert) :
    cert.canonicalId ∈ cert.consumedAfter := by
  rw [cert.hConsumedAfter]
  exact Finset.mem_union_right cert.consumedBefore
    (Finset.mem_singleton_self cert.canonicalId)

theorem settled_trade_truth_requires_verifier_soundness
    (Truth : ProofWork → Prop)
    (cert : SettlementCert)
    (hSound : ∀ offer : ProofOffer, ProofOfferAccepted offer → Truth offer.work) :
    Truth cert.offer.work :=
  hSound cert.offer cert.hOffer

/-! ## Non-vacuity witnesses -/

def exampleWork : ProofWork :=
  ⟨11, 22, 33, 44, 55⟩

def workCanonicalId (work : ProofWork) : Nat :=
  work.statementRoot

theorem workCanonicalId_canonicalizes : canonicalizes workCanonicalId := by
  intro a b hSame
  exact hSame.1

def exampleSafeOrder : BuyOrder where
  buyerId := 1001
  work := exampleWork
  maxPayment := 7
  escrow := 10
  expiryEpoch := 99
  isOpen := true
  sourceVerified := true
  sourceBounded := true
  noPassiveYield := true
  noProfitShare := true
  noFutureEntrant := true
  disclosureMet := true

theorem exampleSafeOrder_admitted :
    BuyOrderAdmitted exampleSafeOrder := by
  constructor <;> norm_num [exampleSafeOrder]

def exampleSafeOffer : ProofOffer where
  sellerId := 2002
  work := exampleWork
  askPrice := 6
  verified := true
  bindingOk := true
  policyOk := true
  nonceOk := true
  verifierAdmitted := true

theorem exampleSafeOffer_accepted :
    ProofOfferAccepted exampleSafeOffer := by
  constructor <;> norm_num [exampleSafeOffer]

def exampleSettlementCert : SettlementCert where
  flow := .postedBuyOrder
  order := exampleSafeOrder
  offer := exampleSafeOffer
  canon := workCanonicalId
  canonicalId := 11
  price := 7
  escrowBefore := 10
  escrowAfter := 3
  sellerCreditBefore := 5
  sellerCreditAfter := 12
  consumedBefore := ∅
  consumedAfter := {11}
  nowEpoch := 42
  hOrder := exampleSafeOrder_admitted
  hOffer := exampleSafeOffer_accepted
  hWorkMatch := by
    norm_num [exampleSafeOrder, exampleSafeOffer, exampleWork, sameWork]
  hPriceAtLeastAsk := by norm_num [exampleSafeOffer]
  hPriceAtMostMax := by norm_num [exampleSafeOrder]
  hEscrowBefore := by norm_num [exampleSafeOrder]
  hEscrowDelta := by norm_num
  hSellerDelta := by norm_num
  hFresh := by norm_num [exampleSafeOrder]
  hCanonical := by norm_num [workCanonicalId, exampleSafeOffer, exampleWork]
  hUnconsumed := by simp
  hConsumedAfter := by simp

theorem settlement_certificate_assumptions_nonvacuous :
    ∃ cert : SettlementCert,
      cert.flow = .postedBuyOrder ∧
        cert.order = exampleSafeOrder ∧
        cert.offer = exampleSafeOffer ∧
        cert.price = 7 ∧
        cert.escrowBefore = 10 ∧
        cert.escrowAfter = 3 ∧
        cert.sellerCreditBefore = 5 ∧
        cert.sellerCreditAfter = 12 ∧
        cert.canonicalId ∈ cert.consumedAfter := by
  refine ⟨exampleSettlementCert, ?_⟩
  simp [exampleSettlementCert]

theorem accepted_settlement_contract_nonvacuous :
    ∃ cert : SettlementCert,
      cert.offer.verified = true ∧
        cert.offer.bindingOk = true ∧
        cert.offer.policyOk = true ∧
        cert.offer.verifierAdmitted = true ∧
        cert.order.sourceVerified = true ∧
        cert.order.sourceBounded = true ∧
        cert.order.noPassiveYield = true ∧
        cert.order.noProfitShare = true ∧
        cert.order.noFutureEntrant = true ∧
        cert.price ≤ cert.order.escrow ∧
        cert.price ≤ cert.escrowBefore ∧
        cert.escrowAfter ≤ cert.escrowBefore ∧
        cert.sellerCreditAfter = cert.sellerCreditBefore + cert.price := by
  exact ⟨exampleSettlementCert,
    settled_trade_implies_verified_bound_and_source_safe exampleSettlementCert⟩

theorem concrete_same_work_duplicate_rejected :
    (settleWork workCanonicalId exampleSafeOffer.work
      (settleWork workCanonicalId exampleSafeOrder.work ∅).2).1 = false := by
  exact same_work_settles_once_under_canonicalizer workCanonicalId
    workCanonicalId_canonicalizes ∅ exampleSafeOrder.work exampleSafeOffer.work
    (by simp [workCanonicalId, exampleSafeOrder, exampleWork])
    (by norm_num [exampleSafeOrder, exampleSafeOffer, exampleWork, sameWork])

/-! ## Secondary-market boundary -/

structure ProofMarketState where
  postedDemand : Bool
  escrowedBudget : Bool
  verifiedSupply : Bool
  canonicalConsumedSet : Bool
  settlementGate : Bool
  transferableReceipts : Bool
  deriving DecidableEq, Repr

structure PrimaryProofMarketExists (state : ProofMarketState) : Prop where
  postedDemand : state.postedDemand = true
  escrowedBudget : state.escrowedBudget = true
  verifiedSupply : state.verifiedSupply = true
  canonicalConsumedSet : state.canonicalConsumedSet = true
  settlementGate : state.settlementGate = true

structure FullProofExchangeExists (state : ProofMarketState) : Prop where
  primary : PrimaryProofMarketExists state
  transferableReceipts : state.transferableReceipts = true

def canMonetizeVerifiedProofWork (state : ProofMarketState) : Prop :=
  PrimaryProofMarketExists state

def canHostUserToUserProofResale (state : ProofMarketState) : Prop :=
  FullProofExchangeExists state

theorem full_exchange_implies_primary_market
    (state : ProofMarketState)
    (h : FullProofExchangeExists state) :
    PrimaryProofMarketExists state :=
  h.primary

theorem full_exchange_requires_transferable_receipts
    (state : ProofMarketState)
    (h : FullProofExchangeExists state) :
    state.transferableReceipts = true :=
  h.transferableReceipts

theorem full_exchange_iff_primary_and_transferable
    (state : ProofMarketState) :
    FullProofExchangeExists state ↔
      PrimaryProofMarketExists state ∧ state.transferableReceipts = true := by
  constructor
  · intro h
    exact ⟨h.primary, h.transferableReceipts⟩
  · intro h
    exact ⟨h.1, h.2⟩

theorem primary_market_does_not_imply_secondary_exchange
    (state : ProofMarketState)
    (hNoReceipts : state.transferableReceipts = false) :
    ¬ FullProofExchangeExists state := by
  intro h
  rw [h.transferableReceipts] at hNoReceipts
  contradiction

theorem monetization_does_not_imply_user_to_user_resale
    (state : ProofMarketState)
    (hNoReceipts : state.transferableReceipts = false) :
    canMonetizeVerifiedProofWork state →
      ¬ canHostUserToUserProofResale state := by
  intro _hPrimary
  exact primary_market_does_not_imply_secondary_exchange state hNoReceipts

theorem proof_mining_shape_is_primary_when_gates_exist
    (state : ProofMarketState)
    (hDemand : state.postedDemand = true)
    (hEscrow : state.escrowedBudget = true)
    (hSupply : state.verifiedSupply = true)
    (hConsumed : state.canonicalConsumedSet = true)
    (hSettlement : state.settlementGate = true) :
    PrimaryProofMarketExists state :=
  ⟨hDemand, hEscrow, hSupply, hConsumed, hSettlement⟩

def examplePrimaryOnlyState : ProofMarketState where
  postedDemand := true
  escrowedBudget := true
  verifiedSupply := true
  canonicalConsumedSet := true
  settlementGate := true
  transferableReceipts := false

def exampleFullExchangeState : ProofMarketState where
  postedDemand := true
  escrowedBudget := true
  verifiedSupply := true
  canonicalConsumedSet := true
  settlementGate := true
  transferableReceipts := true

theorem primary_market_without_secondary_exchange_nonvacuous :
    PrimaryProofMarketExists examplePrimaryOnlyState ∧
      ¬ FullProofExchangeExists examplePrimaryOnlyState := by
  constructor
  · exact proof_mining_shape_is_primary_when_gates_exist examplePrimaryOnlyState
      rfl rfl rfl rfl rfl
  · exact primary_market_does_not_imply_secondary_exchange
      examplePrimaryOnlyState rfl

theorem full_exchange_nonvacuous :
    FullProofExchangeExists exampleFullExchangeState := by
  constructor
  · exact proof_mining_shape_is_primary_when_gates_exist exampleFullExchangeState
      rfl rfl rfl rfl rfl
  · rfl

end ZenoProofMarket
end Proofs
