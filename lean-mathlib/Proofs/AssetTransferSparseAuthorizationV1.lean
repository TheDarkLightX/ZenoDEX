import Proofs.AssetTransferSparseTraceV1

/-!
Authorization and frame properties of the actual sparse selected-policy step.
Amounts are observed in finite `amountAt` rows; the debit conclusion follows
from the constructed balance equation and the leaf's sender/context guard.
No output representation, verified result, or principal enumeration is assumed.

The only extra numerical premises are nonnegative command amount and selected
fee. The abstraction's zero-amount guard only excludes zero, so acceptance does
not derive the amount lower bound. Its fee width guard also admits negative
integers. The compact controls below retain both missing-premise examples.
Runtime constructors enforce these lower bounds; these are model-premise
counterexamples and do not establish runtime defects.

Context/command-signature authentication, policy membership and profile
selection, metadata/height/replay admission, complete effect plans, publication,
and universal runtime/compiler refinement remain outside these statements.
Histories retain the existing fixed release and selected policy configuration.
-/
namespace Proofs.AssetTransferSparseAuthorizationV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace S
export Proofs.AssetTransferSparseTablesV1 (Input step localState accounts
  Unique PositiveAccounts CanonicalBalances accepted_balance_equation
  accepted_sparse_transfer accepted_sender_is_context rejected_step_noop demo
  demo_source demo_deletes_zero_and_frames_other_asset)
end S
namespace T
export Proofs.AssetTransferRefinementV1 (TransferState Command delta indicator
  delta_untouched)
end T
namespace H
export Proofs.AssetTransferSparseTraceV1 (Config Request inputFor run)
end H

attribute [local instance] lexOrd

/-- Non-sender roles receive only the two nonnegative credits, including aliases. -/
theorem delta_non_sender_nonnegative {pre : T.TransferState} {cmd : T.Command}
    (amountNonnegative : 0 ≤ cmd.amountAtoms)
    (feeNonnegative : 0 ≤ pre.policy.transferFeeAtoms) {owner : String}
    (notSender : owner ≠ cmd.sender) : 0 ≤ T.delta pre cmd owner := by
  simp only [T.delta, T.indicator, if_neg notSender, Int.zero_add]
  split <;> split <;> omega

/-- An accepted step cannot reduce any other owner's amount at any denomination. -/
theorem accepted_non_sender_nondecreasing {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances)
    (amountNonnegative : 0 ≤ input.command.amountAtoms)
    (feeNonnegative : 0 ≤ input.policy.transferFeeAtoms)
    (accepted : (S.step input).verdict = .accepted) (owner asset domain : String)
    (notSender : owner ≠ input.command.sender) :
    amountAt input.pre.balances owner asset domain ≤
      amountAt (S.step input).post.balances owner asset domain := by
  have equation := S.accepted_balance_equation canonical.1 canonical.2.1
    accepted owner asset domain
  have credit := delta_non_sender_nonnegative (pre := S.localState input)
    amountNonnegative feeNonnegative notSender
  split at equation <;> omega

/-- A strict debit identifies both the declared sender and its accepted context. -/
theorem accepted_decrease_authorized {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances)
    (amountNonnegative : 0 ≤ input.command.amountAtoms)
    (feeNonnegative : 0 ≤ input.policy.transferFeeAtoms)
    (accepted : (S.step input).verdict = .accepted) {owner asset domain : String}
    (decreased : amountAt (S.step input).post.balances owner asset domain <
      amountAt input.pre.balances owner asset domain) :
    owner = input.command.sender ∧ input.command.sender = input.context.subjectId ∧
      input.command.asset = asset ∧ S.accounts = domain := by
  have sender : owner = input.command.sender := by
    by_cases same : owner = input.command.sender
    · exact same
    · have monotone := accepted_non_sender_nondecreasing canonical amountNonnegative
        feeNonnegative accepted owner asset domain same
      omega
  have equation := S.accepted_balance_equation canonical.1 canonical.2.1
    accepted owner asset domain
  have location : input.command.asset = asset ∧ S.accounts = domain := by
    by_cases same : input.command.asset = asset ∧ S.accounts = domain
    · exact same
    · rw [if_neg same] at equation
      omega
  exact ⟨sender, S.accepted_sender_is_context accepted, location⟩

/-- Foreign assets, foreign domains, and owners outside every transfer role are framed.
The conclusion includes rejected attempts and needs no amount or fee sign premise. -/
theorem step_outside_frame {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances) (owner asset domain : String)
    (outside : input.command.asset ≠ asset ∨ S.accounts ≠ domain ∨
      (owner ≠ input.command.sender ∧ owner ≠ input.command.recipient ∧
        owner ≠ input.policy.feeOwner)) :
    amountAt (S.step input).post.balances owner asset domain =
      amountAt input.pre.balances owner asset domain := by
  cases verdict : (S.step input).verdict with
  | rejected code => rw [(S.rejected_step_noop verdict).1]
  | accepted =>
      have equation := S.accepted_balance_equation canonical.1 canonical.2.1
        verdict owner asset domain
      rcases outside with foreignAsset | foreignDomain | outsideRoles
      · have location : ¬(input.command.asset = asset ∧ S.accounts = domain) :=
          fun h => foreignAsset h.1
        rw [if_neg location] at equation
        omega
      · have location : ¬(input.command.asset = asset ∧ S.accounts = domain) :=
          fun h => foreignDomain h.2
        rw [if_neg location] at equation
        omega
      · have zero := T.delta_untouched (pre := S.localState input)
          outsideRoles.1 outsideRoles.2.1 outsideRoles.2.2
        rw [zero] at equation
        split at equation <;> omega

/-- Endpoint decrease witnesses an actually accepted debit after its executed prefix.
Rejected attempts remain in the request prefix and are omitted by `H.run` itself. -/
theorem history_decrease_has_accepted_sender (config : H.Config)
    (requests : List H.Request) (pre : GlobalState)
    (canonical : S.CanonicalBalances pre.balances)
    (feeNonnegative : 0 ≤ config.policy.transferFeeAtoms)
    (amountsNonnegative : ∀ request ∈ requests, 0 ≤ request.command.amountAtoms)
    {owner asset domain : String}
    (decreased : amountAt (H.run config requests pre).post.balances owner asset domain <
      amountAt pre.balances owner asset domain) :
    ∃ beforeRequests request suffix,
      requests = beforeRequests ++ request :: suffix ∧
      (S.step (H.inputFor config request (H.run config beforeRequests pre).post)).verdict = .accepted ∧
      owner = request.command.sender ∧ request.command.sender = request.context.subjectId ∧
      request.command.asset = asset ∧ S.accounts = domain ∧
      amountAt (S.step (H.inputFor config request (H.run config beforeRequests pre).post)).post.balances
        owner asset domain < amountAt (H.run config beforeRequests pre).post.balances owner asset domain := by
  induction requests generalizing pre with
  | nil =>
      simp only [H.run] at decreased
      omega
  | cons request requests ih =>
      have tailAmounts : ∀ r ∈ requests, 0 ≤ r.command.amountAtoms :=
        fun r member => amountsNonnegative r (List.mem_cons_of_mem request member)
      cases verdict : (S.step (H.inputFor config request pre)).verdict with
      | rejected code =>
          have tailDecrease : amountAt (H.run config requests pre).post.balances owner asset domain <
              amountAt pre.balances owner asset domain := by
            simpa only [H.run, verdict] using decreased
          obtain ⟨beforeRequests, found, suffix, shape, witness⟩ :=
            ih pre canonical tailAmounts tailDecrease
          refine ⟨request :: beforeRequests, found, suffix, ?_, ?_⟩
          · exact congrArg (List.cons request) shape
          · simpa only [H.run, verdict] using witness
      | accepted =>
          by_cases directDecrease :
              amountAt (S.step (H.inputFor config request pre)).post.balances owner asset domain <
                amountAt pre.balances owner asset domain
          · have authorization := accepted_decrease_authorized canonical
              (amountsNonnegative request (List.mem_cons_self ..)) feeNonnegative verdict directDecrease
            exact ⟨[], request, requests, rfl, verdict, authorization.1, authorization.2.1,
              authorization.2.2.1, authorization.2.2.2, directDecrease⟩
          · have nextCanonical :=
              (S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict).2.2.1
            have tailDecrease :
                amountAt (H.run config requests (S.step (H.inputFor config request pre)).post).post.balances
                  owner asset domain <
                amountAt (S.step (H.inputFor config request pre)).post.balances owner asset domain := by
              simp only [H.run, verdict] at decreased
              omega
            obtain ⟨beforeRequests, found, suffix, shape, witness⟩ :=
              ih (S.step (H.inputFor config request pre)).post nextCanonical tailAmounts tailDecrease
            refine ⟨request :: beforeRequests, found, suffix, ?_, ?_⟩
            · exact congrArg (List.cons request) shape
            · simpa only [H.run, verdict] using witness

/-- Every endpoint debit identifies a request whose accepted context declared that owner. -/
theorem history_decrease_has_declared_subject (config : H.Config)
    (requests : List H.Request) (pre : GlobalState)
    (canonical : S.CanonicalBalances pre.balances)
    (feeNonnegative : 0 ≤ config.policy.transferFeeAtoms)
    (amountsNonnegative : ∀ request ∈ requests, 0 ≤ request.command.amountAtoms)
    {owner asset domain : String}
    (decreased : amountAt (H.run config requests pre).post.balances owner asset domain <
      amountAt pre.balances owner asset domain) :
    ∃ request ∈ requests, owner = request.context.subjectId := by
  obtain ⟨beforeRequests, request, suffix, shape, _, sender, subject, _, _, _⟩ :=
    history_decrease_has_accepted_sender config requests pre canonical feeNonnegative
      amountsNonnegative decreased
  refine ⟨request, ?_, sender.trans subject⟩
  rw [shape]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))

/-- The existing zero-deleting sparse example satisfies every debit premise. -/
theorem demo_authorized_debit :
    S.CanonicalBalances S.demo.pre.balances ∧
    0 ≤ S.demo.command.amountAtoms ∧ 0 ≤ S.demo.policy.transferFeeAtoms ∧
    (S.step S.demo).verdict = .accepted ∧
    amountAt (S.step S.demo).post.balances "alice" "USD" S.accounts <
      amountAt S.demo.pre.balances "alice" "USD" S.accounts := by
  refine ⟨⟨S.demo_source.1, S.demo_source.2, by decide, by decide⟩,
    by decide, by decide, S.demo_deletes_zero_and_frames_other_asset.1, ?_⟩
  rw [S.demo_deletes_zero_and_frames_other_asset.2]
  decide

def demoConfig : H.Config := ⟨S.demo.moduleReleaseId, S.demo.policy⟩
def rejectedDemoRequest : H.Request :=
  ⟨{ S.demo.context with subjectId := "mallory" }, S.demo.command⟩
def acceptedDemoRequest : H.Request := ⟨S.demo.context, S.demo.command⟩

/-- A rejection in the executed prefix leaves a later accepted debit reachable. -/
theorem demo_rejected_then_accepted_debit :
    (S.step (H.inputFor demoConfig rejectedDemoRequest S.demo.pre)).verdict =
      .rejected .unauthorizedSubject ∧
    (S.step (H.inputFor demoConfig acceptedDemoRequest
      (H.run demoConfig [rejectedDemoRequest] S.demo.pre).post)).verdict = .accepted ∧
    amountAt (H.run demoConfig [rejectedDemoRequest, acceptedDemoRequest]
      S.demo.pre).post.balances "alice" "USD" S.accounts <
      amountAt S.demo.pre.balances "alice" "USD" S.accounts := by
  have rejected : (S.step (H.inputFor demoConfig rejectedDemoRequest S.demo.pre)).verdict =
      .rejected .unauthorizedSubject := by decide
  have accepted : (S.step (H.inputFor demoConfig acceptedDemoRequest S.demo.pre)).verdict =
      .accepted := S.demo_deletes_zero_and_frames_other_asset.1
  refine ⟨rejected, ?_, ?_⟩
  · simpa only [H.run, rejected] using accepted
  · simpa only [H.run, rejected, accepted] using demo_authorized_debit.2.2.2.2

/-- Dropping the command lower bound admits a reversed one-atom model transfer. -/
def negativeAmount : S.Input :=
  { context := ⟨"module", "alice"⟩
    moduleReleaseId := "module"
    policy := ⟨"USD", "treasury", 0, true⟩
    command := ⟨"asset_transfer", "USD", "alice", "bob", -1, 0⟩
    pre := { staticGlobalState with
      balances := [⟨"bob", "USD", S.accounts, 1⟩]
      supplies := [⟨"USD", 1⟩] } }

theorem negative_amount_requires_constructor_premise :
    S.CanonicalBalances negativeAmount.pre.balances ∧
    0 ≤ negativeAmount.policy.transferFeeAtoms ∧
    (S.step negativeAmount).verdict = .accepted ∧
    amountAt negativeAmount.pre.balances "bob" "USD" S.accounts = 1 ∧
    amountAt (S.step negativeAmount).post.balances "bob" "USD" S.accounts = 0 ∧
    "bob" ≠ negativeAmount.command.sender := by
  refine ⟨⟨by unfold S.Unique; decide, ?_, by decide, by decide⟩, by decide, by decide,
    by decide, ?_, by decide⟩
  · intro row member
    simp only [negativeAmount, List.mem_singleton] at member
    subst row
    decide
  · change amountAt (Proofs.CanonicalEpochEconomicRowsV1.sortOn
      Proofs.AssetTransferSparseTablesV1.balanceWire
      [⟨"alice", "USD", S.accounts, 1⟩]) "bob" "USD" S.accounts = 0
    rw [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort]
    decide

/-- Dropping the selected-fee lower bound can debit a distinct one-atom fee owner. -/
def negativeFee : S.Input :=
  { negativeAmount with
    policy := { negativeAmount.policy with transferFeeAtoms := -1 }
    command := { negativeAmount.command with amountAtoms := 1 }
    pre := { negativeAmount.pre with balances := [⟨"treasury", "USD", S.accounts, 1⟩] } }

theorem negative_fee_requires_constructor_premise :
    S.CanonicalBalances negativeFee.pre.balances ∧
    0 ≤ negativeFee.command.amountAtoms ∧
    (S.step negativeFee).verdict = .accepted ∧
    amountAt negativeFee.pre.balances "treasury" "USD" S.accounts = 1 ∧
    amountAt (S.step negativeFee).post.balances "treasury" "USD" S.accounts = 0 ∧
    "treasury" ≠ negativeFee.command.sender := by
  refine ⟨⟨by unfold S.Unique; decide, ?_, by decide, by decide⟩, by decide, by decide,
    by decide, ?_, by decide⟩
  · intro row member
    simp only [negativeFee, List.mem_singleton] at member
    subst row
    decide
  · change amountAt (Proofs.CanonicalEpochEconomicRowsV1.sortOn
      Proofs.AssetTransferSparseTablesV1.balanceWire
      [⟨"bob", "USD", S.accounts, 1⟩]) "treasury" "USD" S.accounts = 0
    rw [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort]
    decide

end Proofs.AssetTransferSparseAuthorizationV1
