import Proofs.AssetTransferSparseTablesV1

/-!
Constructed histories of the sparse selected-policy transfer. Rejected attempts
contribute no successor or accepted plan. Accepted steps derive their exact
table relation and preserve canonical source rows for the next attempt.

The configuration fixes one module release and selected policy for the history.
Context authentication, policy membership, metadata/height/replay, full effect
plans, receipt arity and publication are outside this mathematical history.
Checked epoch aggregation still requires its actual prefix-bound acceptance.
-/
namespace Proofs.AssetTransferSparseTraceV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open CheckedEconomicAggregationV1 CheckedEpochEconomicTablesV1

namespace S
export Proofs.AssetTransferSparseTablesV1 (Input step CanonicalBalances
  accepted_sparse_transfer rejected_step_noop)
end S

structure Config where
  moduleReleaseId : String
  policy : Proofs.AssetTransferRefinementV1.Policy

structure Request where
  context : Proofs.AssetTransferRefinementV1.Context
  command : Proofs.AssetTransferRefinementV1.Command

def inputFor (config : Config) (request : Request) (pre : GlobalState) : S.Input :=
  ⟨request.context, config.moduleReleaseId, config.policy, request.command, pre⟩

structure History where
  post : GlobalState
  acceptedPlans : List EffectPlan

def run (config : Config) : List Request → GlobalState → History
  | [], pre => ⟨pre, []⟩
  | request :: requests, pre =>
      let next := S.step (inputFor config request pre)
      match next.verdict with
      | .rejected _ => run config requests pre
      | .accepted =>
          let tail := run config requests next.post
          ⟨tail.post, next.plan :: tail.acceptedPlans⟩

theorem rejected_attempt_omitted (config : Config) (request : Request)
    (requests : List Request) (pre : GlobalState)
    {code : Proofs.AssetTransferRefinementV1.RejectCode}
    (rejected : (S.step (inputFor config request pre)).verdict = .rejected code) :
    run config (request :: requests) pre = run config requests pre ∧
    (S.step (inputFor config request pre)).post = pre ∧
    (S.step (inputFor config request pre)).plan = EffectPlan.empty := by
  exact ⟨by simp only [run, rejected], S.rejected_step_noop rejected⟩

/-- The per-route table premise is constructed by execution, not supplied. -/
theorem run_table_chain (config : Config) (requests : List Request) (pre : GlobalState)
    (canonical : S.CanonicalBalances pre.balances) :
    TableChain pre (run config requests pre).acceptedPlans (run config requests pre).post ∧
    S.CanonicalBalances (run config requests pre).post.balances := by
  induction requests generalizing pre with
  | nil => exact ⟨.nil pre, canonical⟩
  | cons request requests ih =>
      cases verdict : (S.step (inputFor config request pre)).verdict with
      | rejected code =>
          simpa only [run, verdict] using ih pre canonical
      | accepted =>
          have one := S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict
          have tail := ih (S.step (inputFor config request pre)).post one.2.2.1
          simp only [run, verdict]
          exact ⟨.cons one.1 tail.1, tail.2⟩

theorem run_plan_count (config : Config) (requests : List Request) (pre : GlobalState) :
    (run config requests pre).acceptedPlans.length ≤ requests.length := by
  induction requests generalizing pre with
  | nil => exact Nat.le_refl 0
  | cons request requests ih =>
      cases verdict : (S.step (inputFor config request pre)).verdict with
      | rejected code =>
          simp only [run, verdict, List.length_cons]
          exact Nat.le_trans (ih pre) (Nat.le_succ _)
      | accepted =>
          simp only [run, verdict, List.length_cons]
          exact Nat.succ_le_succ (ih (S.step (inputFor config request pre)).post)

/-- Exact endpoint amounts follow for every table and complete denomination key. -/
theorem checked_history_exact_tables (config : Config) (requests : List Request)
    (pre : GlobalState) (canonical : S.CanonicalBalances pre.balances)
    (output : Totals)
    (accepted : checkedEpoch i128 (run config requests pre).acceptedPlans = .ok output)
    (table : Table) (owner asset domain : String) :
    amountAt (tableRows table (run config requests pre).post) owner asset domain -
      amountAt (tableRows table pre) owner asset domain =
      output (encodeKey (tableKind table) owner asset domain) :=
  successful_epoch_exact_tables i128 output
    (run_table_chain config requests pre canonical).1 accepted table owner asset domain

/-- Individual accepted commands do not waive aggregate prefix width checks. -/
theorem checked_history_iff_prefix_bounds (config : Config) (requests : List Request)
    (pre : GlobalState) (canonical : S.CanonicalBalances pre.balances) :
    (∃ output, checkedEpoch i128 (run config requests pre).acceptedPlans = .ok output ∧
      ∀ table owner asset domain,
        amountAt (tableRows table (run config requests pre).post) owner asset domain -
          amountAt (tableRows table pre) owner asset domain =
          output (encodeKey (tableKind table) owner asset domain)) ↔
    PrefixFits i128 empty (orderedRows (run config requests pre).acceptedPlans) :=
  checked_epoch_table_composition_iff i128
    (run_table_chain config requests pre canonical).1

end Proofs.AssetTransferSparseTraceV1
