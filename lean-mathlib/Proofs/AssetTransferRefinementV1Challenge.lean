import Proofs.AssetTransferRefinementV1

/-!
# ASSET_TRANSFER V1 — challenge module

The admission challenge for `Proofs.AssetTransferRefinementV1`. It does
three jobs.

**Typed challenge statements.** Each `challenge_*` theorem restates an
intended result with its type written out in full and closes with the named
core theorem, so an incompatible change to a bound signature stops this
module from compiling.

**A deliberately weakened variant.** `leakyDelta` drops the fee-owner credit,
so the fee leaves the sender and reaches nobody. It is emitted alongside the
honest transition so the paired comparison can kill it: the honest total must
match Python and the leaky total must not. `leaky_is_not_conservative`
records that the conservation theorem has content: a variant that differs
only in the fee credit fails it.

**Executable comparison output.** `challengeReportV1` is a deterministic
string built by *evaluating the definitions* — `transition`, `delta`,
`sumOver`, `roleOrderedCode`, and `intendedBalanceCode` — on the fixed vector
table of the core module. It contains no hand-written behavioural labels, so
it cannot agree with Python by accident of a literal that drifted from the
proof.

## Bounded source comparison only

The report compares this model against the current Python
`transition_asset_transfer_v1` on a fixed vector table. It is a bounded
source comparison, not a runtime refinement proof, and it says nothing about
canonical rows, roots, receipts, journals, or production behaviour. The
`custody_domain` label carried by runtime rows is not modeled and nothing
here asserts custody, possession, title, control, or any enforceable claim
over any asset.
-/

namespace Proofs
namespace AssetTransferRefinementV1Challenge

open Proofs.AssetTransferRefinementV1

/-! ## 1. Bound signatures -/

/-- A code is returned iff its guard fails and every lower-rank guard passes. -/
theorem challenge_exact_precedence :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command) (c : RejectCode),
      rejectCode ctx pre cmd = some c ↔
        ¬ guardPasses ctx pre cmd c ∧ ∀ c', c'.rank < c.rank → guardPasses ctx pre cmd c' :=
  rejectCode_eq_some_iff

/-- Every input is decided as the literal rejection or the literal acceptance. -/
theorem challenge_totality :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command),
      (∃ c, rejectCode ctx pre cmd = some c ∧ transition ctx pre cmd = reject c pre) ∨
      (rejectCode ctx pre cmd = none ∧
        transition ctx pre cmd =
          ⟨.accepted, acceptedState pre cmd, acceptedEffects pre cmd⟩) :=
  transition_total

/-- Every rejection returns the exact pre-state and empty abstract effects. -/
theorem challenge_rejection_is_noop :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command) (c : RejectCode),
      (transition ctx pre cmd).verdict = .rejected c →
        (transition ctx pre cmd).post = pre ∧
        (transition ctx pre cmd).effects = AbstractEffects.empty :=
  fun _ _ _ _ h => ⟨rejected_post_eq_pre h, rejected_effects_empty h⟩

/-- Accepted transfers conserve the enumerated total and preserve supply. -/
theorem challenge_accepted_conservation :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command),
      (transition ctx pre cmd).verdict = .accepted →
        ∀ ps : List Principal, occ cmd.sender ps = 1 → occ cmd.recipient ps = 1 →
          occ pre.policy.feeOwner ps = 1 →
            sumOver (transition ctx pre cmd).post.balance ps = sumOver pre.balance ps ∧
            (transition ctx pre cmd).post.supplyAtoms = pre.supplyAtoms :=
  fun _ _ _ h ps hs hr ho =>
    ⟨accepted_conserves_total h ps hs hr ho, accepted_supply_unchanged h⟩

/-- Accepted balances fit `u128` and every aggregated delta fits `i128`. -/
theorem challenge_accepted_bounds :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command),
      StateWellFormed pre → (transition ctx pre cmd).verdict = .accepted →
        ∀ p : Principal,
          IsU128 ((transition ctx pre cmd).post.balance p) ∧ IsI128 (delta pre cmd p) :=
  fun _ _ _ hpre h p => ⟨accepted_balances_u128 hpre h p, accepted_deltas_i128 h p⟩

/-- The three fee-owner role formulas. -/
theorem challenge_alias_formulas :
    ∀ (pre : TransferState) (cmd : Command), cmd.sender ≠ cmd.recipient →
      (pre.policy.feeOwner = cmd.sender →
        delta pre cmd cmd.sender = -cmd.amountAtoms ∧
        delta pre cmd cmd.recipient = cmd.amountAtoms) ∧
      (pre.policy.feeOwner = cmd.recipient →
        delta pre cmd cmd.sender = -(cmd.amountAtoms + pre.policy.transferFeeAtoms) ∧
        delta pre cmd cmd.recipient = cmd.amountAtoms + pre.policy.transferFeeAtoms) ∧
      (pre.policy.feeOwner ≠ cmd.sender → pre.policy.feeOwner ≠ cmd.recipient →
        delta pre cmd cmd.sender = -(cmd.amountAtoms + pre.policy.transferFeeAtoms) ∧
        delta pre cmd cmd.recipient = cmd.amountAtoms ∧
        delta pre cmd pre.policy.feeOwner = pre.policy.transferFeeAtoms) :=
  fun _ _ hsr =>
    ⟨fun hos => delta_fee_owner_is_sender hos hsr,
      fun hor => delta_fee_owner_is_recipient hor hsr,
      fun hos hor => delta_distinct_roles hsr hos hor⟩

/-- Under the supply cover, `BALANCE_OVERFLOW` is unreachable. -/
theorem challenge_overflow_unreachable :
    ∀ (ctx : Context) (pre : TransferState) (cmd : Command),
      StateWellFormed pre → CommandWellFormed cmd →
        ∀ ps : List Principal, occ cmd.sender ps = 1 → occ cmd.recipient ps = 1 →
          occ pre.policy.feeOwner ps = 1 → sumOver pre.balance ps ≤ pre.supplyAtoms →
            rejectCode ctx pre cmd ≠ some .balanceOverflow :=
  fun _ _ _ hpre hcmd ps hs hr ho hcover =>
    balanceOverflow_unreachable hpre hcmd ps hs hr ho hcover

/-- The Python role-ordered loop agrees with the order-independent rule. -/
theorem challenge_role_order_bridge :
    ∀ (pre : TransferState) (cmd : Command),
      StateWellFormed pre → CommandWellFormed cmd → cmd.sender ≠ cmd.recipient →
        roleOrderedCode pre cmd (roleOrder pre cmd) = intendedBalanceCode pre cmd :=
  fun _ _ hpre hcmd hsr => roleOrdered_eq_intended hpre hcmd hsr

/-! ## 2. A deliberately weakened variant -/

/-- Drops the fee-owner credit: the fee leaves the sender and reaches nobody. -/
def leakyDelta (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
    + indicator cmd.recipient cmd.amountAtoms p

/-- The post-state the weakened variant would produce. -/
def leakyPost (pre : TransferState) (cmd : Command) : TransferState :=
  { pre with balance := fun p => pre.balance p + leakyDelta pre cmd p }

def demoPrincipals : List Principal := [alice, bob, treasury]

theorem honest_conserves_on_demo :
    sumOver acceptDistinct.run.post.balance demoPrincipals
        = sumOver acceptDistinct.pre.balance demoPrincipals ∧
    sumOver acceptDistinct.pre.balance demoPrincipals = 115 := by decide

theorem leaky_breaks_conservation_on_demo :
    sumOver (leakyPost acceptDistinct.pre acceptDistinct.cmd).balance demoPrincipals
        ≠ sumOver acceptDistinct.pre.balance demoPrincipals ∧
    sumOver (leakyPost acceptDistinct.pre acceptDistinct.cmd).balance demoPrincipals = 113 := by
  decide

/-- The conservation check has content: the variant that only drops the fee
credit does not satisfy it. -/
theorem leaky_is_not_conservative :
    ¬ (∀ (pre : TransferState) (cmd : Command) (ps : List Principal),
        occ cmd.sender ps = 1 → occ cmd.recipient ps = 1 → occ pre.policy.feeOwner ps = 1 →
          sumOver (leakyPost pre cmd).balance ps = sumOver pre.balance ps) := by
  intro h
  exact leaky_breaks_conservation_on_demo.1
    (h acceptDistinct.pre acceptDistinct.cmd demoPrincipals (by decide) (by decide) (by decide))

/-! ## 3. Vector table -/

structure Vector where
  name : String
  scenario : Scenario

def vectors : List Vector :=
  [ ⟨"accept_distinct", acceptDistinct⟩,
    ⟨"alias_sender", aliasSender⟩,
    ⟨"alias_recipient", aliasRecipient⟩,
    ⟨"release_mismatch", releaseMismatch⟩,
    ⟨"unknown_command", unknownCommand⟩,
    ⟨"unknown_asset", unknownAsset⟩,
    ⟨"disabled_asset", disabledAsset⟩,
    ⟨"unauthorized_subject", unauthorizedSubject⟩,
    ⟨"self_transfer", selfTransfer⟩,
    ⟨"zero_amount", zeroAmount⟩,
    ⟨"fee_limit_exceeded", feeLimitExceeded⟩,
    ⟨"insufficient_balance", insufficientBalance⟩,
    ⟨"insufficient_neighbor", insufficientNeighbor⟩,
    ⟨"exact_balance", exactBalance⟩,
    ⟨"one_atom", oneAtom⟩,
    ⟨"zero_fee", zeroFee⟩,
    ⟨"maximum_neighbor", maximumNeighbor⟩,
    ⟨"overflow_neighbor", overflowNeighbor⟩,
    ⟨"effect_delta_overflow", effectDeltaOverflow⟩,
    ⟨"width_min_delta", widthMinDelta⟩,
    ⟨"width_alias_sender_aggregate", widthAliasSender⟩,
    ⟨"width_fee_alone", widthFeeAlone⟩ ]

def leakyVectors : List Vector :=
  [ ⟨"accept_distinct", acceptDistinct⟩,
    ⟨"alias_sender", aliasSender⟩,
    ⟨"alias_recipient", aliasRecipient⟩ ]

def verdictLabel : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected c => c.code

def optionLabel : Option RejectCode → String
  | none => "NONE"
  | some c => c.code

/-- The verdict labels of the table, evaluated. -/
def vectorLabels : List String := vectors.map fun v => verdictLabel v.scenario.run.verdict

theorem vectorLabels_eq :
    vectorLabels =
      [ "ACCEPTED", "ACCEPTED", "ACCEPTED", "RELEASE_MISMATCH", "UNKNOWN_COMMAND",
        "UNKNOWN_ASSET", "DISABLED_ASSET", "UNAUTHORIZED_SUBJECT", "SELF_TRANSFER",
        "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED", "INSUFFICIENT_BALANCE", "INSUFFICIENT_BALANCE",
        "ACCEPTED", "ACCEPTED", "ACCEPTED", "ACCEPTED", "BALANCE_OVERFLOW",
        "EFFECT_DELTA_OVERFLOW", "ACCEPTED", "ACCEPTED", "EFFECT_DELTA_OVERFLOW" ] := by
  decide

/-- Every rejection code the bounded model can actually emit is produced by some
vector. The exemption of `postStateResourceBoundExceeded` is DERIVED, not named:
its arm is discharged by `rejectCode_ne_postStateResourceBoundExceeded` (its guard
is definitionally `True`; row finiteness is outside Scope), so a future edit that
gives that guard content breaks this proof instead of silently keeping an
exemption. Runtime reachability of the code is pinned by the transition totality
suite. -/
theorem report_vectors_cover_every_emittable_code :
    ∀ c : RejectCode, (∃ ctx pre cmd, rejectCode ctx pre cmd = some c) → c.code ∈ vectorLabels := by
  intro c ⟨ctx, pre, cmd, h⟩
  rw [vectorLabels_eq]
  cases c <;> first
    | exact absurd h (rejectCode_ne_postStateResourceBoundExceeded ctx pre cmd)
    | decide

/-- On every vector the Python loop and the order-independent rule agree,
including the vectors outside the bridge lemma's premises. -/
theorem roleOrdered_agrees_on_every_vector :
    ∀ v ∈ vectors,
      roleOrderedCode v.scenario.pre v.scenario.cmd (roleOrder v.scenario.pre v.scenario.cmd)
        = intendedBalanceCode v.scenario.pre v.scenario.cmd := by
  decide

/-! ## 4. Derived report

Every field below is computed from the definitions above. -/

def codeRow (c : RejectCode) : String :=
  String.intercalate "," ["CODE", c.code]

def widthRow : String :=
  String.intercalate "," ["WIDTH", toString u128Max, toString i128Min, toString i128Max]

def vectorRow (v : Vector) : String :=
  let r := v.scenario.run
  String.intercalate ","
    ["VECTOR", v.name, verdictLabel r.verdict, toString (r.post.balance alice),
      toString (r.post.balance bob), toString (r.post.balance treasury),
      toString r.post.supplyAtoms]

def moveRows (v : Vector) : List String :=
  v.scenario.run.effects.movements.map fun row =>
    String.intercalate "," ["MOVE", v.name, row.principal, toString row.deltaAtoms]

def feeRows (v : Vector) : List String :=
  v.scenario.run.effects.feeAllocations.map fun row =>
    String.intercalate "," ["FEE", v.name, row.principal, toString row.deltaAtoms]

def orderRow (v : Vector) : String :=
  String.intercalate ","
    ["ORDER", v.name,
      optionLabel (intendedBalanceCode v.scenario.pre v.scenario.cmd),
      optionLabel (roleOrderedCode v.scenario.pre v.scenario.cmd
        (roleOrder v.scenario.pre v.scenario.cmd))]

def leakyRow (v : Vector) : String :=
  String.intercalate ","
    ["LEAKY", v.name,
      toString (sumOver v.scenario.pre.balance demoPrincipals),
      toString (sumOver v.scenario.run.post.balance demoPrincipals),
      toString (sumOver (leakyPost v.scenario.pre v.scenario.cmd).balance demoPrincipals)]

/-- The full deterministic comparison report. -/
def challengeReportV1 : String :=
  String.intercalate "\n"
    (allRejectCodes.map codeRow ++
      [widthRow] ++
      vectors.map vectorRow ++
      (vectors.map moveRows).foldr (fun xs acc => xs ++ acc) [] ++
      (vectors.map feeRows).foldr (fun xs acc => xs ++ acc) [] ++
      vectors.map orderRow ++
      leakyVectors.map leakyRow)

end AssetTransferRefinementV1Challenge
end Proofs
