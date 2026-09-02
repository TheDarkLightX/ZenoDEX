/-!
# ASSET_TRANSFER V1 — bounded single-asset transfer core

A machine-checked model of the rejection precedence and the accepted
arithmetic of `transition_asset_transfer_v1` in
`src/core/asset_transfer_module_v1.py` (mirrored by
`zk/global_settlement_abi_v1/src/asset_transfer.rs`). Everything here is an
abstraction chosen to be provable; the gap to the runtime is spelled out
below rather than left implicit.

## Scope

Exactly one asset, one policy, and one command. The runtime carries a policy
list, a balance-row list, and a supply list indexed by asset; this file
carries a single policy record, a single balance function, and a single
supply value.
The command still names an asset, and `UNKNOWN_ASSET` is modeled as "the
named asset is not the policied asset". Multi-asset lookup is not modeled.

The balance ledger is a total function `Principal → Int`. That is exactly the
observable semantics of `AssetTransferStateV1.balance_atoms` and of the
`values.get((asset, owner), 0)` lookup in `_post_balances`: an absent row reads
as zero. Row finiteness, the canonical row ordering, and zero-balance elision
(`if post_atoms == 0: values.pop(...)`) are not modeled. The account total is
therefore stated over an explicit finite enumeration of principals in which
each touched principal occurs exactly once; see `sumOver`, `occ`, and
`accepted_conserves_total`.

## Integer widths

Amounts, fees, balances, and supply are `Int` with an explicit `u128`
predicate (`IsU128`, matching `MAX_ATOMS_V1`). Effect deltas are `Int` with
an explicit `i128` predicate (`IsI128`, matching `MIN_DELTA_ATOMS_V1` and
`MAX_DELTA_ATOMS_V1`). Width discipline is a premise (`StateWellFormed`,
`CommandWellFormed`), never a consequence: the runtime enforces it in the
dataclass constructors, so the transition never sees an out-of-width input.
The transition itself is total on all `Int` inputs.

## Aggregate deltas before width checks

`delta` is the runtime's aggregated delta dictionary extended by zero: the
sender is debited `amount + fee`, the recipient is credited `amount`, and the
fee owner is credited `fee`, with the three credits summed on one principal
when roles alias. The width check (`EFFECT_DELTA_OVERFLOW`) is applied to the
aggregated values and to the fee itself, exactly as the Python
`_transfer_deltas` does. The current Rust `prepare_transfer` mirrors the final
role-specific aggregation. Its `checked_negative_sum` helper admits magnitude
`2^127` as `i128::MIN` and rejects larger magnitudes. The
`widthMinDelta_accepted` and `widthAliasSender_accepted` theorems pin the two
alias-sensitive boundaries shared by the current Python and Rust cores.

## Balance rejection rule

After the width check, the modeled rule is order-independent: if any touched
account would go negative the code is `INSUFFICIENT_BALANCE`; otherwise, if
any touched account would exceed `u128Max`, the code is `BALANCE_OVERFLOW`.
Under the width premises only the sender can go negative and only the
recipient or a distinct fee owner can overflow, so this is the same rule as
"sender insufficiency wins over every recipient or fee-owner overflow", and
`roleOrdered_eq_intended` proves it coincides with the Python role-ordered
loop (sender, recipient, distinct fee owner) on well-formed inputs. The current
Rust `post_balances` performs a negative-delta preflight followed by a
nonnegative-delta preflight before applying any delta. This gives debit
insufficiency the same fixed priority independently of canonical map order.
`balanceOverflow_unreachable` additionally shows that from a pre-state whose
enumerated account total is covered by supply the overflow code can never be
reached at all.

## Effects

`AbstractEffects` carries account-movement rows (principal, aggregated delta)
and fee-allocation rows only, in role order with zero deltas omitted. The
runtime's canonical row sort, the `custody_domain` label, the asset
conservation row, fee conservation rows, lane writes, occurrence
consumptions, and the external outbox are not represented. The
`custody_domain` value `"accounts"` is an accounting-location label only; no
statement here asserts custody, possession, title, control, or any
enforceable claim over any asset by any party.

## What is NOT claimed

No canonical byte encoding, no state roots or any other root or digest, no
journal or receipt, no route, no replay or occurrence discipline, no
signature or authentication derivation, no multi-asset lookup, no
zero-balance elision, no token syntax discipline, and no economic-policy
correctness. No refinement between this model and the Python or Rust runtime
is claimed; the executable comparison in
`Proofs.AssetTransferRefinementV1Challenge` is a bounded source comparison on
a fixed vector table. This is research-only evidence and confers no
settlement, release, production, migration, or value-moving authority.
-/

namespace Proofs
namespace AssetTransferRefinementV1

/-! ## 1. Widths

The literals below are the Python values `MAX_ATOMS_V1`,
`MIN_DELTA_ATOMS_V1`, and `MAX_DELTA_ATOMS_V1`; the `_eq_pow` theorems pin
them to the power-of-two forms. -/

def u128Max : Int := 340282366920938463463374607431768211455
def i128Max : Int := 170141183460469231731687303715884105727
def i128Min : Int := -170141183460469231731687303715884105728

theorem u128Max_eq_pow : u128Max = 2 ^ 128 - 1 := by decide
theorem i128Max_eq_pow : i128Max = 2 ^ 127 - 1 := by decide
theorem i128Min_eq_pow : i128Min = -(2 ^ 127) := by decide

/-- The `u128` width predicate. -/
def IsU128 (x : Int) : Prop := 0 ≤ x ∧ x ≤ u128Max

/-- The `i128` width predicate. -/
def IsI128 (d : Int) : Prop := i128Min ≤ d ∧ d ≤ i128Max

instance (x : Int) : Decidable (IsU128 x) := inferInstanceAs (Decidable (0 ≤ x ∧ x ≤ u128Max))
instance (d : Int) : Decidable (IsI128 d) := inferInstanceAs (Decidable (i128Min ≤ d ∧ d ≤ i128Max))

/-! ## 2. Tokens

Uninterpreted strings. The runtime's token syntax (`_require_token`) and root
syntax (`_require_root`) are not modeled. -/

abbrev Principal := String
abbrev Asset := String
abbrev Root := String
abbrev CommandKind := String

/-- The wire value of `ASSET_TRANSFER_COMMAND_KIND_V1`. -/
def assetTransferCommandKind : CommandKind := "asset_transfer"

/-! ## 3. Rejection codes

`AssetTransferRejectCodeV1` as a closed enumeration. Declaration order is the
rejection precedence, and `rank` is the position in that order. -/

inductive RejectCode where
  | releaseMismatch
  | unknownCommand
  | unknownAsset
  | disabledAsset
  | unauthorizedSubject
  | selfTransfer
  | zeroAmount
  | feeLimitExceeded
  | effectDeltaOverflow
  | insufficientBalance
  | balanceOverflow
  | postStateResourceBoundExceeded
  deriving DecidableEq, Repr

/-- The stable wire string for each code, matching the Python enum values. -/
def RejectCode.code : RejectCode → String
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .unknownAsset => "UNKNOWN_ASSET"
  | .disabledAsset => "DISABLED_ASSET"
  | .unauthorizedSubject => "UNAUTHORIZED_SUBJECT"
  | .selfTransfer => "SELF_TRANSFER"
  | .zeroAmount => "ZERO_AMOUNT"
  | .feeLimitExceeded => "FEE_LIMIT_EXCEEDED"
  | .effectDeltaOverflow => "EFFECT_DELTA_OVERFLOW"
  | .insufficientBalance => "INSUFFICIENT_BALANCE"
  | .balanceOverflow => "BALANCE_OVERFLOW"
  | .postStateResourceBoundExceeded => "POST_STATE_RESOURCE_BOUND_EXCEEDED"

/-- Position in the precedence order. -/
def RejectCode.rank : RejectCode → Nat
  | .releaseMismatch => 0
  | .unknownCommand => 1
  | .unknownAsset => 2
  | .disabledAsset => 3
  | .unauthorizedSubject => 4
  | .selfTransfer => 5
  | .zeroAmount => 6
  | .feeLimitExceeded => 7
  | .effectDeltaOverflow => 8
  | .insufficientBalance => 9
  | .balanceOverflow => 10
  | .postStateResourceBoundExceeded => 11

/-- The precedence order. The transition walks this list and returns the
first code whose guard fails. -/
def allRejectCodes : List RejectCode :=
  [ .releaseMismatch, .unknownCommand, .unknownAsset, .disabledAsset,
    .unauthorizedSubject, .selfTransfer, .zeroAmount, .feeLimitExceeded,
    .effectDeltaOverflow, .insufficientBalance, .balanceOverflow,
    .postStateResourceBoundExceeded ]

/-- Boolean duplicate check, kept self-contained. -/
def hasDuplicateCode : List RejectCode → Bool
  | [] => false
  | c :: rest => rest.contains c || hasDuplicateCode rest

theorem allRejectCodes_length : allRejectCodes.length = 12 := rfl

theorem allRejectCodes_codes :
    allRejectCodes.map RejectCode.code =
      [ "RELEASE_MISMATCH", "UNKNOWN_COMMAND", "UNKNOWN_ASSET", "DISABLED_ASSET",
        "UNAUTHORIZED_SUBJECT", "SELF_TRANSFER", "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED",
        "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW",
        "POST_STATE_RESOURCE_BOUND_EXCEEDED" ] := rfl

theorem allRejectCodes_ranks :
    allRejectCodes.map RejectCode.rank = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := rfl

theorem allRejectCodes_complete (c : RejectCode) : c ∈ allRejectCodes := by
  cases c <;> decide

theorem allRejectCodes_no_duplicates : hasDuplicateCode allRejectCodes = false := by
  decide

theorem RejectCode.rank_injective {a b : RejectCode} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-! ## 4. Records

The fields that decide the transition. Context fields that do not affect the
decision (`chain_id`, `deployment_root`, `profile_root`, `writer_epoch`,
`command_occurrence_id`, `grant_root`) are omitted. -/

/-- One `AssetTransferPolicyV1`. -/
structure Policy where
  asset : Asset
  feeOwner : Principal
  transferFeeAtoms : Int
  enabled : Bool

/-- The single-asset projection of `AssetTransferStateV1`. -/
structure TransferState where
  moduleReleaseId : Root
  policy : Policy
  balance : Principal → Int
  supplyAtoms : Int

/-- The deciding fields of `AssetTransferContextV1`. -/
structure Context where
  moduleReleaseId : Root
  subjectId : Principal

/-- `AssetTransferCommandV1`. -/
structure Command where
  commandKind : CommandKind
  asset : Asset
  sender : Principal
  recipient : Principal
  amountAtoms : Int
  maxFeeAtoms : Int

/-- The width discipline the runtime constructors enforce on a state. -/
structure StateWellFormed (s : TransferState) : Prop where
  balances : ∀ p : Principal, IsU128 (s.balance p)
  supply : IsU128 s.supplyAtoms
  fee : IsU128 s.policy.transferFeeAtoms

/-- The width discipline the runtime constructor enforces on a command. -/
structure CommandWellFormed (c : Command) : Prop where
  amount : IsU128 c.amountAtoms
  maxFee : IsU128 c.maxFeeAtoms

/-! ## 5. Aggregated deltas

`delta` is the `deltas` dictionary of `_transfer_deltas` extended by zero. -/

/-- `v` at principal `q`, zero elsewhere. -/
def indicator (q : Principal) (v : Int) (p : Principal) : Int :=
  if p = q then v else 0

theorem indicator_self (q : Principal) (v : Int) : indicator q v q = v := by
  simp [indicator]

theorem indicator_of_ne {p q : Principal} (h : p ≠ q) (v : Int) : indicator q v p = 0 := by
  simp [indicator, h]

/-- The aggregated per-principal delta: debit the sender by `amount + fee`,
credit the recipient by `amount`, credit the fee owner by `fee`, summing on
one principal when roles alias. -/
def delta (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
    + indicator cmd.recipient cmd.amountAtoms p
    + indicator pre.policy.feeOwner pre.policy.transferFeeAtoms p

/-- The candidate post balance of a principal. -/
def postBalance (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  pre.balance p + delta pre cmd p

/-! ## 6. Guards

One guard per code, in the order of `allRejectCodes`. A guard that *passes*
means the corresponding rejection does not fire. -/

/-- The width check of `_transfer_deltas`: every aggregated delta and the
fee itself fit `i128`. -/
def widthAdmitted (pre : TransferState) (cmd : Command) : Prop :=
  IsI128 pre.policy.transferFeeAtoms
    ∧ IsI128 (delta pre cmd cmd.sender)
    ∧ IsI128 (delta pre cmd cmd.recipient)
    ∧ IsI128 (delta pre cmd pre.policy.feeOwner)

/-- Some touched account would go negative. -/
def roleUnderflow (pre : TransferState) (cmd : Command) : Prop :=
  postBalance pre cmd cmd.sender < 0
    ∨ postBalance pre cmd cmd.recipient < 0
    ∨ postBalance pre cmd pre.policy.feeOwner < 0

/-- Some touched account would exceed `u128Max`. -/
def roleOverflow (pre : TransferState) (cmd : Command) : Prop :=
  u128Max < postBalance pre cmd cmd.sender
    ∨ u128Max < postBalance pre cmd cmd.recipient
    ∨ u128Max < postBalance pre cmd pre.policy.feeOwner

instance (pre : TransferState) (cmd : Command) : Decidable (widthAdmitted pre cmd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (pre : TransferState) (cmd : Command) : Decidable (roleUnderflow pre cmd) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance (pre : TransferState) (cmd : Command) : Decidable (roleOverflow pre cmd) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The guard table, one arm per code, each arm the runtime condition under
which that rejection does *not* fire. -/
def guardPasses (ctx : Context) (pre : TransferState) (cmd : Command) : RejectCode → Prop
  | .releaseMismatch => ctx.moduleReleaseId = pre.moduleReleaseId
  | .unknownCommand => cmd.commandKind = assetTransferCommandKind
  | .unknownAsset => cmd.asset = pre.policy.asset
  | .disabledAsset => pre.policy.enabled = true
  | .unauthorizedSubject => cmd.sender = ctx.subjectId
  | .selfTransfer => cmd.sender ≠ cmd.recipient
  | .zeroAmount => cmd.amountAtoms ≠ 0
  | .feeLimitExceeded => pre.policy.transferFeeAtoms ≤ cmd.maxFeeAtoms
  | .effectDeltaOverflow => widthAdmitted pre cmd
  | .insufficientBalance => ¬ roleUnderflow pre cmd
  | .balanceOverflow => ¬ roleOverflow pre cmd
  -- Row finiteness is not modeled (see Scope), so the post-state row-ceiling
  -- reject cannot fire in this abstraction: its guard always passes. Runtime
  -- reachability of the code is pinned by the transition totality suite.
  | .postStateResourceBoundExceeded => True

instance guardPassesDecidable (ctx : Context) (pre : TransferState) (cmd : Command) :
    DecidablePred (guardPasses ctx pre cmd)
  | .releaseMismatch => inferInstanceAs (Decidable (ctx.moduleReleaseId = pre.moduleReleaseId))
  | .unknownCommand => inferInstanceAs (Decidable (cmd.commandKind = assetTransferCommandKind))
  | .unknownAsset => inferInstanceAs (Decidable (cmd.asset = pre.policy.asset))
  | .disabledAsset => inferInstanceAs (Decidable (pre.policy.enabled = true))
  | .unauthorizedSubject => inferInstanceAs (Decidable (cmd.sender = ctx.subjectId))
  | .selfTransfer => inferInstanceAs (Decidable (cmd.sender ≠ cmd.recipient))
  | .zeroAmount => inferInstanceAs (Decidable (cmd.amountAtoms ≠ 0))
  | .feeLimitExceeded =>
      inferInstanceAs (Decidable (pre.policy.transferFeeAtoms ≤ cmd.maxFeeAtoms))
  | .effectDeltaOverflow => inferInstanceAs (Decidable (widthAdmitted pre cmd))
  | .insufficientBalance => inferInstanceAs (Decidable (¬ roleUnderflow pre cmd))
  | .balanceOverflow => inferInstanceAs (Decidable (¬ roleOverflow pre cmd))
  | .postStateResourceBoundExceeded => inferInstanceAs (Decidable True)

/-! ## 7. Decision and transition -/

/-- The first code in the list whose guard fails. -/
def firstFailing (g : RejectCode → Prop) [DecidablePred g] : List RejectCode → Option RejectCode
  | [] => none
  | c :: rest => if g c then firstFailing g rest else some c

/-- The rejection decision: the first failing guard in precedence order. -/
def rejectCode (ctx : Context) (pre : TransferState) (cmd : Command) : Option RejectCode :=
  firstFailing (guardPasses ctx pre cmd) allRejectCodes

/-- One abstract effect row: a principal and a signed atom delta. -/
structure MovementRow where
  principal : Principal
  deltaAtoms : Int
  deriving DecidableEq, Repr

/-- The modeled effect surface: account movements and fee allocations. -/
structure AbstractEffects where
  movements : List MovementRow
  feeAllocations : List MovementRow
  deriving DecidableEq, Repr

/-- The empty abstract effects carried by every rejection. -/
def AbstractEffects.empty : AbstractEffects := ⟨[], []⟩

/-- The runtime's dictionary key order: sender, recipient, then the fee owner
only when it is a distinct principal. -/
def roleOrder (pre : TransferState) (cmd : Command) : List Principal :=
  if pre.policy.feeOwner = cmd.sender ∨ pre.policy.feeOwner = cmd.recipient then
    [cmd.sender, cmd.recipient]
  else
    [cmd.sender, cmd.recipient, pre.policy.feeOwner]

/-- Movement rows for the given principals, zero deltas omitted. -/
def movementRows (d : Principal → Int) : List Principal → List MovementRow
  | [] => []
  | p :: ps => if d p = 0 then movementRows d ps else ⟨p, d p⟩ :: movementRows d ps

/-- The abstract effects of an accepted transfer. -/
def acceptedEffects (pre : TransferState) (cmd : Command) : AbstractEffects where
  movements := movementRows (delta pre cmd) (roleOrder pre cmd)
  feeAllocations :=
    if pre.policy.transferFeeAtoms = 0 then []
    else [⟨pre.policy.feeOwner, pre.policy.transferFeeAtoms⟩]

/-- The post-state of an accepted transfer: balances move by `delta`; the
release id, policy, and supply are unchanged. -/
def acceptedState (pre : TransferState) (cmd : Command) : TransferState :=
  { pre with balance := postBalance pre cmd }

inductive Verdict where
  | accepted
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

/-- The full result of one transition attempt. -/
structure TransitionResult where
  verdict : Verdict
  post : TransferState
  effects : AbstractEffects

/-- A rejection: the exact pre-state and empty abstract effects. -/
def reject (code : RejectCode) (pre : TransferState) : TransitionResult :=
  ⟨.rejected code, pre, AbstractEffects.empty⟩

/-- `transition_asset_transfer_v1`, restricted to the modeled surface. -/
def transition (ctx : Context) (pre : TransferState) (cmd : Command) : TransitionResult :=
  match rejectCode ctx pre cmd with
  | some code => reject code pre
  | none => ⟨.accepted, acceptedState pre cmd, acceptedEffects pre cmd⟩

/-! ## 8. Exact precedence

`rejectCode` returns exactly the lowest-rank failing guard. The generic
lemmas are stated for any rank-sorted code list and instantiated at
`allRejectCodes`. -/

theorem firstFailing_eq_none_iff (g : RejectCode → Prop) [DecidablePred g] :
    ∀ codes : List RejectCode, firstFailing g codes = none ↔ ∀ c ∈ codes, g c
  | [] => by simp [firstFailing]
  | c :: rest => by
      constructor
      · intro h c' hc'
        by_cases hg : g c
        · simp only [firstFailing, if_pos hg] at h
          rcases List.mem_cons.mp hc' with rfl | hmem
          · exact hg
          · exact (firstFailing_eq_none_iff g rest).mp h c' hmem
        · simp [firstFailing, if_neg hg] at h
      · intro h
        have hg : g c := h c List.mem_cons_self
        simp only [firstFailing, if_pos hg]
        exact (firstFailing_eq_none_iff g rest).mpr
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- Strictly increasing ranks along a list. -/
def RankSorted : List RejectCode → Prop
  | [] => True
  | c :: rest => (∀ c' ∈ rest, c.rank < c'.rank) ∧ RankSorted rest

instance RankSorted.decidable : ∀ codes : List RejectCode, Decidable (RankSorted codes)
  | [] => inferInstanceAs (Decidable True)
  | c :: rest =>
      have : Decidable (RankSorted rest) := RankSorted.decidable rest
      inferInstanceAs (Decidable ((∀ c' ∈ rest, c.rank < c'.rank) ∧ RankSorted rest))

theorem allRejectCodes_rankSorted : RankSorted allRejectCodes := by decide

theorem firstFailing_some_spec (g : RejectCode → Prop) [DecidablePred g] :
    ∀ (codes : List RejectCode) (c : RejectCode), RankSorted codes →
      firstFailing g codes = some c →
        c ∈ codes ∧ ¬ g c ∧ ∀ c' ∈ codes, c'.rank < c.rank → g c'
  | [], _, _, h => by simp [firstFailing] at h
  | c₀ :: rest, c, hs, h => by
      by_cases hg : g c₀
      · simp only [firstFailing, if_pos hg] at h
        obtain ⟨hmem, hnot, hbefore⟩ := firstFailing_some_spec g rest c hs.2 h
        refine ⟨List.mem_cons_of_mem c₀ hmem, hnot, ?_⟩
        intro c' hc' hlt
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact hg
        · exact hbefore c' hc' hlt
      · simp only [firstFailing, if_neg hg, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, hg, ?_⟩
        intro c' hc' hlt
        rcases List.mem_cons.mp hc' with rfl | hc'
        · omega
        · have := hs.1 c' hc'
          omega

theorem firstFailing_some_of (g : RejectCode → Prop) [DecidablePred g]
    (codes : List RejectCode) (hs : RankSorted codes) (c : RejectCode) (hc : c ∈ codes)
    (hnot : ¬ g c) (hbefore : ∀ c' ∈ codes, c'.rank < c.rank → g c') :
    firstFailing g codes = some c := by
  cases hf : firstFailing g codes with
  | none => exact absurd ((firstFailing_eq_none_iff g codes).mp hf c hc) hnot
  | some c'' =>
      obtain ⟨hmem, hnot'', hbefore''⟩ := firstFailing_some_spec g codes c'' hs hf
      by_cases h1 : c''.rank < c.rank
      · exact absurd (hbefore c'' hmem h1) hnot''
      · by_cases h2 : c.rank < c''.rank
        · exact absurd (hbefore'' c hc h2) hnot
        · have heq : c''.rank = c.rank := by omega
          rw [RejectCode.rank_injective heq]

/-- Exact precedence: a code is returned iff its guard fails and every
lower-rank guard passes. -/
theorem rejectCode_eq_some_iff (ctx : Context) (pre : TransferState) (cmd : Command)
    (c : RejectCode) :
    rejectCode ctx pre cmd = some c ↔
      ¬ guardPasses ctx pre cmd c ∧ ∀ c', c'.rank < c.rank → guardPasses ctx pre cmd c' := by
  constructor
  · intro h
    obtain ⟨_, hnot, hbefore⟩ :=
      firstFailing_some_spec _ allRejectCodes c allRejectCodes_rankSorted h
    exact ⟨hnot, fun c' hlt => hbefore c' (allRejectCodes_complete c') hlt⟩
  · intro h
    exact firstFailing_some_of _ allRejectCodes allRejectCodes_rankSorted c
      (allRejectCodes_complete c) h.1 (fun c' _ hlt => h.2 c' hlt)

/-- No code is returned iff every guard passes. -/
theorem rejectCode_eq_none_iff (ctx : Context) (pre : TransferState) (cmd : Command) :
    rejectCode ctx pre cmd = none ↔ ∀ c, guardPasses ctx pre cmd c := by
  show firstFailing _ allRejectCodes = none ↔ _
  rw [firstFailing_eq_none_iff]
  exact ⟨fun h c => h c (allRejectCodes_complete c), fun h c _ => h c⟩

/-! ## 9. Totality and the rejection no-op -/

/-- Every input is decided: either some code is returned and the result is
the literal rejection, or no code is returned and the result is the literal
acceptance. -/
theorem transition_total (ctx : Context) (pre : TransferState) (cmd : Command) :
    (∃ c, rejectCode ctx pre cmd = some c ∧ transition ctx pre cmd = reject c pre) ∨
    (rejectCode ctx pre cmd = none ∧
      transition ctx pre cmd = ⟨.accepted, acceptedState pre cmd, acceptedEffects pre cmd⟩) := by
  unfold transition
  cases h : rejectCode ctx pre cmd with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some c => exact Or.inl ⟨c, rfl, rfl⟩

theorem reject_post (c : RejectCode) (pre : TransferState) : (reject c pre).post = pre := rfl

theorem reject_effects (c : RejectCode) (pre : TransferState) :
    (reject c pre).effects = AbstractEffects.empty := rfl

/-- Every rejection returns the exact pre-state. -/
theorem rejected_post_eq_pre {ctx : Context} {pre : TransferState} {cmd : Command}
    {c : RejectCode} (h : (transition ctx pre cmd).verdict = .rejected c) :
    (transition ctx pre cmd).post = pre := by
  rcases transition_total ctx pre cmd with ⟨c', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

/-- Every rejection emits the empty abstract effects. -/
theorem rejected_effects_empty {ctx : Context} {pre : TransferState} {cmd : Command}
    {c : RejectCode} (h : (transition ctx pre cmd).verdict = .rejected c) :
    (transition ctx pre cmd).effects = AbstractEffects.empty := by
  rcases transition_total ctx pre cmd with ⟨c', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

theorem rejected_iff {ctx : Context} {pre : TransferState} {cmd : Command} {c : RejectCode} :
    (transition ctx pre cmd).verdict = .rejected c ↔ rejectCode ctx pre cmd = some c := by
  rcases transition_total ctx pre cmd with ⟨c', hc', heq⟩ | ⟨hn, heq⟩
  · rw [heq, hc']
    simp [reject]
  · rw [heq, hn]
    simp

/-- Acceptance is exactly "every guard passes". -/
theorem accepted_iff_all_guards (ctx : Context) (pre : TransferState) (cmd : Command) :
    (transition ctx pre cmd).verdict = .accepted ↔ ∀ c, guardPasses ctx pre cmd c := by
  rcases transition_total ctx pre cmd with ⟨c, hc, heq⟩ | ⟨hn, heq⟩
  · rw [heq]
    constructor
    · intro h
      simp [reject] at h
    · intro h
      have hnone := (rejectCode_eq_none_iff ctx pre cmd).mpr h
      rw [hnone] at hc
      cases hc
  · rw [heq]
    exact ⟨fun _ => (rejectCode_eq_none_iff ctx pre cmd).mp hn, fun _ => rfl⟩

theorem accepted_post_eq {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) :
    (transition ctx pre cmd).post = acceptedState pre cmd ∧
    (transition ctx pre cmd).effects = acceptedEffects pre cmd := by
  rcases transition_total ctx pre cmd with ⟨c, -, heq⟩ | ⟨-, heq⟩
  · rw [heq] at h
    simp [reject] at h
  · rw [heq]
    exact ⟨rfl, rfl⟩

/-! ## 10. Accepted arithmetic -/

/-- Supply is untouched by a transfer. -/
theorem accepted_supply_unchanged {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) :
    (transition ctx pre cmd).post.supplyAtoms = pre.supplyAtoms := by
  rw [(accepted_post_eq h).1]
  rfl

/-- Balances move pointwise by the aggregated delta. -/
theorem accepted_balance_eq {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) (p : Principal) :
    (transition ctx pre cmd).post.balance p = pre.balance p + delta pre cmd p := by
  rw [(accepted_post_eq h).1]
  rfl

/-- A principal in none of the three roles has zero delta. -/
theorem delta_untouched {pre : TransferState} {cmd : Command} {p : Principal}
    (hs : p ≠ cmd.sender) (hr : p ≠ cmd.recipient) (ho : p ≠ pre.policy.feeOwner) :
    delta pre cmd p = 0 := by
  unfold delta
  rw [indicator_of_ne hs, indicator_of_ne hr, indicator_of_ne ho]
  omega

theorem accepted_untouched_unchanged {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) {p : Principal}
    (hs : p ≠ cmd.sender) (hr : p ≠ cmd.recipient) (ho : p ≠ pre.policy.feeOwner) :
    (transition ctx pre cmd).post.balance p = pre.balance p := by
  rw [accepted_balance_eq h p, delta_untouched hs hr ho]
  omega

/-- Distinct fee owner: `-(amount + fee)`, `+amount`, `+fee`. -/
theorem delta_distinct_roles {pre : TransferState} {cmd : Command}
    (hsr : cmd.sender ≠ cmd.recipient) (hos : pre.policy.feeOwner ≠ cmd.sender)
    (hor : pre.policy.feeOwner ≠ cmd.recipient) :
    delta pre cmd cmd.sender = -(cmd.amountAtoms + pre.policy.transferFeeAtoms) ∧
    delta pre cmd cmd.recipient = cmd.amountAtoms ∧
    delta pre cmd pre.policy.feeOwner = pre.policy.transferFeeAtoms := by
  refine ⟨?_, ?_, ?_⟩
  · unfold delta
    rw [indicator_self, indicator_of_ne hsr, indicator_of_ne (Ne.symm hos)]
    omega
  · unfold delta
    rw [indicator_of_ne (Ne.symm hsr), indicator_self, indicator_of_ne (Ne.symm hor)]
    omega
  · unfold delta
    rw [indicator_of_ne hos, indicator_of_ne hor, indicator_self]
    omega

/-- Fee owner equals sender: the debit and the fee credit aggregate to
`-amount` on the sender; the recipient receives `amount`. -/
theorem delta_fee_owner_is_sender {pre : TransferState} {cmd : Command}
    (hos : pre.policy.feeOwner = cmd.sender) (hsr : cmd.sender ≠ cmd.recipient) :
    delta pre cmd cmd.sender = -cmd.amountAtoms ∧
    delta pre cmd cmd.recipient = cmd.amountAtoms := by
  constructor
  · unfold delta
    rw [indicator_self, indicator_of_ne hsr, hos, indicator_self]
    omega
  · unfold delta
    rw [indicator_of_ne (Ne.symm hsr), indicator_self, hos, indicator_of_ne (Ne.symm hsr)]
    omega

/-- Fee owner equals recipient: the sender pays `amount + fee` and the
recipient receives `amount + fee`. -/
theorem delta_fee_owner_is_recipient {pre : TransferState} {cmd : Command}
    (hor : pre.policy.feeOwner = cmd.recipient) (hsr : cmd.sender ≠ cmd.recipient) :
    delta pre cmd cmd.sender = -(cmd.amountAtoms + pre.policy.transferFeeAtoms) ∧
    delta pre cmd cmd.recipient = cmd.amountAtoms + pre.policy.transferFeeAtoms := by
  constructor
  · unfold delta
    rw [indicator_self, indicator_of_ne hsr, hor, indicator_of_ne hsr]
    omega
  · unfold delta
    rw [indicator_of_ne (Ne.symm hsr), indicator_self, hor, indicator_self]
    omega

/-! ## 11. Enumerated account totals

The ledger is a function, so the account total is stated over an explicit
finite enumeration of principals. `occ q ps` counts the occurrences of `q`. -/

def sumOver (f : Principal → Int) : List Principal → Int
  | [] => 0
  | p :: ps => f p + sumOver f ps

def occ (q : Principal) : List Principal → Int
  | [] => 0
  | p :: ps => (if p = q then 1 else 0) + occ q ps

theorem sumOver_add (f g : Principal → Int) :
    ∀ ps : List Principal, sumOver (fun p => f p + g p) ps = sumOver f ps + sumOver g ps
  | [] => rfl
  | p :: ps => by
      simp only [sumOver, sumOver_add f g ps]
      omega

theorem sumOver_congr {f g : Principal → Int} (h : ∀ p, f p = g p) :
    ∀ ps : List Principal, sumOver f ps = sumOver g ps
  | [] => rfl
  | p :: ps => by simp only [sumOver, h p, sumOver_congr h ps]

theorem sumOver_nonneg {f : Principal → Int} (hf : ∀ p, 0 ≤ f p) :
    ∀ ps : List Principal, 0 ≤ sumOver f ps
  | [] => by simp [sumOver]
  | p :: ps => by
      have h1 := hf p
      have h2 := sumOver_nonneg hf ps
      simp only [sumOver]
      omega

theorem sumOver_indicator (q : Principal) (v : Int) :
    ∀ ps : List Principal, sumOver (fun p => indicator q v p) ps = v * occ q ps
  | [] => by simp [sumOver, occ]
  | p :: ps => by
      have ih := sumOver_indicator q v ps
      simp only [sumOver, occ]
      rw [ih, Int.mul_add]
      unfold indicator
      by_cases h : p = q
      · rw [if_pos h, if_pos h]
        omega
      · rw [if_neg h, if_neg h]
        omega

/-- The enumerated delta total, as the three role terms. -/
theorem sumOver_delta (pre : TransferState) (cmd : Command) (ps : List Principal) :
    sumOver (delta pre cmd) ps =
      -(cmd.amountAtoms + pre.policy.transferFeeAtoms) * occ cmd.sender ps
        + cmd.amountAtoms * occ cmd.recipient ps
        + pre.policy.transferFeeAtoms * occ pre.policy.feeOwner ps := by
  show sumOver (fun p =>
      (fun p => indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
        + indicator cmd.recipient cmd.amountAtoms p) p
        + indicator pre.policy.feeOwner pre.policy.transferFeeAtoms p) ps = _
  rw [sumOver_add, sumOver_add, sumOver_indicator, sumOver_indicator, sumOver_indicator]

/-- Conservation of the enumerated account total: for any enumeration in
which each touched principal occurs exactly once, the total is unchanged. -/
theorem accepted_conserves_total {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) (ps : List Principal)
    (hs : occ cmd.sender ps = 1) (hr : occ cmd.recipient ps = 1)
    (ho : occ pre.policy.feeOwner ps = 1) :
    sumOver (transition ctx pre cmd).post.balance ps = sumOver pre.balance ps := by
  rw [(accepted_post_eq h).1]
  have hsum : sumOver (acceptedState pre cmd).balance ps
      = sumOver pre.balance ps + sumOver (delta pre cmd) ps := by
    rw [← sumOver_add]
    rfl
  rw [hsum, sumOver_delta, hs, hr, ho]
  omega

/-- The supply cover `total ≤ supply` is preserved. -/
theorem accepted_supply_cover_preserved {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) (ps : List Principal)
    (hs : occ cmd.sender ps = 1) (hr : occ cmd.recipient ps = 1)
    (ho : occ pre.policy.feeOwner ps = 1)
    (hcover : sumOver pre.balance ps ≤ pre.supplyAtoms) :
    sumOver (transition ctx pre cmd).post.balance ps ≤ (transition ctx pre cmd).post.supplyAtoms := by
  rw [accepted_conserves_total h ps hs hr ho, accepted_supply_unchanged h]
  exact hcover

/-! ## 12. Width bounds of accepted transitions -/

/-- Every aggregated delta of an accepted transfer fits `i128`: the three
role values by the width guard, every other principal because its delta is
zero. -/
theorem accepted_deltas_i128 {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) (p : Principal) :
    IsI128 (delta pre cmd p) := by
  have hw : widthAdmitted pre cmd :=
    (accepted_iff_all_guards ctx pre cmd).mp h .effectDeltaOverflow
  by_cases hs : p = cmd.sender
  · rw [hs]
    exact hw.2.1
  by_cases hr : p = cmd.recipient
  · rw [hr]
    exact hw.2.2.1
  by_cases ho : p = pre.policy.feeOwner
  · rw [ho]
    exact hw.2.2.2
  rw [delta_untouched hs hr ho]
  exact ⟨by decide, by decide⟩

theorem movementRows_mem {d : Principal → Int} :
    ∀ {ps : List Principal} {row : MovementRow}, row ∈ movementRows d ps →
      row.deltaAtoms = d row.principal ∧ row.deltaAtoms ≠ 0
  | [], _, h => by simp [movementRows] at h
  | p :: ps, row, h => by
      simp only [movementRows] at h
      split at h
      · exact movementRows_mem h
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨rfl, by assumption⟩
        · exact movementRows_mem h

/-- Every emitted movement row carries an `i128` delta. -/
theorem accepted_movement_rows_i128 {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) :
    ∀ row ∈ (transition ctx pre cmd).effects.movements, IsI128 row.deltaAtoms := by
  intro row hrow
  rw [(accepted_post_eq h).2] at hrow
  have hmem := movementRows_mem hrow
  rw [hmem.1]
  exact accepted_deltas_i128 h row.principal

/-- Every post balance of an accepted transfer fits `u128`: the three role
accounts by the balance guards, every other account because it is unchanged
from a well-formed pre-state. -/
theorem accepted_balances_u128 {ctx : Context} {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre) (h : (transition ctx pre cmd).verdict = .accepted)
    (p : Principal) : IsU128 ((transition ctx pre cmd).post.balance p) := by
  rw [accepted_balance_eq h p]
  have hg := (accepted_iff_all_guards ctx pre cmd).mp h
  have hu : ¬ roleUnderflow pre cmd := hg .insufficientBalance
  have hov : ¬ roleOverflow pre cmd := hg .balanceOverflow
  simp only [roleUnderflow, roleOverflow, postBalance, not_or] at hu hov
  unfold IsU128
  by_cases hs : p = cmd.sender
  · rw [hs]
    omega
  by_cases hr : p = cmd.recipient
  · rw [hr]
    omega
  by_cases ho : p = pre.policy.feeOwner
  · rw [ho]
    omega
  rw [delta_untouched hs hr ho]
  have hp := hpre.balances p
  unfold IsU128 at hp
  omega

/-! ## 13. The Python role-ordered loop

`_post_balances` walks the delta dictionary in insertion order (sender,
recipient, then a distinct fee owner) and returns the first failing check.
On well-formed inputs that loop returns the same code as the
order-independent rule. -/

/-- The Python loop over a principal list. -/
def roleOrderedCode (pre : TransferState) (cmd : Command) : List Principal → Option RejectCode
  | [] => none
  | p :: rest =>
      if postBalance pre cmd p < 0 then some .insufficientBalance
      else if u128Max < postBalance pre cmd p then some .balanceOverflow
      else roleOrderedCode pre cmd rest

/-- The order-independent balance rule used by `guardPasses`. -/
def intendedBalanceCode (pre : TransferState) (cmd : Command) : Option RejectCode :=
  if roleUnderflow pre cmd then some .insufficientBalance
  else if roleOverflow pre cmd then some .balanceOverflow
  else none

theorem roleOrdered_eq_intended {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed cmd)
    (hsr : cmd.sender ≠ cmd.recipient) :
    roleOrderedCode pre cmd (roleOrder pre cmd) = intendedBalanceCode pre cmd := by
  have hbs := (hpre.balances cmd.sender).2
  have hbr := (hpre.balances cmd.recipient).1
  have hbo := (hpre.balances pre.policy.feeOwner).1
  have hfee := hpre.fee.1
  have hamt := hcmd.amount.1
  unfold IsU128 at hbs hbr hbo hfee hamt
  unfold roleOrder intendedBalanceCode
  by_cases hos : pre.policy.feeOwner = cmd.sender
  · obtain ⟨hds, hdr⟩ := delta_fee_owner_is_sender hos hsr
    rw [if_pos (Or.inl hos)]
    simp only [roleOrderedCode, roleUnderflow, roleOverflow, postBalance, hos]
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  · by_cases hor : pre.policy.feeOwner = cmd.recipient
    · obtain ⟨hds, hdr⟩ := delta_fee_owner_is_recipient hor hsr
      rw [if_pos (Or.inr hor)]
      simp only [roleOrderedCode, roleUnderflow, roleOverflow, postBalance, hor]
      repeat' split
      all_goals first | rfl | (exfalso; omega)
    · obtain ⟨hds, hdr, hdo⟩ := delta_distinct_roles hsr hos hor
      rw [if_neg (by rintro (h | h) <;> contradiction)]
      simp only [roleOrderedCode, roleUnderflow, roleOverflow, postBalance]
      repeat' split
      all_goals first | rfl | (exfalso; omega)

/-! ## 14. Overflow is unreachable under the supply cover

Two well-formed accounts that each occur once in an enumeration sum to at
most the enumerated total; with the total covered by a `u128` supply, no
touched account can exceed `u128Max` once the sender is solvent. -/

theorem sumOver_two_le {f : Principal → Int} (hf : ∀ p, 0 ≤ f p) {s r : Principal}
    (hsr : s ≠ r) {ps : List Principal} (hs : occ s ps = 1) (hr : occ r ps = 1) :
    f s + f r ≤ sumOver f ps := by
  have hg : ∀ p, 0 ≤ f p - indicator s (f s) p - indicator r (f r) p := by
    intro p
    by_cases hps : p = s
    · rw [hps, indicator_self, indicator_of_ne hsr]
      omega
    · by_cases hpr : p = r
      · rw [hpr, indicator_of_ne (Ne.symm hsr), indicator_self]
        omega
      · rw [indicator_of_ne hps, indicator_of_ne hpr]
        have := hf p
        omega
  have hsplit : ∀ p, f p =
      (fun p => (f p - indicator s (f s) p - indicator r (f r) p) + indicator s (f s) p) p
        + indicator r (f r) p := by
    intro p
    show f p = (f p - indicator s (f s) p - indicator r (f r) p) + indicator s (f s) p
      + indicator r (f r) p
    omega
  rw [sumOver_congr hsplit, sumOver_add, sumOver_add, sumOver_indicator, sumOver_indicator,
    hs, hr]
  have := sumOver_nonneg hg ps
  omega

/-- From a well-formed pre-state whose enumerated total is covered by supply,
`BALANCE_OVERFLOW` can never be returned. -/
theorem balanceOverflow_unreachable {ctx : Context} {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed cmd) (ps : List Principal)
    (hs : occ cmd.sender ps = 1) (hr : occ cmd.recipient ps = 1)
    (ho : occ pre.policy.feeOwner ps = 1)
    (hcover : sumOver pre.balance ps ≤ pre.supplyAtoms) :
    rejectCode ctx pre cmd ≠ some .balanceOverflow := by
  intro h
  rw [rejectCode_eq_some_iff] at h
  obtain ⟨hfail, hbefore⟩ := h
  have hsr : cmd.sender ≠ cmd.recipient := hbefore .selfTransfer (by decide)
  have hunder : ¬ roleUnderflow pre cmd := hbefore .insufficientBalance (by decide)
  have hover : roleOverflow pre cmd := Decidable.of_not_not hfail
  have hbal : ∀ p, 0 ≤ pre.balance p := fun p => (hpre.balances p).1
  have hsupply := hpre.supply.2
  have hfee := hpre.fee.1
  have hamt := hcmd.amount.1
  have hbs := (hpre.balances cmd.sender).2
  simp only [roleUnderflow, roleOverflow, postBalance, not_or] at hunder hover
  by_cases hos : pre.policy.feeOwner = cmd.sender
  · obtain ⟨hds, hdr⟩ := delta_fee_owner_is_sender hos hsr
    have hbound := sumOver_two_le hbal hsr hs hr
    rw [hos] at hover
    rcases hover with h1 | h1 | h1 <;> omega
  · by_cases hor : pre.policy.feeOwner = cmd.recipient
    · obtain ⟨hds, hdr⟩ := delta_fee_owner_is_recipient hor hsr
      have hbound := sumOver_two_le hbal hsr hs hr
      rw [hor] at hover
      rcases hover with h1 | h1 | h1 <;> omega
    · obtain ⟨hds, hdr, hdo⟩ := delta_distinct_roles hsr hos hor
      have hbound1 := sumOver_two_le hbal hsr hs hr
      have hbound2 := sumOver_two_le hbal (Ne.symm hos) hs ho
      rcases hover with h1 | h1 | h1 <;> omega

/-! ## 15. Fixtures

The vector table shared with `Proofs.AssetTransferRefinementV1Challenge` and
with the Python comparison. Root strings are arbitrary tokens here; only
their equality or inequality is observed. -/

/-- A finite ledger: lookup with default zero, the observable semantics of
`balance_atoms`. -/
def ledger : List (Principal × Int) → Principal → Int
  | [], _ => 0
  | (q, v) :: rest, p => if p = q then v else ledger rest p

def alice : Principal := "alice"
def bob : Principal := "bob"
def treasury : Principal := "treasury"
def mallory : Principal := "mallory"
def usd : Asset := "USD"
def eur : Asset := "EUR"
def releaseA : Root := "release-3"
def releaseB : Root := "release-99"

/-- `2 ^ 127`, as a literal. -/
def twoPow127 : Int := 170141183460469231731687303715884105728

theorem twoPow127_eq_pow : twoPow127 = 2 ^ 127 := by decide

/-- One input triple. -/
structure Scenario where
  ctx : Context
  pre : TransferState
  cmd : Command

/-- Build a scenario from the vector-table fields; the state release id is
always `releaseA` and the policied asset is always `usd`. -/
def scenario (feeOwner : Principal) (fee : Int) (enabled : Bool)
    (rows : List (Principal × Int)) (supply : Int) (ctxRelease : Root) (subject : Principal)
    (kind : CommandKind) (asset : Asset) (sender recipient : Principal)
    (amount maxFee : Int) : Scenario where
  ctx := { moduleReleaseId := ctxRelease, subjectId := subject }
  pre :=
    { moduleReleaseId := releaseA
      policy := { asset := usd, feeOwner := feeOwner, transferFeeAtoms := fee, enabled := enabled }
      balance := ledger rows
      supplyAtoms := supply }
  cmd :=
    { commandKind := kind, asset := asset, sender := sender, recipient := recipient,
      amountAtoms := amount, maxFeeAtoms := maxFee }

def Scenario.run (s : Scenario) : TransitionResult := transition s.ctx s.pre s.cmd

def baseRows : List (Principal × Int) := [(alice, 100), (bob, 10), (treasury, 5)]

def acceptDistinct : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 2
def aliasSender : Scenario :=
  scenario alice 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 2
def aliasRecipient : Scenario :=
  scenario bob 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 2
def releaseMismatch : Scenario :=
  scenario treasury 2 true baseRows 115 releaseB alice assetTransferCommandKind usd alice bob 30 2
def unknownCommand : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice "unknown" usd alice bob 30 2
def unknownAsset : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind eur alice bob 30 2
def disabledAsset : Scenario :=
  scenario treasury 2 false baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 2
def unauthorizedSubject : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA mallory assetTransferCommandKind usd alice bob 30 2
def selfTransfer : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice alice 30 2
def zeroAmount : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 0 2
def feeLimitExceeded : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 1
def insufficientBalance : Scenario :=
  scenario treasury 2 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 99 2
def insufficientNeighbor : Scenario :=
  scenario treasury 2 true [(alice, 31), (bob, 10), (treasury, 5)] 46 releaseA alice
    assetTransferCommandKind usd alice bob 30 2
def exactBalance : Scenario :=
  scenario treasury 2 true [(alice, 32), (bob, 10), (treasury, 5)] 47 releaseA alice
    assetTransferCommandKind usd alice bob 30 2
def oneAtom : Scenario :=
  scenario treasury 0 true [(alice, 1), (bob, 10), (treasury, 5)] 16 releaseA alice
    assetTransferCommandKind usd alice bob 1 0
def zeroFee : Scenario :=
  scenario treasury 0 true baseRows 115 releaseA alice assetTransferCommandKind usd alice bob 30 0
def maximumNeighbor : Scenario :=
  scenario treasury 0 true [(alice, 30), (bob, u128Max - 30)] u128Max releaseA alice
    assetTransferCommandKind usd alice bob 30 0
/-- One atom past the recipient maximum. This pre-state violates the supply
cover (`30 + (u128Max - 29) > u128Max`), which is exactly why the runtime
never sees it; see `balanceOverflow_unreachable`. -/
def overflowNeighbor : Scenario :=
  scenario treasury 0 true [(alice, 30), (bob, u128Max - 29)] u128Max releaseA alice
    assetTransferCommandKind usd alice bob 30 0
def effectDeltaOverflow : Scenario :=
  scenario treasury 0 true [(alice, twoPow127)] twoPow127 releaseA alice
    assetTransferCommandKind usd alice bob twoPow127 0
/-- Sender delta exactly `i128Min`, admitted by both current runtime cores. -/
def widthMinDelta : Scenario :=
  scenario treasury 1 true [(alice, twoPow127)] twoPow127 releaseA alice
    assetTransferCommandKind usd alice bob i128Max 1
/-- Fee owner equals sender with `amount + fee > i128Max`: the final sender
delta is `-amount`, so the pre-aggregation sum does not constrain this role. -/
def widthAliasSender : Scenario :=
  scenario alice i128Max true [(alice, i128Max)] i128Max releaseA alice
    assetTransferCommandKind usd alice bob i128Max i128Max
/-- The fee alone exceeds `i128Max` although every aggregated delta is tiny. -/
def widthFeeAlone : Scenario :=
  scenario alice twoPow127 true [(alice, 1)] 1 releaseA alice
    assetTransferCommandKind usd alice bob 1 twoPow127

/-! ## 16. Boundary lemmas

Each statement is decided by evaluating the transition on a fixture. -/

theorem demo_accepted_values :
    acceptDistinct.run.verdict = .accepted ∧
    acceptDistinct.run.post.balance alice = 68 ∧
    acceptDistinct.run.post.balance bob = 40 ∧
    acceptDistinct.run.post.balance treasury = 7 ∧
    acceptDistinct.run.post.supplyAtoms = 115 ∧
    acceptDistinct.run.effects =
      ⟨[⟨alice, -32⟩, ⟨bob, 30⟩, ⟨treasury, 2⟩], [⟨treasury, 2⟩]⟩ := by decide

theorem aliasSender_values :
    aliasSender.run.verdict = .accepted ∧
    aliasSender.run.post.balance alice = 70 ∧
    aliasSender.run.post.balance bob = 40 ∧
    aliasSender.run.post.balance treasury = 5 ∧
    aliasSender.run.effects = ⟨[⟨alice, -30⟩, ⟨bob, 30⟩], [⟨alice, 2⟩]⟩ := by decide

theorem aliasRecipient_values :
    aliasRecipient.run.verdict = .accepted ∧
    aliasRecipient.run.post.balance alice = 68 ∧
    aliasRecipient.run.post.balance bob = 42 ∧
    aliasRecipient.run.post.balance treasury = 5 ∧
    aliasRecipient.run.effects = ⟨[⟨alice, -32⟩, ⟨bob, 32⟩], [⟨bob, 2⟩]⟩ := by decide

theorem rejection_vectors :
    releaseMismatch.run.verdict = .rejected .releaseMismatch ∧
    unknownCommand.run.verdict = .rejected .unknownCommand ∧
    unknownAsset.run.verdict = .rejected .unknownAsset ∧
    disabledAsset.run.verdict = .rejected .disabledAsset ∧
    unauthorizedSubject.run.verdict = .rejected .unauthorizedSubject ∧
    selfTransfer.run.verdict = .rejected .selfTransfer ∧
    zeroAmount.run.verdict = .rejected .zeroAmount ∧
    feeLimitExceeded.run.verdict = .rejected .feeLimitExceeded ∧
    insufficientBalance.run.verdict = .rejected .insufficientBalance ∧
    insufficientBalance.run.post.balance alice = 100 ∧
    insufficientBalance.run.effects = AbstractEffects.empty := by decide

theorem oneAtom_accepted :
    oneAtom.run.verdict = .accepted ∧
    oneAtom.run.post.balance alice = 0 ∧
    oneAtom.run.post.balance bob = 11 ∧
    oneAtom.run.post.balance treasury = 5 ∧
    oneAtom.run.effects = ⟨[⟨alice, -1⟩, ⟨bob, 1⟩], []⟩ := by decide

theorem exactBalance_accepted :
    exactBalance.run.verdict = .accepted ∧
    exactBalance.run.post.balance alice = 0 ∧
    exactBalance.run.post.balance bob = 40 ∧
    exactBalance.run.post.balance treasury = 7 := by decide

theorem insufficientNeighbor_rejected :
    insufficientNeighbor.run.verdict = .rejected .insufficientBalance ∧
    insufficientNeighbor.run.post.balance alice = 31 ∧
    insufficientNeighbor.run.effects = AbstractEffects.empty := by decide

theorem maximumNeighbor_accepted :
    maximumNeighbor.run.verdict = .accepted ∧
    maximumNeighbor.run.post.balance alice = 0 ∧
    maximumNeighbor.run.post.balance bob = u128Max ∧
    maximumNeighbor.run.post.balance treasury = 0 := by decide

theorem overflowNeighbor_rejected :
    overflowNeighbor.run.verdict = .rejected .balanceOverflow ∧
    overflowNeighbor.run.post.balance bob = u128Max - 29 ∧
    overflowNeighbor.run.effects = AbstractEffects.empty := by decide

theorem zeroFee_accepted_without_fee_row :
    zeroFee.run.verdict = .accepted ∧
    zeroFee.run.post.balance alice = 70 ∧
    zeroFee.run.post.balance bob = 40 ∧
    zeroFee.run.post.balance treasury = 5 ∧
    zeroFee.run.effects = ⟨[⟨alice, -30⟩, ⟨bob, 30⟩], []⟩ := by decide

/-- `fee = max_fee` is admitted; `fee = max_fee + 1` is `FEE_LIMIT_EXCEEDED`. -/
theorem feeLimit_boundary :
    acceptDistinct.pre.policy.transferFeeAtoms = acceptDistinct.cmd.maxFeeAtoms ∧
    acceptDistinct.run.verdict = .accepted ∧
    feeLimitExceeded.pre.policy.transferFeeAtoms = feeLimitExceeded.cmd.maxFeeAtoms + 1 ∧
    feeLimitExceeded.run.verdict = .rejected .feeLimitExceeded := by decide

theorem widthMinDelta_accepted :
    delta widthMinDelta.pre widthMinDelta.cmd alice = i128Min ∧
    widthMinDelta.run.verdict = .accepted ∧
    widthMinDelta.run.post.balance alice = 0 ∧
    widthMinDelta.run.post.balance bob = i128Max ∧
    widthMinDelta.run.post.balance treasury = 1 := by decide

theorem widthAliasSender_accepted :
    delta widthAliasSender.pre widthAliasSender.cmd alice = -i128Max ∧
    widthAliasSender.run.verdict = .accepted ∧
    widthAliasSender.run.post.balance alice = 0 ∧
    widthAliasSender.run.post.balance bob = i128Max := by decide

theorem widthFeeAlone_rejected :
    delta widthFeeAlone.pre widthFeeAlone.cmd alice = -1 ∧
    delta widthFeeAlone.pre widthFeeAlone.cmd bob = 1 ∧
    widthFeeAlone.run.verdict = .rejected .effectDeltaOverflow := by decide

theorem effectDeltaOverflow_rejected :
    effectDeltaOverflow.run.verdict = .rejected .effectDeltaOverflow ∧
    effectDeltaOverflow.run.post.balance alice = twoPow127 := by decide

end AssetTransferRefinementV1
end Proofs
