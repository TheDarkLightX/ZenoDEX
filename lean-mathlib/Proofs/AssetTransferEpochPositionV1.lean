import Std.Tactic

/-!
An explicit epoch fold derives constant target height and prefix association.
Roots are abstract natural-number identities. Connecting this model to actual
hashes, decoded state, receipt authentication and Python/Rust admission is an
external representation/refinement obligation. No value-safety theorem follows
from this control-flow model alone. Runtime UInt64 use additionally requires
sourceHeight < 2^64 - 1; runtime admission rejects overflow.
-/

namespace Proofs.AssetTransferEpochPositionV1

structure Stamp where
  height : Nat
  root : Nat
  deriving DecidableEq, Repr

structure Command where
  height : Nat
  preRoot : Nat
  postRoot : Nat
  deriving DecidableEq, Repr

def predecessorHeight (sourceHeight index : Nat) : Nat :=
  if index = 0 then sourceHeight else sourceHeight + 1

def step (sourceHeight index : Nat) (state : Stamp) (cmd : Command) : Option Stamp :=
  if cmd.preRoot = state.root ∧ cmd.height = sourceHeight + 1 ∧
      state.height = predecessorHeight sourceHeight index ∧
      index < 64 then
    some ⟨sourceHeight + 1, cmd.postRoot⟩
  else none

def run (sourceHeight index : Nat) (state : Stamp) : List Command → Option Stamp
  | [] => some state
  | cmd :: rest => (step sourceHeight index state cmd).bind fun next =>
      run sourceHeight (index + 1) next rest

theorem accepted_step_binds_height_and_predecessor
    {h i : Nat} {s post : Stamp} {cmd : Command}
    (accepted : step h i s cmd = some post) :
    post.height = h + 1 ∧ cmd.preRoot = s.root ∧ i < 64 := by
  unfold step at accepted
  split at accepted
  · rename_i guard
    cases accepted
    exact ⟨rfl, guard.1, guard.2.2.2⟩
  · contradiction

theorem run_append (h i : Nat) (s : Stamp) (xs ys : List Command) :
    run h i s (xs ++ ys) =
      (run h i s xs).bind fun middle => run h (i + xs.length) middle ys := by
  induction xs generalizing i s with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, run, Option.bind_some]
  | cons cmd rest ih =>
      simp only [List.cons_append, run, List.length_cons]
      cases hs : step h i s cmd with
      | none => simp only [Option.bind_none]
      | some next =>
          simp only [Option.bind_some]
          rw [ih]
          simp only [Nat.add_assoc, Nat.add_comm 1 rest.length]

theorem accepted_prefix_has_exact_intermediate_state
    {h i : Nat} {s post : Stamp} {xs ys : List Command}
    (accepted : run h i s (xs ++ ys) = some post) :
    ∃ middle, run h i s xs = some middle ∧
      run h (i + xs.length) middle ys = some post := by
  rw [run_append] at accepted
  cases hp : run h i s xs with
  | none => simp only [hp, Option.bind_none] at accepted; contradiction
  | some middle =>
      exact ⟨middle, rfl, by simpa only [hp, Option.bind_some] using accepted⟩

theorem accepted_run_length_bound {h i : Nat} {s post : Stamp} {cmds : List Command}
    (initialBound : i ≤ 64) (accepted : run h i s cmds = some post) :
    i + cmds.length ≤ 64 := by
  induction cmds generalizing i s with
  | nil => simpa only [List.length_nil, Nat.add_zero] using initialBound
  | cons cmd rest ih =>
      simp only [run] at accepted
      cases hs : step h i s cmd with
      | none => simp only [hs, Option.bind_none] at accepted; contradiction
      | some next =>
          have hi := (accepted_step_binds_height_and_predecessor hs).2.2
          have hb : i + 1 ≤ 64 := by omega
          have tail := ih hb (by simpa only [hs, Option.bind_some] using accepted)
          simp only [List.length_cons]
          omega

theorem accepted_nonempty_run_height
    {h i : Nat} {s post : Stamp} {cmd : Command} {rest : List Command}
    (accepted : run h i s (cmd :: rest) = some post) : post.height = h + 1 := by
  induction rest generalizing i s cmd with
  | nil =>
      cases hs : step h i s cmd with
      | none => simp only [run, hs, Option.bind_none] at accepted; contradiction
      | some next =>
          have heq : next = post := by
            simpa only [run, hs, Option.bind_some, Option.some.injEq] using accepted
          rw [← heq]
          exact (accepted_step_binds_height_and_predecessor hs).1
  | cons next rest ih =>
      simp only [run] at accepted
      cases hs : step h i s cmd with
      | none => simp only [hs, Option.bind_none] at accepted; contradiction
      | some middle =>
          apply ih
          simpa only [hs, Option.bind_some] using accepted

theorem two_command_nonempty_control :
    run 7 0 ⟨7, 10⟩ [⟨8, 10, 11⟩, ⟨8, 11, 12⟩] = some ⟨8, 12⟩ := by decide

theorem wrong_prefix_root_rejects :
    run 7 0 ⟨7, 10⟩ [⟨8, 10, 11⟩, ⟨8, 10, 12⟩] = none := by decide

theorem hidden_intermediate_height_rejects :
    run 7 0 ⟨7, 10⟩ [⟨8, 10, 11⟩, ⟨9, 11, 12⟩] = none := by decide

end Proofs.AssetTransferEpochPositionV1
