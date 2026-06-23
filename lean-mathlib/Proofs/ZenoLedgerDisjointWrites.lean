import Init.Data.List.Basic
import Init.Data.List.Pairwise
import Init.Data.List.Perm

namespace ZenoDEX.ZenoLedgerDisjointWrites

/-!
This file isolates the local scheduling fact used by ZenoLedger replay:
assignments to distinct state cells commute. The runtime conflict graph computes
richer read/write sets, but this small theorem captures the key-cell case that
underlies deterministic parallel replay.

Aristotle source packet: `768d14a7-c33c-4a13-b6b7-3e791c3a17bf`.
The packet built locally, and this integrated version keeps the theorem surfaces
unchanged while placing the result in the repo proof tree.
-/

structure Write (Key : Type) where
  key : Key
  value : Nat

def State (Key : Type) := Key → Nat

def applyWrite {Key : Type} [DecidableEq Key]
    (w : Write Key) (st : State Key) : State Key :=
  fun k => if k = w.key then w.value else st k

def applyWrites {Key : Type} [DecidableEq Key] :
    List (Write Key) → State Key → State Key
  | [], st => st
  | w :: rest, st => applyWrites rest (applyWrite w st)

def PairwiseDistinctKeys {Key : Type} (xs : List (Write Key)) : Prop :=
  xs.Pairwise (fun a b => a.key ≠ b.key)

def SameValueOnKey {Key : Type} (a b : Write Key) : Prop :=
  a.key = b.key → a.value = b.value

/-- Assignments to distinct keys commute extensionally. -/
theorem applyWrite_commutes_of_distinct
    {Key : Type} [DecidableEq Key]
    (a b : Write Key)
    (hneq : a.key ≠ b.key)
    (st : State Key) :
    applyWrite a (applyWrite b st) = applyWrite b (applyWrite a st) := by
  funext k
  by_cases hka : k = a.key <;> by_cases hkb : k = b.key <;> simp_all [applyWrite]

/--
Pairwise-distinct writes can be reordered without changing the final state.

This is the concrete key-update version of the conflict-graph confluence
obligation: once a batch is partitioned into disjoint write cells, any replay
order inside that independent set produces the same state.
-/
theorem applyWrites_perm_invariant_of_pairwise_distinct
    {Key : Type} [DecidableEq Key]
    {xs ys : List (Write Key)}
    (hperm : xs.Perm ys)
    (hdistinct : PairwiseDistinctKeys xs)
    (st : State Key) :
    applyWrites xs st = applyWrites ys st := by
  induction hperm generalizing st with
  | nil => rfl
  | cons x _ ih =>
      simp only [applyWrites]
      exact ih ((List.pairwise_cons.mp hdistinct).2) (applyWrite x st)
  | swap x y _ =>
      simp only [applyWrites]
      have hd := hdistinct
      unfold PairwiseDistinctKeys at hd
      have hyx : y.key ≠ x.key := by
        rw [List.pairwise_cons] at hd
        exact hd.1 x (List.mem_cons.mpr (Or.inl rfl))
      congr 1
      exact applyWrite_commutes_of_distinct x y (Ne.symm hyx) st
  | trans h1 _ ih1 ih2 =>
      have hdistinct2 : PairwiseDistinctKeys _ :=
        (h1.pairwise_iff (fun {a b} h => Ne.symm h)).mp hdistinct
      exact (ih1 hdistinct st).trans (ih2 hdistinct2 st)

/--
Duplicate writes to the same key commute when they write the same value.
This models idempotent duplicate proof chunks.
-/
theorem applyWrite_commutes_of_same_key_same_value
    {Key : Type} [DecidableEq Key]
    (a b : Write Key)
    (hsame : a.key = b.key)
    (hvalue : a.value = b.value)
    (st : State Key) :
    applyWrite a (applyWrite b st) = applyWrite b (applyWrite a st) := by
  funext k
  simp [applyWrite, hsame, hvalue]

end ZenoDEX.ZenoLedgerDisjointWrites
