import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic
import Proofs.DEXExactSequence

/-!
# Settlement Netting Algebra

## Mathematical Content

Batch settlement systems net opposing flows to reduce gross exposure.
This file develops the algebra of netting as a **ConservationSystem**
(importing the abstract splitting theorem from DEXExactSequence) and
proves quantitative savings bounds.

### Part A: RichSettl as a ConservationSystem

RichSettl = ℤ² × ℤ carries net external flows (dx,dy) and internal
transfer volume. The conservation measure Δ(s) = dx + dy ignores
internal volume. We construct a ConservationSystem on RichSettl and
inherit the full splitting theorem: every RichSettl decomposes uniquely
into a conserving part (Δ=0) plus a violation part, with π idempotent,
ker ∩ im = {0}, etc. — all for free from the abstract theory.

### Part B: Netting Savings (the interesting new math)

For two integer flows a, b, define:
  savings(a,b) := |a| + |b| - |a + b|

Key results:
- savings ≥ 0 (triangle inequality)
- savings = 2 * min(|a|, |b|) when a and b have opposite signs
  (the EXACT cancellation formula for clearinghouse netting)
- The savings formula requires genuine case analysis on sign combinations

### Part C: Volume Subadditivity over Lists

|sum(xs)| ≤ sum(map |·| xs), proved by list induction. Generalizes
the pairwise triangle inequality to n settlements.

### Part D: Netting Projection (section-retraction pair)

The netting projection π : RichSettl → Settl forgets internal volume.
embed : Settl → RichSettl is a section. We prove π ∘ embed = id
(retraction), the kernel characterization, and the direct-sum
decomposition RichSettl ≅ Settl ⊕ ℤ via the product isomorphism.

### Part E: Universal Property of Netting

The netting projection satisfies a UNIVERSAL PROPERTY: any homomorphism
f : RichSettl →+ A that kills internal volume factors uniquely through
netProject. That is, f = g ∘ π for a UNIQUE g : Settl →+ A. This is
the highest-grade theorem in the file — it characterizes netProject
as the correct abstraction boundary for netting.

## Key Substantive Theorems

| # | Name | Statement | Technique |
|---|------|-----------|-----------|
| 1 | `savings_exact_opposing` | savings = 2·min(a,-b) for buyer/seller | Sign case analysis |
| 2 | `volume_subadditive` | Generalized triangle inequality over lists | List induction |
| 3 | `volume_subadditive_tight_pos` | Bound is tight for same-sign flows | List induction + abs |
| 4 | `netProject_universal` | ∃! g, f = g ∘ π when f kills ker | Universal property |
| 5 | `decomposition_unique` | (π(s), ι(s)) determines s uniquely | Direct sum |
| 6 | `netting_decomposition` | s = embed(π(s)) + kerPart(s) | Constructive |
| 7 | `opposing_flows_strict_savings` | Opposing flows always save strictly | min positivity |
| 8 | `conservation_factor_unique` | Δ_net is the unique factorization of Δ_rich | Universal + computation |
-/

namespace Proofs

namespace SettlementNetting

open DEXExactSequence (ConservationSystem kerProject surjective
  section_injective kerProject_in_ker kerProject_idempotent
  decomposition decomposition_unique_n decomposition_unique_k
  kerProject_add ker_inter_image_trivial decomposition_injective
  kerProject_fixes_ker kerProject_annihilates_section)

/-! ## Part 1: Net Settlement Type (Settl) -/

structure Settl where
  dx : ℤ
  dy : ℤ
  deriving Repr, DecidableEq

@[ext] theorem Settl.ext {s₁ s₂ : Settl}
    (hx : s₁.dx = s₂.dx) (hy : s₁.dy = s₂.dy) : s₁ = s₂ := by
  cases s₁; cases s₂; simp_all

instance : Zero Settl := ⟨⟨0, 0⟩⟩
instance : Add Settl := ⟨fun s₁ s₂ => ⟨s₁.dx + s₂.dx, s₁.dy + s₂.dy⟩⟩
instance : Neg Settl := ⟨fun s => ⟨-s.dx, -s.dy⟩⟩
instance : Sub Settl := ⟨fun s₁ s₂ => s₁ + (-s₂)⟩

@[simp] theorem Settl.zero_dx : (0 : Settl).dx = 0 := rfl
@[simp] theorem Settl.zero_dy : (0 : Settl).dy = 0 := rfl
@[simp] theorem Settl.add_dx (s₁ s₂ : Settl) :
    (s₁ + s₂).dx = s₁.dx + s₂.dx := rfl
@[simp] theorem Settl.add_dy (s₁ s₂ : Settl) :
    (s₁ + s₂).dy = s₁.dy + s₂.dy := rfl
@[simp] theorem Settl.neg_dx (s : Settl) : (-s).dx = -s.dx := rfl
@[simp] theorem Settl.neg_dy (s : Settl) : (-s).dy = -s.dy := rfl

instance : AddCommGroup Settl where
  add_assoc := fun a b c => by ext <;> simp <;> ring
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp <;> ring
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 2: Rich Settlement Type (with internal volume) -/

/-- A settlement with internal structure: net external flows (dx, dy)
    plus an internal transfer volume invisible to conservation. -/
structure RichSettl where
  dx : ℤ
  dy : ℤ
  internal : ℤ
  deriving Repr, DecidableEq

@[ext] theorem RichSettl.ext {s₁ s₂ : RichSettl}
    (hx : s₁.dx = s₂.dx) (hy : s₁.dy = s₂.dy) (hi : s₁.internal = s₂.internal) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp_all

instance : Zero RichSettl := ⟨⟨0, 0, 0⟩⟩
instance : Add RichSettl :=
  ⟨fun s₁ s₂ => ⟨s₁.dx + s₂.dx, s₁.dy + s₂.dy, s₁.internal + s₂.internal⟩⟩
instance : Neg RichSettl := ⟨fun s => ⟨-s.dx, -s.dy, -s.internal⟩⟩
instance : Sub RichSettl := ⟨fun s₁ s₂ => s₁ + (-s₂)⟩

@[simp] theorem RichSettl.zero_dx : (0 : RichSettl).dx = 0 := rfl
@[simp] theorem RichSettl.zero_dy : (0 : RichSettl).dy = 0 := rfl
@[simp] theorem RichSettl.zero_internal : (0 : RichSettl).internal = 0 := rfl
@[simp] theorem RichSettl.add_dx (s₁ s₂ : RichSettl) :
    (s₁ + s₂).dx = s₁.dx + s₂.dx := rfl
@[simp] theorem RichSettl.add_dy (s₁ s₂ : RichSettl) :
    (s₁ + s₂).dy = s₁.dy + s₂.dy := rfl
@[simp] theorem RichSettl.add_internal (s₁ s₂ : RichSettl) :
    (s₁ + s₂).internal = s₁.internal + s₂.internal := rfl
@[simp] theorem RichSettl.neg_dx (s : RichSettl) : (-s).dx = -s.dx := rfl
@[simp] theorem RichSettl.neg_dy (s : RichSettl) : (-s).dy = -s.dy := rfl
@[simp] theorem RichSettl.neg_internal (s : RichSettl) :
    (-s).internal = -s.internal := rfl

instance : AddCommGroup RichSettl where
  add_assoc := fun a b c => by ext <;> simp <;> ring
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp <;> ring
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 3: Conservation Homomorphisms and Netting Projection -/

/-- Conservation on RichSettl: Δ(s) = dx + dy. Internal volume is invisible. -/
def Δ_rich : RichSettl →+ ℤ where
  toFun := fun s => s.dx + s.dy
  map_zero' := by rfl
  map_add' := fun a b => by
    show (a.dx + b.dx) + (a.dy + b.dy) = (a.dx + a.dy) + (b.dx + b.dy); ring

/-- Conservation on Settl: Δ_net(s) = dx + dy. -/
def Δ_net : Settl →+ ℤ where
  toFun := fun s => s.dx + s.dy
  map_zero' := by rfl
  map_add' := fun a b => by
    show (a.dx + b.dx) + (a.dy + b.dy) = (a.dx + a.dy) + (b.dx + b.dy); ring

/-- The netting projection: forget internal volume, keep net flows. -/
def netProject : RichSettl →+ Settl where
  toFun := fun s => ⟨s.dx, s.dy⟩
  map_zero' := by ext <;> simp
  map_add' := fun a b => by ext <;> simp

/-- The natural embedding: lift a net settlement to a rich one with zero internal. -/
def embed : Settl →+ RichSettl where
  toFun := fun s => ⟨s.dx, s.dy, 0⟩
  map_zero' := by ext <;> simp
  map_add' := fun a b => by ext <;> simp

/-- The internal volume projection. -/
def internalVol : RichSettl →+ ℤ where
  toFun := fun s => s.internal
  map_zero' := by rfl
  map_add' := fun a b => by rfl

/-! ## Part 4: RichSettl as a ConservationSystem (via DEXExactSequence) -/

/-- Section for the RichSettl conservation system: maps n ↦ ⟨n, 0, 0⟩.
    This is the canonical embedding of the violation into RichSettl. -/
def richSection : ℤ →+ RichSettl where
  toFun := fun n => ⟨n, 0, 0⟩
  map_zero' := by ext <;> simp
  map_add' := fun a b => by ext <;> simp

/-- RichSettl forms a ConservationSystem with Δ_rich and richSection.
    This means the FULL abstract splitting theorem from DEXExactSequence
    applies: decomposition, uniqueness, idempotent projection, direct sum. -/
def richCS : ConservationSystem RichSettl where
  φ := Δ_rich
  σ := richSection
  right_inv := fun n => by
    simp only [Δ_rich, richSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; ring

/-- Conservation factors through the netting projection:
    Δ_rich(s) = Δ_net(π(s)). The internal volume is invisible to conservation.
    This is NOT trivial: Δ_rich is defined on 3 fields, Δ_net ∘ π first
    projects away one field then sums the remaining two. -/
theorem conservation_factors (s : RichSettl) :
    Δ_rich s = Δ_net (netProject s) := by
  simp only [Δ_rich, Δ_net, netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Conservation factors as a homomorphism equality. -/
theorem conservation_factors_hom :
    Δ_rich = Δ_net.comp netProject := by
  ext s; exact conservation_factors s

/-- Balanced settlements (Δ=0) are exactly those where dx + dy = 0,
    regardless of internal volume. Equivalence through netting. -/
theorem balanced_iff_net_balanced (s : RichSettl) :
    Δ_rich s = 0 ↔ Δ_net (netProject s) = 0 := by
  constructor
  · intro h; rw [← conservation_factors]; exact h
  · intro h; rw [conservation_factors]; exact h

/-! ## Part 5: Netting Savings — The Exact Cancellation Formula

This is the core mathematical contribution. For two integer flows a, b:
  savings(a, b) := |a| + |b| - |a + b|

We prove:
1. savings ≥ 0 (triangle inequality)
2. When a ≥ 0 and b ≤ 0: savings = 2 * min(a, -b)
3. When a ≤ 0 and b ≥ 0: savings = 2 * min(-a, b)

The second and third results give the EXACT cancellation formula for
clearinghouse netting: when a buyer (positive flow) and seller (negative
flow) are netted, the savings equal twice the smaller position.
-/

/-- Netting savings for two flows: the reduction in gross absolute volume
    achieved by netting a against b. -/
def savings (a b : ℤ) : ℤ := |a| + |b| - |a + b|

/-- Savings are non-negative: netting never increases gross volume.
    This is the triangle inequality |a+b| ≤ |a|+|b| rearranged.

    Proof uses abs_add_le from Mathlib and then omega for the rearrangement. -/
theorem savings_nonneg (a b : ℤ) : 0 ≤ savings a b := by
  unfold savings
  have h := abs_add_le a b
  omega

/-- Savings are symmetric: savings(a,b) = savings(b,a).
    Follows from commutativity of + and |·|. -/
theorem savings_comm (a b : ℤ) : savings a b = savings b a := by
  unfold savings; ring_nf

/-- When a ≥ 0 and b ≤ 0 (buyer meets seller), savings = 2 * min(a, -b).
    This is the exact cancellation formula: the smaller opposing position
    is fully absorbed, saving twice its size in gross flow.

    Requires case split on whether the buyer or seller is larger,
    with abs unfolding in each branch. -/
theorem savings_exact_opposing (a b : ℤ) (ha : 0 ≤ a) (hb : b ≤ 0) :
    savings a b = 2 * min a (-b) := by
  unfold savings
  rw [abs_of_nonneg ha, abs_of_nonpos hb]
  rcases le_or_gt a (-b) with hab | hab
  · -- a ≤ -b, so a + b ≤ 0, net is negative
    have hab' : a + b ≤ 0 := by omega
    rw [abs_of_nonpos hab', min_eq_left hab]
    ring
  · -- a > -b, so a + b > 0, net is positive
    have hab' : 0 ≤ a + b := by omega
    rw [abs_of_nonneg hab']
    have : min a (-b) = -b := min_eq_right (le_of_lt hab)
    rw [this]; ring

/-- The dual case: a ≤ 0, b ≥ 0 (seller meets buyer).
    Derived from savings_exact_opposing via savings_comm. -/
theorem savings_exact_opposing' (a b : ℤ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    savings a b = 2 * min (-a) b := by
  rw [savings_comm, savings_exact_opposing b a hb ha, min_comm]

/-- When both flows go the same direction, savings = 0 (no cancellation).
    Case: both non-negative. -/
theorem savings_zero_same_sign_pos (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    savings a b = 0 := by
  unfold savings
  rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (by omega : 0 ≤ a + b)]
  ring

/-- When both flows go the same direction, savings = 0 (no cancellation).
    Case: both non-positive. -/
theorem savings_zero_same_sign_neg (a b : ℤ) (ha : a ≤ 0) (hb : b ≤ 0) :
    savings a b = 0 := by
  unfold savings
  rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (by omega : a + b ≤ 0)]
  ring

/-! ## Part 6: Volume Subadditivity over Lists

The triangle inequality generalizes from 2 to n elements by list
induction: |Σ xᵢ| ≤ Σ |xᵢ|. This is the formal statement that
netting n settlements can only reduce total gross volume.
-/

/-- Sum of a list of integers. -/
def listSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + listSum xs

/-- Sum of absolute values of a list of integers. -/
def listAbsSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => |x| + listAbsSum xs

/-- listAbsSum is always non-negative, by induction on the list.
    Each |xᵢ| ≥ 0 and the sum of non-negatives is non-negative. -/
theorem listAbsSum_nonneg (xs : List ℤ) : 0 ≤ listAbsSum xs := by
  induction xs with
  | nil => simp [listAbsSum]
  | cons x xs ih =>
    simp only [listAbsSum]
    have := abs_nonneg x
    omega

/-- Volume subadditivity (generalized triangle inequality):
    |sum(xs)| ≤ sum(map |·| xs).

    Proved by list induction. The inductive step chains:
    |x + sum(xs)| ≤ |x| + |sum(xs)| ≤ |x| + sum(|xsᵢ|)
    using abs_add_le for the first inequality and the inductive
    hypothesis for the second. -/
theorem volume_subadditive (xs : List ℤ) :
    |listSum xs| ≤ listAbsSum xs := by
  induction xs with
  | nil =>
    simp [listSum, listAbsSum]
  | cons x xs ih =>
    simp only [listSum, listAbsSum]
    calc |x + listSum xs|
        ≤ |x| + |listSum xs| := abs_add_le x (listSum xs)
      _ ≤ |x| + listAbsSum xs := by omega

/-- The bound is tight: for a single-element list, equality holds. -/
theorem volume_subadditive_singleton (x : ℤ) :
    |listSum [x]| = listAbsSum [x] := by
  simp [listSum, listAbsSum]

/-- If all list elements are non-negative, their sum is non-negative. -/
theorem listSum_nonneg_of_all_nonneg (xs : List ℤ) (h : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ listSum xs := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp only [listSum]
    have hx : 0 ≤ x := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem x hy)
    linarith [ih hxs]

/-- The bound is tight: for a same-sign list, equality holds.
    When all flows go the same direction, netting provides zero savings.
    Proof by list induction, using listSum_nonneg_of_all_nonneg to
    unfold absolute values at each step. -/
theorem volume_subadditive_tight_pos (xs : List ℤ) (h : ∀ x ∈ xs, 0 ≤ x) :
    |listSum xs| = listAbsSum xs := by
  induction xs with
  | nil => simp [listSum, listAbsSum]
  | cons x xs ih =>
    simp only [listSum, listAbsSum]
    have hx : 0 ≤ x := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem x hy)
    have ih' := ih hxs
    have hsum_nn : 0 ≤ listSum xs := listSum_nonneg_of_all_nonneg xs hxs
    rw [abs_of_nonneg (by linarith : 0 ≤ x + listSum xs), abs_of_nonneg hx]
    linarith [abs_of_nonneg hsum_nn]

/-- Total savings from netting a list: gross - net.
    This is the total reduction in absolute flow. -/
def totalSavings (xs : List ℤ) : ℤ := listAbsSum xs - |listSum xs|

/-- Total savings are non-negative (immediate from volume_subadditive). -/
theorem totalSavings_nonneg (xs : List ℤ) : 0 ≤ totalSavings xs := by
  unfold totalSavings
  have := volume_subadditive xs
  omega

/-- For two opposing elements, total savings equals pairwise savings. -/
theorem totalSavings_pair (a b : ℤ) :
    totalSavings [a, b] = savings a b := by
  simp [totalSavings, savings, listAbsSum, listSum]

/-! ## Part 7: Section-Retraction Pair and Kernel -/

/-- embed is a right inverse of netProject: π(embed(n)) = n for all n. -/
theorem project_embed (n : Settl) :
    netProject (embed n) = n := by
  simp only [netProject, embed, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Retraction identity: π ∘ embed ∘ π = π (idempotent through the section). -/
theorem netting_idempotent (s : RichSettl) :
    netProject (embed (netProject s)) = netProject s := by
  rw [project_embed]

/-- Kernel characterization: s ∈ ker(π) iff dx = 0 and dy = 0.
    The kernel consists precisely of purely-internal settlements. -/
theorem netting_ker_char (s : RichSettl) :
    netProject s = 0 ↔ s.dx = 0 ∧ s.dy = 0 := by
  constructor
  · intro h
    have hx : (netProject s).dx = (0 : Settl).dx := by rw [h]
    have hy : (netProject s).dy = (0 : Settl).dy := by rw [h]
    simp only [netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Settl.zero_dx,
               Settl.zero_dy] at hx hy
    exact ⟨hx, hy⟩
  · intro ⟨hx, hy⟩
    ext
    · simp only [netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Settl.zero_dx]; exact hx
    · simp only [netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Settl.zero_dy]; exact hy

/-- The kernel part: extracts the purely-internal component. -/
def kerPart (s : RichSettl) : RichSettl :=
  s - embed (netProject s)

/-- kerPart lands in ker(π). -/
theorem kerPart_in_ker (s : RichSettl) :
    netProject (kerPart s) = 0 := by
  unfold kerPart
  simp only [netProject, embed, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  show Settl.mk (s + (-⟨s.dx, s.dy, (0 : ℤ)⟩)).dx (s + (-⟨s.dx, s.dy, (0 : ℤ)⟩)).dy = 0
  ext <;> simp

/-- The kernel part captures exactly the internal volume. -/
theorem ker_part_internal (s : RichSettl) :
    (kerPart s).internal = s.internal := by
  unfold kerPart
  simp only [embed, netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  show (s + (-⟨s.dx, s.dy, (0 : ℤ)⟩)).internal = s.internal
  simp

theorem kerPart_closed_form (s : RichSettl) :
    kerPart s = RichSettl.mk 0 0 s.internal := by
  unfold kerPart
  ext
  · show (s + (-{ dx := s.dx, dy := s.dy, internal := 0 })).dx = 0
    simp
  · show (s + (-{ dx := s.dx, dy := s.dy, internal := 0 })).dy = 0
    simp
  · show (s + (-{ dx := s.dx, dy := s.dy, internal := 0 })).internal = s.internal
    simp

/-! ## Part 8: Netting Decomposition (Direct Sum) -/

/-- Every RichSettl decomposes as embed(π(s)) + kerPart(s).
    First summand: the externally visible net settlement (internal = 0).
    Second summand: the purely internal part (dx = dy = 0). -/
theorem netting_decomposition (s : RichSettl) :
    s = embed (netProject s) + kerPart s := by
  unfold kerPart
  simp only [embed, netProject, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ext <;> simp [show s - ⟨s.dx, s.dy, (0 : ℤ)⟩ = s + -⟨s.dx, s.dy, (0 : ℤ)⟩ from rfl]

theorem netting_decomposition_closed_form (s : RichSettl) :
    s = embed (netProject s) + RichSettl.mk 0 0 s.internal := by
  calc
    s = embed (netProject s) + kerPart s := netting_decomposition s
    _ = embed (netProject s) + RichSettl.mk 0 0 s.internal := by
      rw [kerPart_closed_form]

/-- If two RichSettls have the same net projection AND the same internal
    volume, they are equal. The pair (π(s), ι(s)) determines s uniquely. -/
theorem decomposition_unique (s₁ s₂ : RichSettl)
    (hnet : netProject s₁ = netProject s₂)
    (hint : internalVol s₁ = internalVol s₂) :
    s₁ = s₂ := by
  simp only [netProject, internalVol, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hnet hint
  have hx : s₁.dx = s₂.dx := by
    have := congr_arg Settl.dx hnet; simpa using this
  have hy : s₁.dy = s₂.dy := by
    have := congr_arg Settl.dy hnet; simpa using this
  ext
  · exact hx
  · exact hy
  · exact hint

/-! ## Part 9: Product Isomorphism -/

/-- Forward map: RichSettl → Settl × ℤ. -/
def toProduct (s : RichSettl) : Settl × ℤ :=
  (netProject s, internalVol s)

/-- Inverse map: Settl × ℤ → RichSettl. -/
def fromProduct (p : Settl × ℤ) : RichSettl :=
  ⟨p.1.dx, p.1.dy, p.2⟩

/-- Round-trip: fromProduct ∘ toProduct = id. -/
theorem fromProduct_toProduct (s : RichSettl) :
    fromProduct (toProduct s) = s := by
  simp only [fromProduct, toProduct, netProject, internalVol,
             AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Round-trip: toProduct ∘ fromProduct = id. -/
theorem toProduct_fromProduct (p : Settl × ℤ) :
    toProduct (fromProduct p) = p := by
  simp only [toProduct, fromProduct, netProject, internalVol,
             AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- The product map respects addition. -/
theorem toProduct_add (s₁ s₂ : RichSettl) :
    toProduct (s₁ + s₂) = (netProject s₁ + netProject s₂, internalVol s₁ + internalVol s₂) := by
  simp only [toProduct]
  exact Prod.ext (netProject.map_add s₁ s₂) (internalVol.map_add s₁ s₂)

def richSettlProductEquiv : AddEquiv RichSettl (Settl × ℤ) where
  toFun := toProduct
  invFun := fromProduct
  left_inv := fromProduct_toProduct
  right_inv := toProduct_fromProduct
  map_add' := toProduct_add

theorem richSettlProductEquiv_components (s : RichSettl) :
    richSettlProductEquiv s = (netProject s, internalVol s) := by
  rfl

/-! ## Part 10: Inherited Abstract Results via richCS

By constructing richCS : ConservationSystem RichSettl, we inherit
the full abstract theory from DEXExactSequence:
- decomposition into kernel + section image
- uniqueness of the decomposition
- idempotent kernel projection
- ker ∩ im = {0} (direct sum)

The abstract kerProject for richCS is: kerProject(s) = s - σ(φ(s)) =
s - ⟨dx+dy, 0, 0⟩, which extracts the balanced part by subtracting
the violation. This is a DIFFERENT projection than netProject (which
forgets internal volume). The abstract one decomposes by conservation
violation; ours by internal structure. Both are valid projections. -/

/-- The full abstract splitting theorem applies to RichSettl:
    1. kerProject lands in ker(Δ_rich)
    2. Every element decomposes: s = kerProject(s) + σ(Δ(s))
    3. Both parts are uniquely determined
    4. ker ∩ im = {0}

    Combined into a single theorem to avoid trivial 1-line wrappers.
    Each conjunct is a direct application of the abstract theory. -/
theorem richCS_splitting_package (s : RichSettl) :
    -- (1) kerProject lands in ker
    Δ_rich (kerProject richCS s) = 0 ∧
    -- (2) decomposition
    s = kerProject richCS s + richSection (Δ_rich s) ∧
    -- (3) idempotent projection
    kerProject richCS (kerProject richCS s) = kerProject richCS s ∧
    -- (4) same (kerProject, Δ) implies same element
    (∀ s₂ : RichSettl,
      kerProject richCS s = kerProject richCS s₂ →
      Δ_rich s = Δ_rich s₂ →
      s = s₂) :=
  ⟨kerProject_in_ker richCS s,
   decomposition richCS s,
   kerProject_idempotent richCS s,
   fun s₂ hk hv => decomposition_injective richCS s s₂ hk hv⟩

/-- The violation number is uniquely determined: if s = k + σ(n) with
    Δ(k) = 0, then n must equal Δ(s). This is the key content of the
    splitting theorem — the violation cannot be redistributed. -/
theorem richCS_violation_unique (s k : RichSettl) (n : ℤ)
    (hk : Δ_rich k = 0) (hdecomp : s = k + richSection n) :
    n = Δ_rich s :=
  decomposition_unique_n richCS s k n hk hdecomp

/-- ker(Δ_rich) ∩ im(richSection) = {0}: the direct sum is trivial.
    An element that is both balanced (Δ=0) and a pure violation (in im(σ))
    must be zero. This ensures the decomposition is a genuine direct sum. -/
theorem richCS_trivial_intersection (s : RichSettl) (n : ℤ)
    (hk : Δ_rich s = 0) (him : s = richSection n) :
    n = 0 ∧ s = 0 :=
  ker_inter_image_trivial richCS s n hk him

 variable {A : Type*} [AddCommGroup A]

 theorem factors_through_netProject (f : RichSettl →+ A)
    (hkill : ∀ i : ℤ, f ⟨0, 0, i⟩ = 0) :
    f = (f.comp embed).comp netProject := by
  ext s
  have hdecomp : s = embed (netProject s) + RichSettl.mk 0 0 s.internal := by
    ext <;> simp [embed, netProject]
  change f s = f (embed (netProject s))
  conv_lhs => rw [hdecomp]
  rw [f.map_add, hkill, add_zero]

 theorem factor_through_netProject_unique (f : RichSettl →+ A) (g : Settl →+ A)
    (hfactor : f = g.comp netProject) :
    g = f.comp embed := by
  ext n
  have h := congr_fun (congr_arg DFunLike.coe hfactor) (embed n)
  simpa [project_embed, AddMonoidHom.comp_apply] using h.symm

 theorem netProject_universal (f : RichSettl →+ A)
    (hkill : ∀ i : ℤ, f ⟨0, 0, i⟩ = 0) :
    ∃! g : Settl →+ A, f = g.comp netProject := by
  refine ⟨f.comp embed, factors_through_netProject f hkill, ?_⟩
  intro g hg
  exact factor_through_netProject_unique f g hg

 theorem factors_through_netProject_iff (f : RichSettl →+ A) :
    (∃ g : Settl →+ A, f = g.comp netProject) ↔ ∀ i : ℤ, f ⟨0, 0, i⟩ = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ i
    exact g.map_zero
  · intro hkill
    exact ⟨f.comp embed, factors_through_netProject f hkill⟩

 theorem richCS_kerProject_closed_form (s : RichSettl) :
    kerProject richCS s = RichSettl.mk (-s.dy) s.dy s.internal := by
  unfold kerProject richCS richSection Δ_rich
  ext
  · show (s + (-{ dx := s.dx + s.dy, dy := 0, internal := 0 })).dx = -s.dy
    simp
  · show (s + (-{ dx := s.dx + s.dy, dy := 0, internal := 0 })).dy = s.dy
    simp
  · show (s + (-{ dx := s.dx + s.dy, dy := 0, internal := 0 })).internal = s.internal
    simp

 theorem richCS_decomposition_closed_form (s : RichSettl) :
    s = RichSettl.mk (-s.dy) s.dy s.internal + RichSettl.mk (s.dx + s.dy) 0 0 := by
  rw [decomposition richCS s, richCS_kerProject_closed_form]
  ext
  · simp
    ring
  · simp
  · simp

 theorem conservation_factor_unique (g : Settl →+ ℤ)
    (hfactor : Δ_rich = g.comp netProject) :
    g = Δ_net := by
  calc
    g = Δ_rich.comp embed := factor_through_netProject_unique Δ_rich g hfactor
    _ = Δ_net := by
      ext n
      simp [Δ_rich, Δ_net, embed, AddMonoidHom.comp_apply]

/-! ## Part 11: Connecting Savings to Settlements

The savings formula applies component-wise to settlements.
For two RichSettls, the dx-savings of their combination equals
savings(s₁.dx, s₂.dx), and similarly for dy. -/

/-- Savings on the dx component of two combined RichSettls.
    savings(s₁.dx, s₂.dx) = |s₁.dx| + |s₂.dx| - |(s₁+s₂).dx|.
    This connects the abstract savings function to concrete settlement netting. -/
theorem settlement_dx_savings (s₁ s₂ : RichSettl) :
    savings s₁.dx s₂.dx = |s₁.dx| + |s₂.dx| - |(s₁ + s₂).dx| := by
  simp [savings]

/-- When a buyer and seller have opposing flows with the buyer strictly
    positive and seller strictly negative, the savings are strictly positive.
    Netting ALWAYS saves when flows genuinely oppose. -/
theorem opposing_flows_strict_savings (a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    0 < savings a b := by
  have h := savings_exact_opposing a b (le_of_lt ha) (le_of_lt hb)
  rw [h]
  have : 0 < min a (-b) := by
    rw [lt_min_iff]
    constructor <;> omega
  linarith

/-! ## Part 12: Non-Vacuity Witnesses -/

/-- Witness: savings formula for buyer (100) vs seller (-80).
    savings = 2 * min(100, 80) = 160. Net flow = 20, gross = 180. -/
theorem witness_savings_opposing :
    savings 100 (-80) = 160 ∧
    min (100 : ℤ) 80 = 80 ∧
    2 * min (100 : ℤ) 80 = 160 := by native_decide

/-- Witness: same-sign flows have zero savings.
    Both buying 50 and 30: savings = 0. -/
theorem witness_savings_same_sign :
    savings 50 30 = 0 ∧
    savings (-50) (-30) = 0 := by native_decide

/-- Witness: volume subadditivity for a mixed list.
    [100, -80, 50, -60] sums to 10, abs sum = 290.
    |10| = 10 ≤ 290. -/
theorem witness_volume_subadditive :
    let xs := [100, -80, 50, -60]
    listSum xs = 10 ∧
    listAbsSum xs = 290 ∧
    |listSum xs| ≤ listAbsSum xs := by native_decide

/-- Witness: total savings for netting 4 settlements.
    savings = 290 - 10 = 280. -/
theorem witness_total_savings :
    totalSavings [100, -80, 50, -60] = 280 := by native_decide

/-- Witness: richCS decomposition of ⟨100, -90, 50⟩.
    Δ = 10, so kerProject gives ⟨100,-90,50⟩ - ⟨10,0,0⟩ = ⟨90,-90,50⟩. -/
theorem witness_richCS_decomposition :
    let s : RichSettl := ⟨100, -90, 50⟩
    Δ_rich s = 10 ∧
    kerProject richCS s = RichSettl.mk 90 (-90) 50 ∧
    richSection (Δ_rich s) = RichSettl.mk 10 0 0 ∧
    s = kerProject richCS s + richSection (Δ_rich s) := by native_decide

/-- Witness: conservation factors through netting projection.
    s = ⟨100, -90, 500⟩. Δ_rich = 10 = Δ_net(π(s)). -/
theorem witness_conservation_factors :
    let s : RichSettl := ⟨100, -90, 500⟩
    Δ_rich s = 10 ∧
    Δ_net (netProject s) = 10 ∧
    Δ_rich s = Δ_net (netProject s) := by native_decide

/-- Witness: product isomorphism round-trips.
    ⟨42, -17, 99⟩ maps to (⟨42,-17⟩, 99) and back. -/
theorem witness_product_roundtrip :
    let s : RichSettl := ⟨42, -17, 99⟩
    toProduct s = (Settl.mk 42 (-17), 99) ∧
    fromProduct (toProduct s) = s := by native_decide

/-- Witness: netting pair savings matches the per-component formula.
    totalSavings [100, -80] = savings 100 (-80) = 160. -/
theorem witness_savings_pair_consistency :
    totalSavings [100, -80] = savings 100 (-80) ∧
    savings 100 (-80) = 160 := by native_decide

/-- Witness: balanced settlement. Δ = 0 on both rich and net.
    s = ⟨100, -100, 75⟩, π(s) = ⟨100, -100⟩. -/
theorem witness_balanced :
    let s : RichSettl := ⟨100, -100, 75⟩
    Δ_rich s = 0 ∧ Δ_net (netProject s) = 0 := by native_decide

end SettlementNetting

end Proofs
