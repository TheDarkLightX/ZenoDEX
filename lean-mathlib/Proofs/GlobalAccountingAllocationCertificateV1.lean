import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Bounded model of `GlobalAccountingAllocationCertificateV1`

Research-only, bounded model of the sidecar checker implemented in
`src/core/global_accounting_allocation_certificate_v1.py` and its Rust twin.
Three lanes, two control domains, and two claimants stand for the twelve lanes and
the unbounded vocabulary of the running code; amounts are natural numbers, so
finite-width arithmetic, canonical bytes, roots, and authority are outside this
model (the checked-`u128` folds and root recomputation are replayed, not proved).

A lane fragment classifies the atoms a lane controls into claimant entitlements,
unencumbered reserves, and pending external obligations, and binds its open
terminal claims to entitlements of the same claimant and domain.  The certificate
relation is what the checker accepts: every lane passes its producer gate,
partitions its controlled atoms exactly once, and bounds its terminal claims; the
lane rows sum to the global tables; and the lane aggregates equal global custody.

The theorems derive the normative partition
`controlled = claimant_entitlements + unencumbered_reserves + pending_external`
at the global level from the lane-level relation, the same-domain backing and
open-terminal coverage relations of `GlobalClaimantCustodyRelationV1`, the exact
current-profile custody equality when reserves and external obligations are zero,
and the fact that without a receipt-backed producer the only accepted certificate
is the registered-empty one.  Counterexamples show that each conjunct is
load-bearing: a reserve never stands in for a missing entitlement.
-/

namespace Proofs
namespace GlobalAccountingAllocationCertificateV1

inductive Lane where
  | l0
  | l1
  | l2
  deriving DecidableEq, Repr

inductive Domain where
  | d0
  | d1
  deriving DecidableEq, Repr

inductive Claimant where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- Sum over the three bounded lanes. -/
def sumLanes (f : Lane → Nat) : Nat :=
  f .l0 + f .l1 + f .l2

/-- Sum over the two bounded claimants. -/
def sumClaimants (f : Claimant → Nat) : Nat :=
  f .alice + f .bob

/-- One lane's fragment: its producer flags and its classified rows, keyed by
control domain (the controlling principal is folded into the domain). -/
structure LaneFragment where
  enabled : Bool
  receiptBacked : Bool
  controlled : Domain → Nat
  entitlement : Claimant → Domain → Nat
  reserve : Domain → Nat
  external : Domain → Nat
  terminal : Claimant → Domain → Nat

/-- The global economic tables the certificate is checked against. -/
structure Tables where
  custody : Domain → Nat
  liability : Claimant → Domain → Nat
  reserves : Domain → Nat
  external : Domain → Nat
  openTerminal : Claimant → Domain → Nat

/-- A fragment with no rows at all (`is_empty` in the running code). -/
def FragmentEmpty (f : LaneFragment) : Prop :=
  (∀ d, f.controlled d = 0 ∧ f.reserve d = 0 ∧ f.external d = 0) ∧
    ∀ c d, f.entitlement c d = 0 ∧ f.terminal c d = 0

/-- Producer gate: an enabled lane needs a receipt-backed producer
(`BLOCKED_LANE_PRODUCER_MISSING`) and a disabled lane is empty
(`DISABLED_LANE_NOT_EMPTY`). -/
def ProducerGate (f : LaneFragment) : Prop :=
  (f.enabled = true → f.receiptBacked = true) ∧ (f.enabled = false → FragmentEmpty f)

/-- Exactly-once partition of the controlled atoms per domain
(`SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE`). -/
def LanePartition (f : LaneFragment) : Prop :=
  ∀ d, f.controlled d = sumClaimants (fun c => f.entitlement c d) + f.reserve d + f.external d

/-- The open terminal claims of a claimant in a domain, summed, never exceed that
claimant's entitlement in the domain (`TERMINAL_BINDING_DRIFT`).  The model keeps one
amount per (claimant, domain) cell, so this is the aggregate bound the running checker
enforces by folding terminal rows per (asset, claimant, control domain); a per-row
comparison would be weaker (two claims of 2 against an entitlement of 3 must reject). -/
def TerminalBound (f : LaneFragment) : Prop :=
  ∀ c d, f.terminal c d ≤ f.entitlement c d

/-- The lane rows, summed over lanes, equal the global tables
(`ENTITLEMENT_ROWS_DRIFT`, `RESERVE_ROWS_DRIFT`, `EXTERNAL_OBLIGATION_BINDING_DRIFT`,
`TERMINAL_BINDING_DRIFT`). -/
def RowsEqual (cert : Lane → LaneFragment) (t : Tables) : Prop :=
  (∀ c d, sumLanes (fun l => (cert l).entitlement c d) = t.liability c d) ∧
    (∀ d, sumLanes (fun l => (cert l).reserve d) = t.reserves d) ∧
    (∀ d, sumLanes (fun l => (cert l).external d) = t.external d) ∧
    ∀ c d, sumLanes (fun l => (cert l).terminal c d) = t.openTerminal c d

/-- The lane aggregates equal global custody (`LANE_AGGREGATE_DRIFT`). -/
def AggregateEqual (cert : Lane → LaneFragment) (t : Tables) : Prop :=
  ∀ d, sumLanes (fun l => (cert l).controlled d) = t.custody d

/-- The per-lane checks. -/
def LaneChecks (f : LaneFragment) : Prop :=
  ProducerGate f ∧ LanePartition f ∧ TerminalBound f

/-- What the checker accepts. -/
def CertificateRelation (cert : Lane → LaneFragment) (t : Tables) : Prop :=
  (∀ l, LaneChecks (cert l)) ∧ RowsEqual cert t ∧ AggregateEqual cert t

/-- The normative partition at the global level follows from the lane-level
relation: summing every lane's exact partition and rewriting through the row and
aggregate equalities gives `custody = entitlements + reserves + external` per
domain.  Derived, not assumed: `Tables` carries no partition field. -/
theorem certificate_implies_normativePartition (cert : Lane → LaneFragment) (t : Tables)
    (h : CertificateRelation cert t) (d : Domain) :
    t.custody d = sumClaimants (fun c => t.liability c d) + t.reserves d + t.external d := by
  obtain ⟨hlanes, ⟨hent, hres, hext, -⟩, hagg⟩ := h
  have p0 := (hlanes .l0).2.1 d
  have p1 := (hlanes .l1).2.1 d
  have p2 := (hlanes .l2).2.1 d
  have ea := hent .alice d
  have eb := hent .bob d
  have r := hres d
  have e := hext d
  have a := hagg d
  simp only [sumLanes, sumClaimants] at *
  omega

/-- Same-domain backing (R1 of the claimant-backing guard): total claimant
entitlements never exceed custody in that domain. -/
theorem certificate_implies_sameDomainBacked (cert : Lane → LaneFragment) (t : Tables)
    (h : CertificateRelation cert t) (d : Domain) :
    sumClaimants (fun c => t.liability c d) ≤ t.custody d := by
  have := certificate_implies_normativePartition cert t h d
  omega

/-- Open-terminal coverage (R2 of the claimant-backing guard), per claimant and
domain: the lane-level terminal bounds sum to the global bound. -/
theorem certificate_implies_terminalCovered (cert : Lane → LaneFragment) (t : Tables)
    (h : CertificateRelation cert t) (c : Claimant) (d : Domain) :
    t.openTerminal c d ≤ t.liability c d := by
  obtain ⟨hlanes, ⟨hent, -, -, hterm⟩, -⟩ := h
  have b0 := (hlanes .l0).2.2 c d
  have b1 := (hlanes .l1).2.2 c d
  have b2 := (hlanes .l2).2.2 c d
  have e := hent c d
  have o := hterm c d
  simp only [sumLanes] at *
  omega

/-- The exact current-profile custody equality of `GlobalClaimantCustodyRelationV1`
is the special case of the normative partition with zero reserves and zero pending
external obligations. -/
theorem certificate_noReserve_noExternal_implies_exactCustody (cert : Lane → LaneFragment)
    (t : Tables) (h : CertificateRelation cert t) (hres : ∀ d, t.reserves d = 0)
    (hext : ∀ d, t.external d = 0) (d : Domain) :
    t.custody d = sumClaimants (fun c => t.liability c d) := by
  have := certificate_implies_normativePartition cert t h d
  have := hres d
  have := hext d
  omega

/-- Without a receipt-backed producer no lane may be enabled: the producer gate
turns `receiptBacked = false` into `enabled = false` for every lane. -/
theorem noReceiptBacked_forces_allDisabled (cert : Lane → LaneFragment)
    (hgate : ∀ l, ProducerGate (cert l)) (hrb : ∀ l, (cert l).receiptBacked = false)
    (l : Lane) : (cert l).enabled = false := by
  cases henabled : (cert l).enabled with
  | false => rfl
  | true =>
    have := (hgate l).1 henabled
    rw [hrb l] at this
    exact nomatch this

/-- Without a receipt-backed producer every table the certificate is checked against
is zero (custody, reserves, external obligations, every liability and open terminal):
together with `noReceiptBacked_forces_allDisabled`, which gives the disabled flags,
this is the model-level form of the fixture invariant that every accepted vector is
registered-empty over disabled lanes. -/
theorem noReceiptBacked_implies_zeroTables (cert : Lane → LaneFragment) (t : Tables)
    (h : CertificateRelation cert t) (hrb : ∀ l, (cert l).receiptBacked = false) (d : Domain) :
    t.custody d = 0 ∧ t.reserves d = 0 ∧ t.external d = 0 ∧
      ∀ c, t.liability c d = 0 ∧ t.openTerminal c d = 0 := by
  obtain ⟨hlanes, ⟨hent, hres, hext, hterm⟩, hagg⟩ := h
  have hgate : ∀ l, ProducerGate (cert l) := fun l => (hlanes l).1
  have empty : ∀ l, FragmentEmpty (cert l) := fun l =>
    (hgate l).2 (noReceiptBacked_forces_allDisabled cert hgate hrb l)
  have z0 := (empty .l0).1 d
  have z1 := (empty .l1).1 d
  have z2 := (empty .l2).1 d
  have a := hagg d
  have r := hres d
  have e := hext d
  refine ⟨?_, ?_, ?_, fun c => ?_⟩
  · simp only [sumLanes] at a; omega
  · simp only [sumLanes] at r; omega
  · simp only [sumLanes] at e; omega
  · have c0 := (empty .l0).2 c d
    have c1 := (empty .l1).2 c d
    have c2 := (empty .l2).2 c d
    have le := hent c d
    have lt := hterm c d
    simp only [sumLanes] at le lt
    omega

/-- A disabled, receipt-less, empty fragment. -/
def emptyFragment : LaneFragment where
  enabled := false
  receiptBacked := false
  controlled := fun _ => 0
  entitlement := fun _ _ => 0
  reserve := fun _ => 0
  external := fun _ => 0
  terminal := fun _ _ => 0

/-- The registered-empty certificate: every lane disabled and empty. -/
def registeredEmptyCertificate : Lane → LaneFragment := fun _ => emptyFragment

/-- All-zero tables. -/
def zeroTables : Tables where
  custody := fun _ => 0
  liability := fun _ _ => 0
  reserves := fun _ => 0
  external := fun _ => 0
  openTerminal := fun _ _ => 0

/-- Every check passes on the empty fragment. -/
theorem emptyFragment_checks : LaneChecks emptyFragment :=
  ⟨⟨fun h => absurd h (by decide),
      fun _ => ⟨fun d => by cases d <;> decide, fun c d => by cases c <;> cases d <;> decide⟩⟩,
    fun d => by cases d <;> decide, fun c d => by cases c <;> cases d <;> decide⟩

/-- Non-vacuity: the registered-empty certificate over zero tables is accepted, so
`noReceiptBacked_implies_zeroTables` is not proved of an empty relation. -/
theorem registeredEmpty_nonvacuous : CertificateRelation registeredEmptyCertificate zeroTables := by
  refine ⟨fun l => ?_, ⟨fun c d => ?_, fun d => ?_, fun d => ?_, fun c d => ?_⟩, fun d => ?_⟩
  · exact emptyFragment_checks
  · cases c <;> cases d <;> decide
  · cases d <;> decide
  · cases d <;> decide
  · cases c <;> cases d <;> decide
  · cases d <;> decide

/-- An enabled, receipt-backed fragment: domain `d0` holds 7 atoms = alice 3 + bob 2 +
reserve 1 + external 1, domain `d1` holds 4 atoms = alice 4; alice has an open
terminal claim of 2 in `d0`. -/
def hotFragment : LaneFragment where
  enabled := true
  receiptBacked := true
  controlled := fun d => match d with
    | .d0 => 7
    | .d1 => 4
  entitlement := fun c d => match c, d with
    | .alice, .d0 => 3
    | .bob, .d0 => 2
    | .alice, .d1 => 4
    | .bob, .d1 => 0
  reserve := fun d => match d with
    | .d0 => 1
    | .d1 => 0
  external := fun d => match d with
    | .d0 => 1
    | .d1 => 0
  terminal := fun c d => match c, d with
    | .alice, .d0 => 2
    | _, _ => 0

/-- Every check passes on the hot fragment. -/
theorem hotFragment_checks : LaneChecks hotFragment :=
  ⟨⟨fun _ => rfl, fun h => absurd h (by decide)⟩, fun d => by cases d <;> decide,
    fun c d => by cases c <;> cases d <;> decide⟩

/-- One receipt-backed lane beside two registered-empty lanes. -/
def mixedCertificate : Lane → LaneFragment := fun l => match l with
  | .l0 => hotFragment
  | .l1 => emptyFragment
  | .l2 => emptyFragment

/-- The tables `mixedCertificate` reconciles against. -/
def mixedTables : Tables where
  custody := fun d => match d with
    | .d0 => 7
    | .d1 => 4
  liability := fun c d => match c, d with
    | .alice, .d0 => 3
    | .bob, .d0 => 2
    | .alice, .d1 => 4
    | .bob, .d1 => 0
  reserves := fun d => match d with
    | .d0 => 1
    | .d1 => 0
  external := fun d => match d with
    | .d0 => 1
    | .d1 => 0
  openTerminal := fun c d => match c, d with
    | .alice, .d0 => 2
    | _, _ => 0

/-- Non-vacuity with content: a certificate carrying entitlements, a reserve, an
external obligation, and a terminal claim is accepted, so the derived theorems are
not consequences of emptiness. -/
theorem mixed_nonvacuous : CertificateRelation mixedCertificate mixedTables := by
  refine ⟨fun l => ?_, ⟨fun c d => ?_, fun d => ?_, fun d => ?_, fun c d => ?_⟩, fun d => ?_⟩
  · cases l
    · exact hotFragment_checks
    · exact emptyFragment_checks
    · exact emptyFragment_checks
  · cases c <;> cases d <;> decide
  · cases d <;> decide
  · cases d <;> decide
  · cases c <;> cases d <;> decide
  · cases d <;> decide

/-- The hot fragment with its reserve dropped: `d0` then holds 7 atoms but only
3 + 2 + 0 + 1 = 6 are assigned. -/
def unassignedFragment : LaneFragment :=
  { hotFragment with reserve := fun _ => 0 }

/-- An unassigned controlled atom fails the exactly-once partition. -/
theorem unassignedAtom_fails_partition : ¬ LanePartition unassignedFragment :=
  fun h => absurd (h .d0) (by decide)

/-- The hot fragment with one of alice's `d0` atoms moved from her entitlement into
the reserve: the partition still balances (2 + 2 + 2 + 1 = 7). -/
def reserveMaskingFragment : LaneFragment :=
  { hotFragment with
    entitlement := fun c d => match c, d with
      | .alice, .d0 => 2
      | .bob, .d0 => 2
      | .alice, .d1 => 4
      | .bob, .d1 => 0
    reserve := fun d => match d with
      | .d0 => 2
      | .d1 => 0 }

/-- `mixedCertificate` with the masking fragment in lane `l0`. -/
def reserveMaskingCertificate : Lane → LaneFragment := fun l => match l with
  | .l0 => reserveMaskingFragment
  | .l1 => emptyFragment
  | .l2 => emptyFragment

/-- A reserve never stands in for a missing claimant entitlement: against the same
tables (alice is owed 3 in `d0`) the masking certificate fails the row equality
even though every lane still partitions exactly and the custody aggregate still
matches.  This is the model-level form of the reserve interpretation
`NAMED_UNENCUMBERED_NO_CLAIMANT`. -/
theorem reserve_cannot_cover_claimant :
    ¬ RowsEqual reserveMaskingCertificate mixedTables ∧
      (∀ l, LanePartition (reserveMaskingCertificate l)) ∧
      AggregateEqual reserveMaskingCertificate mixedTables := by
  refine ⟨fun h => absurd (h.1 .alice .d0) (by decide), fun l => ?_, fun d => ?_⟩
  · cases l <;> intro d <;> cases d <;> decide
  · cases d <;> decide

/-- An enabled lane without a receipt-backed producer fails the producer gate. -/
theorem enabledWithoutProducer_fails_gate :
    ¬ ProducerGate { hotFragment with receiptBacked := false } :=
  fun h => absurd (h.1 rfl) (by decide)

/-- A terminal claim above the claimant's same-domain entitlement fails the bound. -/
theorem terminalOverEntitlement_fails_bound :
    ¬ TerminalBound { hotFragment with terminal := fun c d => match c, d with
      | .alice, .d0 => 4
      | _, _ => 0 } :=
  fun h => absurd (h .alice .d0) (by decide)

/-- Tables that agree with `unassignedFragment` row by row (alice 3, bob 2, no
reserve, external 1) while custody records the 7 controlled atoms. -/
def unassignedTables : Tables :=
  { mixedTables with reserves := fun _ => 0 }

/-- The unassigned certificate. -/
def unassignedCertificate : Lane → LaneFragment := fun l => match l with
  | .l0 => unassignedFragment
  | .l1 => emptyFragment
  | .l2 => emptyFragment

/-- Everything except the lane partition holds for the unassigned certificate. -/
theorem unassigned_satisfies_all_but_partition :
    (∀ l, ProducerGate (unassignedCertificate l) ∧ TerminalBound (unassignedCertificate l)) ∧
      RowsEqual unassignedCertificate unassignedTables ∧
      AggregateEqual unassignedCertificate unassignedTables := by
  refine ⟨fun l => ?_, ⟨fun c d => ?_, fun d => ?_, fun d => ?_, fun c d => ?_⟩, fun d => ?_⟩
  · cases l
    · exact ⟨⟨fun _ => rfl, fun h => absurd h (by decide)⟩, fun c d => by cases c <;> cases d <;> decide⟩
    · exact ⟨emptyFragment_checks.1, emptyFragment_checks.2.2⟩
    · exact ⟨emptyFragment_checks.1, emptyFragment_checks.2.2⟩
  · cases c <;> cases d <;> decide
  · cases d <;> decide
  · cases d <;> decide
  · cases c <;> cases d <;> decide
  · cases d <;> decide

/-- The lane partition premise is necessary for the normative partition: with the
gate, terminal bound, row equality, and aggregate equality all holding but one
atom unassigned, `custody d0 = 7` while entitlements + reserves + external = 6. -/
theorem lanePartition_premise_is_necessary :
    ¬ ∀ (cert : Lane → LaneFragment) (t : Tables),
      ((∀ l, ProducerGate (cert l) ∧ TerminalBound (cert l)) ∧ RowsEqual cert t ∧
        AggregateEqual cert t) →
      ∀ d, t.custody d = sumClaimants (fun c => t.liability c d) + t.reserves d + t.external d :=
  fun universal =>
    absurd (universal unassignedCertificate unassignedTables unassigned_satisfies_all_but_partition .d0)
      (by decide)

end GlobalAccountingAllocationCertificateV1
end Proofs
