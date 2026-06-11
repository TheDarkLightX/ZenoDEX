import Proofs.BatchAuctionCanonical
import Proofs.BatchCPMMUnification

/-!
# Settlement Canonical Execution Bridge

This file connects the S-tier batch canonicalization theorem to the settlement
execution surface in `BatchCPMMUnification`.

The key proof shape is:

```text
winner in S
and forall x in S, winner <= x
and runtime trace realizes the winner candidate
and the winner key is aligned with batchAB(candidate)
-> executed trace has the canonical (A,B) objective over S
```

This does not claim the runtime candidate generator is complete.  It proves the
smaller bridge from a checked winner certificate plus a realization equality to
the executed settlement and objective.
-/

namespace TauSwap
namespace Batch

/-- Decompose `k₁ ≤ k₂` for abstract keys into the component statement:
either `k₁` has strictly more volume, or volumes tie and either `k₁` has
strictly more surplus, or both tie and `ord k₁ ≤ ord k₂`.  Abstract-key
counterpart of `key_le_iff`, used by the settlement execution bridge below. -/
theorem key_le_components {k₁ k₂ : Key} (h : k₁ ≤ k₂) :
    (vol k₂ < vol k₁) ∨
      (vol k₁ = vol k₂ ∧ ((sur k₂ < sur k₁) ∨ (sur k₁ = sur k₂ ∧ ord k₁ ≤ ord k₂))) := by
  simpa [vol, sur, ord, key] using
    (key_le_iff (v₁ := vol k₁) (v₂ := vol k₂) (s₁ := sur k₁) (s₂ := sur k₂)
      (o₁ := ord k₁) (o₂ := ord k₂)).1 (by simpa [key, vol, sur, ord] using h)

end Batch

namespace SettlementCanonicalExecution

open BatchCPMMUnification

/-! ## Key Decoding -/

@[simp] theorem vol_key (v s : Nat) (o : _root_.TauSwap.Batch.Order) :
    _root_.TauSwap.Batch.vol (_root_.TauSwap.Batch.key v s o) = v := by
  simp [_root_.TauSwap.Batch.vol, _root_.TauSwap.Batch.key]

@[simp] theorem sur_key (v s : Nat) (o : _root_.TauSwap.Batch.Order) :
    _root_.TauSwap.Batch.sur (_root_.TauSwap.Batch.key v s o) = s := by
  simp [_root_.TauSwap.Batch.sur, _root_.TauSwap.Batch.key]

@[simp] theorem ord_key (v s : Nat) (o : _root_.TauSwap.Batch.Order) :
    _root_.TauSwap.Batch.ord (_root_.TauSwap.Batch.key v s o) = o := by
  simp [_root_.TauSwap.Batch.ord, _root_.TauSwap.Batch.key]

/-! ## Certificate Shape -/

/-- A Tau-checkable certificate shape for a canonical settlement winner:
the winner is in the finite candidate key set and is less than or equal to
every candidate key under the total `(A,B,order)` key. -/
def CertificateOK
    (S : Finset _root_.TauSwap.Batch.Key)
    (winner : _root_.TauSwap.Batch.Key) : Prop :=
  winner ∈ S ∧ ∀ x ∈ S, winner ≤ x

/-- Runtime-list certificate shape: the winner appears in the emitted ordered
list and is no worse than every emitted key.  This is the natural shape for a
stream checker before order and duplicates are forgotten with `toFinset`. -/
def ListCertificateOK
    (emitted : List _root_.TauSwap.Batch.Key)
    (winner : _root_.TauSwap.Batch.Key) : Prop :=
  winner ∈ emitted ∧ ∀ x ∈ emitted, winner ≤ x

/-- A runtime-list certificate promotes to the finite-set certificate used by
the canonical settlement theorems. -/
theorem certificateOK_toFinset_of_listCertificate
    {emitted : List _root_.TauSwap.Batch.Key}
    {winner : _root_.TauSwap.Batch.Key}
    (hcert : ListCertificateOK emitted winner) :
    CertificateOK emitted.toFinset winner := by
  constructor
  · simpa using hcert.1
  · intro x hx
    exact hcert.2 x (by simpa using hx)

/-- A finite-set certificate over the deduplicated emitted list can be checked
as a list certificate over the original runtime list. -/
theorem listCertificateOK_of_certificateOK_toFinset
    {emitted : List _root_.TauSwap.Batch.Key}
    {winner : _root_.TauSwap.Batch.Key}
    (hcert : CertificateOK emitted.toFinset winner) :
    ListCertificateOK emitted winner := by
  constructor
  · simpa using hcert.1
  · intro x hx
    exact hcert.2 x (by simpa using hx)

/-- A certified key-minimum maximizes executed volume. -/
theorem certificate_volume_max
    {S : Finset _root_.TauSwap.Batch.Key}
    {winner : _root_.TauSwap.Batch.Key}
    (hcert : CertificateOK S winner) :
    ∀ x ∈ S, _root_.TauSwap.Batch.vol winner ≥ _root_.TauSwap.Batch.vol x := by
  intro x hx
  have hwx : winner ≤ x := hcert.2 x hx
  rcases _root_.TauSwap.Batch.key_le_components hwx with hvol_lt | ⟨hvol_eq, _⟩
  · exact Nat.le_of_lt hvol_lt
  · exact Nat.le_of_eq hvol_eq.symm

/-- Among candidates with maximum volume tied, a certified key-minimum
maximizes surplus. -/
theorem certificate_surplus_max_on_volume_tie
    {S : Finset _root_.TauSwap.Batch.Key} {winner : _root_.TauSwap.Batch.Key}
    (hcert : CertificateOK S winner) :
    ∀ x ∈ S, _root_.TauSwap.Batch.vol winner = _root_.TauSwap.Batch.vol x →
      _root_.TauSwap.Batch.sur winner ≥ _root_.TauSwap.Batch.sur x := by
  intro x hx hvol
  have hwx : winner ≤ x := hcert.2 x hx
  rcases _root_.TauSwap.Batch.key_le_components hwx with hvol_lt | ⟨_, htail⟩
  · rw [hvol] at hvol_lt
    exact False.elim ((Nat.lt_irrefl (_root_.TauSwap.Batch.vol x)) hvol_lt)
  · rcases htail with hsur_lt | ⟨hsur_eq, _⟩
    · exact Nat.le_of_lt hsur_lt
    · exact Nat.le_of_eq hsur_eq.symm

/-- Among candidates with maximum volume and surplus tied, a certified
key-minimum has the canonical lexicographically least order. -/
theorem certificate_order_min_on_objective_tie
    {S : Finset _root_.TauSwap.Batch.Key} {winner : _root_.TauSwap.Batch.Key}
    (hcert : CertificateOK S winner) :
    ∀ x ∈ S, _root_.TauSwap.Batch.vol winner = _root_.TauSwap.Batch.vol x →
      _root_.TauSwap.Batch.sur winner = _root_.TauSwap.Batch.sur x →
        _root_.TauSwap.Batch.ord winner ≤ _root_.TauSwap.Batch.ord x := by
  intro x hx hvol hsur
  have hwx : winner ≤ x := hcert.2 x hx
  rcases _root_.TauSwap.Batch.key_le_components hwx with hvol_lt | ⟨_, htail⟩
  · rw [hvol] at hvol_lt
    exact False.elim ((Nat.lt_irrefl (_root_.TauSwap.Batch.vol x)) hvol_lt)
  · rcases htail with hsur_lt | ⟨_, hord⟩
    · rw [hsur] at hsur_lt
      exact False.elim ((Nat.lt_irrefl (_root_.TauSwap.Batch.sur x)) hsur_lt)
    · exact hord

/-- Two certificate-valid winners for the same candidate key set are equal. -/
theorem certificate_unique {S : Finset _root_.TauSwap.Batch.Key} {w₁ w₂ : _root_.TauSwap.Batch.Key}
    (h₁ : CertificateOK S w₁) (h₂ : CertificateOK S w₂) :
    w₁ = w₂ :=
  le_antisymm (h₁.2 w₂ h₂.1) (h₂.2 w₁ h₁.1)

/-! ## Feasible-Domain Coverage -/

/-- The emitted candidate key set covers a feasible domain when every feasible
key appears in the emitted set.  Extra emitted keys are allowed; the winner must
also be proved feasible when transferring the certificate to the domain. -/
def CoversDomain
    (emitted domain : Finset _root_.TauSwap.Batch.Key) : Prop :=
  ∀ x ∈ domain, x ∈ emitted

/-- A winner certificate over an emitted set transfers to the full feasible
domain when the emitted set covers the domain and the winner itself is feasible. -/
theorem certificate_restricts_to_covered_domain
    {emitted domain : Finset _root_.TauSwap.Batch.Key}
    {winner : _root_.TauSwap.Batch.Key}
    (hcert : CertificateOK emitted winner)
    (hcover : CoversDomain emitted domain)
    (hwinner : winner ∈ domain) :
    CertificateOK domain winner := by
  exact ⟨hwinner, fun x hx => hcert.2 x (hcover x hx)⟩

/-- Candidate-level generator coverage: every abstract feasible candidate maps
to a key that appears in the emitted key set. -/
def CoversKeyImage
    {α : Type}
    (emitted : Finset _root_.TauSwap.Batch.Key)
    (domain : Finset α)
    (keyOf : α → _root_.TauSwap.Batch.Key) : Prop :=
  ∀ candidate ∈ domain, keyOf candidate ∈ emitted

/-- Runtime-list generator coverage: every abstract feasible candidate maps to
a key that appears in the emitted ordered key list. -/
def CoversKeyList
    {α : Type}
    (emitted : List _root_.TauSwap.Batch.Key)
    (domain : Finset α)
    (keyOf : α → _root_.TauSwap.Batch.Key) : Prop :=
  ∀ candidate ∈ domain, keyOf candidate ∈ emitted

/-- List coverage promotes to finite-set image coverage by forgetting order and
duplicates. -/
theorem coversKeyImage_of_coversKeyList
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    (hcover : CoversKeyList emitted domain keyOf) :
    CoversKeyImage emitted.toFinset domain keyOf := by
  intro candidate hcandidate
  simpa using hcover candidate hcandidate

/-- A projected-domain subset audit gives runtime-list coverage.  This is the
usual shape of an external generator audit: every feasible domain key appears
in the deduplicated emitted runtime list. -/
theorem coversKeyList_of_image_subset_toFinset
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    (hsub : domain.image keyOf ⊆ emitted.toFinset) :
    CoversKeyList emitted domain keyOf := by
  intro candidate hcandidate
  have hkey : keyOf candidate ∈ domain.image keyOf :=
    Finset.mem_image.mpr ⟨candidate, hcandidate, rfl⟩
  simpa using hsub hkey

/-- Exact projected-domain equality is enough for runtime-list coverage. -/
theorem coversKeyList_of_toFinset_eq_image
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    (heq : emitted.toFinset = domain.image keyOf) :
    CoversKeyList emitted domain keyOf := by
  exact coversKeyList_of_image_subset_toFinset (by
    intro key hkey
    simpa [heq] using hkey)

/-- Candidate-level coverage implies key-domain coverage for the image of the
feasible candidate domain.  This is the abstract shape a concrete generator
coverage theorem should discharge. -/
theorem coversDomain_image_of_coversKeyImage
    {α : Type}
    {emitted : Finset _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    (hcover : CoversKeyImage emitted domain keyOf) :
    CoversDomain emitted (domain.image keyOf) := by
  intro key hkey
  rcases Finset.mem_image.mp hkey with ⟨candidate, hcandidate, hkey_eq⟩
  rw [← hkey_eq]
  exact hcover candidate hcandidate

/-! ## Runtime Realization Bridge -/

/-- A candidate settlement carries its batch and the deterministic tie-break
order used to build the canonical key. -/
structure SettlementCandidate where
  batch : BatchSettlement
  order : _root_.TauSwap.Batch.Order

/-- The canonical key induced by a candidate's executed `(A,B)` objective and
order. -/
def SettlementCandidate.key (c : SettlementCandidate) : _root_.TauSwap.Batch.Key :=
  _root_.TauSwap.Batch.key (batchAB c.batch).1 (batchAB c.batch).2 c.order

/-- The runtime trace realizes a candidate when the trace batch is exactly the
candidate batch.  This is intentionally an equality bridge; concrete runtime
parsers can prove this by replaying their trace semantics. -/
def Realizes (trace : BatchSettlement) (candidate : SettlementCandidate) : Prop :=
  trace = candidate.batch

/-- Realization preserves the computed `(A,B)` objective. -/
theorem realizes_batchAB_eq {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hreal : Realizes trace candidate) :
    batchAB trace = batchAB candidate.batch := by
  rw [hreal]

/-- Realization preserves the settlement fold. -/
theorem realizes_batchToSettlement_eq {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch := by
  rw [hreal]

/-- If the runtime realizes a candidate whose induced key is certified minimal,
then the executed trace has the canonical volume, surplus, and tie-break
properties over the certified key set. -/
theorem realized_certificate_canonical_objective
    {S : Finset _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK S candidate.key)
    (hreal : Realizes trace candidate) :
    candidate.key ∈ S ∧
      (∀ x ∈ S, (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ S, (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ S, (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
          candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  have hAB : batchAB trace = batchAB candidate.batch :=
    realizes_batchAB_eq hreal
  refine ⟨hcert.1, ?_, ?_, ?_⟩
  · intro x hx
    have hmax := certificate_volume_max hcert x hx
    simpa [SettlementCandidate.key, hAB]
      using hmax
  · intro x hx hvol
    have hsur := certificate_surplus_max_on_volume_tie hcert x hx
    have hvolKey :
        _root_.TauSwap.Batch.vol candidate.key = _root_.TauSwap.Batch.vol x := by
      simpa [SettlementCandidate.key, hAB] using hvol
    simpa [SettlementCandidate.key, hAB]
      using hsur hvolKey
  · intro x hx hvol hsur
    have horder := certificate_order_min_on_objective_tie hcert x hx
    have hvolKey :
        _root_.TauSwap.Batch.vol candidate.key = _root_.TauSwap.Batch.vol x := by
      simpa [SettlementCandidate.key, hAB] using hvol
    have hsurKey :
        _root_.TauSwap.Batch.sur candidate.key = _root_.TauSwap.Batch.sur x := by
      simpa [SettlementCandidate.key, hAB] using hsur
    simpa [SettlementCandidate.key]
      using horder hvolKey hsurKey

/-- End-to-end bridge for this layer: a certified canonical candidate realized
by the runtime trace gives both the same executed settlement fold and the
canonical `(A,B)` objective over the certified key set. -/
theorem realized_certificate_executes_canonical_settlement
    {S : Finset _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK S candidate.key)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ S ∧
      (∀ x ∈ S, (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ S, (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ S, (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
          candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact ⟨realizes_batchToSettlement_eq hreal,
    realized_certificate_canonical_objective hcert hreal⟩

/-! ## Covered-Domain Execution Bridge -/

/-- If the emitted candidate key set covers the feasible domain, and the
certified realized candidate is feasible, then the executed trace has the
canonical volume, surplus, and tie-break properties over the feasible domain,
not merely over the emitted set. -/
theorem realized_certificate_canonical_objective_on_covered_domain
    {emitted domain : Finset _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK emitted candidate.key)
    (hcover : CoversDomain emitted domain)
    (hfeasible : candidate.key ∈ domain)
    (hreal : Realizes trace candidate) :
    candidate.key ∈ domain ∧
      (∀ x ∈ domain,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_certificate_canonical_objective
    (certificate_restricts_to_covered_domain hcert hcover hfeasible)
    hreal

/-- Covered-domain end-to-end bridge: a runtime trace realizing a feasible
certified candidate executes that candidate's settlement fold and is canonical
over the full covered feasible domain. -/
theorem realized_certificate_executes_canonical_domain_settlement
    {emitted domain : Finset _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK emitted candidate.key)
    (hcover : CoversDomain emitted domain)
    (hfeasible : candidate.key ∈ domain)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain ∧
      (∀ x ∈ domain,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact ⟨realizes_batchToSettlement_eq hreal,
    realized_certificate_canonical_objective_on_covered_domain
      hcert hcover hfeasible hreal⟩

/-! ## Generator-Coverage Execution Bridge -/

/-- Candidate-level generator coverage is sufficient to use the covered-domain
execution theorem on the key image of the feasible candidate domain. -/
theorem realized_certificate_executes_canonical_image_settlement
    {α : Type}
    {emitted : Finset _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK emitted candidate.key)
    (hcover : CoversKeyImage emitted domain keyOf)
    (hfeasible : candidate.key ∈ domain.image keyOf)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain.image keyOf ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_certificate_executes_canonical_domain_settlement
    hcert (coversDomain_image_of_coversKeyImage hcover) hfeasible hreal

/-- Runtime-list coverage is sufficient to use the canonical execution theorem
on the key image of the feasible candidate domain.  This is the closest abstract
shape to an ordered runtime generator: order and duplicates in the emitted list
are irrelevant after the certificate is checked over `emitted.toFinset`. -/
theorem realized_list_certificate_executes_canonical_image_settlement
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK emitted.toFinset candidate.key)
    (hcover : CoversKeyList emitted domain keyOf)
    (hfeasible : candidate.key ∈ domain.image keyOf)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain.image keyOf ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_certificate_executes_canonical_image_settlement
    hcert (coversKeyImage_of_coversKeyList hcover) hfeasible hreal

/-- Fully list-facing canonical execution theorem.  A runtime-list certificate,
runtime-list coverage, feasible winner key, and realization equality are enough
to conclude that the executed settlement is canonical over the feasible key
image. -/
theorem realized_runtime_list_certificate_executes_canonical_image_settlement
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : ListCertificateOK emitted candidate.key)
    (hcover : CoversKeyList emitted domain keyOf)
    (hfeasible : candidate.key ∈ domain.image keyOf)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain.image keyOf ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_list_certificate_executes_canonical_image_settlement
    (certificateOK_toFinset_of_listCertificate hcert) hcover hfeasible hreal

/-- Runtime projected-domain equality closes the generator-coverage side
condition for the list-facing canonical execution theorem.  This is the common
certificate shape for an audited generator that proves the deduplicated emitted
key list is exactly the feasible key image. -/
theorem realized_runtime_list_certificate_executes_canonical_of_toFinset_eq_image
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : ListCertificateOK emitted candidate.key)
    (heq : emitted.toFinset = domain.image keyOf)
    (hfeasible : candidate.key ∈ domain.image keyOf)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain.image keyOf ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_runtime_list_certificate_executes_canonical_image_settlement
    hcert (coversKeyList_of_toFinset_eq_image heq) hfeasible hreal

/-- Set-certificate variant of the projected-domain equality theorem.  Use this
when the runtime verifier first deduplicates the emitted list and checks the
minimum certificate over `emitted.toFinset`. -/
theorem realized_toFinset_certificate_executes_canonical_of_toFinset_eq_image
    {α : Type}
    {emitted : List _root_.TauSwap.Batch.Key}
    {domain : Finset α}
    {keyOf : α → _root_.TauSwap.Batch.Key}
    {trace : BatchSettlement}
    {candidate : SettlementCandidate}
    (hcert : CertificateOK emitted.toFinset candidate.key)
    (heq : emitted.toFinset = domain.image keyOf)
    (hfeasible : candidate.key ∈ domain.image keyOf)
    (hreal : Realizes trace candidate) :
    batchToSettlement trace = batchToSettlement candidate.batch ∧
      candidate.key ∈ domain.image keyOf ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
      (∀ x ∈ domain.image keyOf,
        (batchAB trace).1 = _root_.TauSwap.Batch.vol x →
          (batchAB trace).2 = _root_.TauSwap.Batch.sur x →
            candidate.order ≤ _root_.TauSwap.Batch.ord x) := by
  exact realized_runtime_list_certificate_executes_canonical_of_toFinset_eq_image
    (listCertificateOK_of_certificateOK_toFinset hcert) heq hfeasible hreal

end SettlementCanonicalExecution
end TauSwap
