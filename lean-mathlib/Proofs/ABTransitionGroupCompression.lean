import Proofs.ABReserveStateQuotient

/-!
# AB Transition-Group Compression Bridge

This file isolates the generic Lean proof component behind the bounded
transition-group compression certificate.

The host checker starts from a list of predecessor transition rows and emits one
compressed row per generated child state. Each compressed row carries a
representative transition and the list of transition rows in the generated-child
group. This Lean file proves the abstract contract for that shape: if every
source transition is covered by exactly some host-validated group membership,
and every group member is a source transition whose generated child matches the
group key, then the compressed generated-child image is exactly the source
transition generated-child image.

Scope: this is a research proof component. It does not prove Python-to-Lean
refinement, JSON canonicalization, packet hashing, Merkle membership, digest
computation, nonzero `min_amount_out`, settlement, state-root, production, or
governance authority.
-/

namespace ABTransitionGroupCompression

open ABReserveStateQuotient

/-- Host transition row for the abstract child-frontier compression surface.

The proof only needs the parent/child masks, the representative step, and the
generated child reserve state. The host checker owns CPMM execution, Merkle
membership, packet hashing, and digest computation. -/
structure TransitionRow where
  parentMask : Nat
  childMask : Nat
  stepBit : Nat
  parentState : ReserveState
  generatedChild : ReserveState
  deriving Repr, DecidableEq

/-- One compressed generated-child group.

`members` is the host-provided set of transition rows that generated the child.
`transitionGroupCount` mirrors the host-side count field and is checked against
`members.length` in the validity predicate. -/
structure CompressedTransitionGroup where
  generatedChild : ReserveState
  representative : TransitionRow
  members : List TransitionRow
  transitionGroupCount : Nat
  deriving Repr, DecidableEq

/-- Generated-child image of the source transition rows. -/
def transitionGeneratedChildren (transitions : List TransitionRow) : List ReserveState :=
  transitions.map TransitionRow.generatedChild

/-- Generated-child image of the compressed group rows. -/
def compressedGeneratedChildren (groups : List CompressedTransitionGroup) : List ReserveState :=
  groups.map CompressedTransitionGroup.generatedChild

/-- Local validity for a compressed transition group.

The representative must be a member, the count must match the member list, and
every member must share the group generated-child key. -/
def compressedTransitionGroupSound (group : CompressedTransitionGroup) : Prop :=
  group.representative ∈ group.members ∧
    group.transitionGroupCount = group.members.length ∧
    ∀ transition, transition ∈ group.members ->
      transition.generatedChild = group.generatedChild

/-- Every source transition is covered by a compressed group membership. -/
def compressionCoversTransitions
    (transitions : List TransitionRow)
    (groups : List CompressedTransitionGroup) : Prop :=
  ∀ transition, transition ∈ transitions ->
    ∃ group, group ∈ groups ∧ transition ∈ group.members

/-- Compressed group memberships contain no transition outside the source rows. -/
def compressionHasNoExtraTransitions
    (transitions : List TransitionRow)
    (groups : List CompressedTransitionGroup) : Prop :=
  ∀ group, group ∈ groups ->
    ∀ transition, transition ∈ group.members -> transition ∈ transitions

/-- Data-only shell for a host-emitted transition-group compression table.

The Boolean fields mirror the host packet rails. They are modeled as validity
inputs; this file does not prove hash computation or host refinement. -/
structure TransitionGroupCompressionHostTable where
  transitions : List TransitionRow
  groups : List CompressedTransitionGroup
  packetHashBound : Bool
  noAuthorityEffect : Bool
  transitionGroupCompressionBound : Bool
  generatedImageDigestBound : Bool
  representativeTransitionBound : Bool
  deriving Repr

/-- Validity predicate for a transition-group compression host table. -/
def transitionGroupCompressionHostTableValid
    (table : TransitionGroupCompressionHostTable) : Prop :=
  table.packetHashBound = true ∧
    table.noAuthorityEffect = true ∧
    table.transitionGroupCompressionBound = true ∧
    table.generatedImageDigestBound = true ∧
    table.representativeTransitionBound = true ∧
    (∀ group, group ∈ table.groups -> compressedTransitionGroupSound group) ∧
    compressionCoversTransitions table.transitions table.groups ∧
    compressionHasNoExtraTransitions table.transitions table.groups

/-- A valid group representative is a source transition row. -/
theorem compressedTransitionGroup_representative_mem_transitions
    {table : TransitionGroupCompressionHostTable}
    {group : CompressedTransitionGroup}
    (hvalid : transitionGroupCompressionHostTableValid table)
    (hgroup : group ∈ table.groups) :
    group.representative ∈ table.transitions := by
  rcases hvalid with
    ⟨_hhash, _hnoAuthority, _hcompression, _hdigest, _hrepresentative,
      hgroupSound, _hcover, hnoExtra⟩
  rcases hgroupSound group hgroup with ⟨hrepMem, _hcount, _hchildren⟩
  exact hnoExtra group hgroup group.representative hrepMem

/-- A valid compressed table preserves the generated-child image.

The compressed generated-child rows contain a child exactly when some source
transition row generated that child. -/
theorem transitionGroupCompression_preserves_generatedChildImage
    {table : TransitionGroupCompressionHostTable}
    (hvalid : transitionGroupCompressionHostTableValid table) :
    ∀ child,
      child ∈ compressedGeneratedChildren table.groups ↔
        child ∈ transitionGeneratedChildren table.transitions := by
  rcases hvalid with
    ⟨_hhash, _hnoAuthority, _hcompression, _hdigest, _hrepresentative,
      hgroupSound, hcover, hnoExtra⟩
  intro child
  constructor
  · intro hchild
    unfold compressedGeneratedChildren at hchild
    rw [List.mem_map] at hchild
    rcases hchild with ⟨group, hgroup, rfl⟩
    rcases hgroupSound group hgroup with ⟨hrepMem, _hcount, hmemberChild⟩
    have hrepSource :
        group.representative ∈ table.transitions :=
      hnoExtra group hgroup group.representative hrepMem
    unfold transitionGeneratedChildren
    rw [List.mem_map]
    exact ⟨group.representative, hrepSource,
      hmemberChild group.representative hrepMem⟩
  · intro hchild
    unfold transitionGeneratedChildren at hchild
    rw [List.mem_map] at hchild
    rcases hchild with ⟨transition, htransition, rfl⟩
    rcases hcover transition htransition with ⟨group, hgroup, hmember⟩
    rcases hgroupSound group hgroup with ⟨_hrepMem, _hcount, hmemberChild⟩
    unfold compressedGeneratedChildren
    rw [List.mem_map]
    exact ⟨group, hgroup, (hmemberChild transition hmember).symm⟩

/-- A valid nonempty source transition corpus forces a nonempty compressed
group corpus. -/
theorem transitionGroupCompression_nonempty_groups_of_nonempty_transitions
    {table : TransitionGroupCompressionHostTable}
    (hvalid : transitionGroupCompressionHostTableValid table)
    (hnonempty : ∃ transition, transition ∈ table.transitions) :
    ∃ group, group ∈ table.groups := by
  rcases hvalid with
    ⟨_hhash, _hnoAuthority, _hcompression, _hdigest, _hrepresentative,
      _hgroupSound, hcover, _hnoExtra⟩
  rcases hnonempty with ⟨transition, htransition⟩
  rcases hcover transition htransition with ⟨group, hgroup, _hmember⟩
  exact ⟨group, hgroup⟩

/-- Host-table endpoint for the transition-group compression bridge.

A valid table gives the host rails, proves every group representative is a
source transition, and proves exact equality of the compressed and source
generated-child images. -/
theorem transitionGroupCompressionHostTable_validates
    (table : TransitionGroupCompressionHostTable)
    (hvalid : transitionGroupCompressionHostTableValid table) :
    table.packetHashBound = true ∧
      table.noAuthorityEffect = true ∧
      table.transitionGroupCompressionBound = true ∧
      table.generatedImageDigestBound = true ∧
      table.representativeTransitionBound = true ∧
      (∀ group, group ∈ table.groups -> group.representative ∈ table.transitions) ∧
      (∀ child,
        child ∈ compressedGeneratedChildren table.groups ↔
          child ∈ transitionGeneratedChildren table.transitions) := by
  rcases hvalid with
    ⟨hhash, hnoAuthority, hcompression, hdigest, hrepresentative,
      hgroupSound, hcover, hnoExtra⟩
  have hvalidAgain :
      transitionGroupCompressionHostTableValid table :=
    ⟨hhash, hnoAuthority, hcompression, hdigest, hrepresentative,
      hgroupSound, hcover, hnoExtra⟩
  exact ⟨hhash, hnoAuthority, hcompression, hdigest, hrepresentative,
    fun group hgroup =>
      compressedTransitionGroup_representative_mem_transitions
        (table := table) hvalidAgain hgroup,
    transitionGroupCompression_preserves_generatedChildImage hvalidAgain⟩

/-- Concrete non-vacuity witness for the transition-group compression bridge. -/
theorem witness_transitionGroupCompressionHostTable_validates :
    let parent : ReserveState := ⟨1000, 900⟩
    let childA : ReserveState := ⟨1100, 810⟩
    let childB : ReserveState := ⟨1200, 700⟩
    let t1 : TransitionRow := ⟨0, 1, 0, parent, childA⟩
    let t2 : TransitionRow := ⟨2, 3, 1, parent, childA⟩
    let t3 : TransitionRow := ⟨4, 5, 2, parent, childB⟩
    let groupA : CompressedTransitionGroup := ⟨childA, t1, [t1, t2], 2⟩
    let groupB : CompressedTransitionGroup := ⟨childB, t3, [t3], 1⟩
    let table : TransitionGroupCompressionHostTable := {
      transitions := [t1, t2, t3]
      groups := [groupA, groupB]
      packetHashBound := true
      noAuthorityEffect := true
      transitionGroupCompressionBound := true
      generatedImageDigestBound := true
      representativeTransitionBound := true
    }
    transitionGroupCompressionHostTableValid table ∧
      table.packetHashBound = true ∧
      table.noAuthorityEffect = true ∧
      table.transitionGroupCompressionBound = true ∧
      table.generatedImageDigestBound = true ∧
      table.representativeTransitionBound = true ∧
      (∀ group, group ∈ table.groups -> group.representative ∈ table.transitions) ∧
      (∀ child,
        child ∈ compressedGeneratedChildren table.groups ↔
          child ∈ transitionGeneratedChildren table.transitions) := by
  let parent : ReserveState := ⟨1000, 900⟩
  let childA : ReserveState := ⟨1100, 810⟩
  let childB : ReserveState := ⟨1200, 700⟩
  let t1 : TransitionRow := ⟨0, 1, 0, parent, childA⟩
  let t2 : TransitionRow := ⟨2, 3, 1, parent, childA⟩
  let t3 : TransitionRow := ⟨4, 5, 2, parent, childB⟩
  let groupA : CompressedTransitionGroup := ⟨childA, t1, [t1, t2], 2⟩
  let groupB : CompressedTransitionGroup := ⟨childB, t3, [t3], 1⟩
  let table : TransitionGroupCompressionHostTable := {
    transitions := [t1, t2, t3]
    groups := [groupA, groupB]
    packetHashBound := true
    noAuthorityEffect := true
    transitionGroupCompressionBound := true
    generatedImageDigestBound := true
    representativeTransitionBound := true
  }
  have hvalid : transitionGroupCompressionHostTableValid table := by
    unfold transitionGroupCompressionHostTableValid
      compressedTransitionGroupSound
      compressionCoversTransitions
      compressionHasNoExtraTransitions
    simp [table, groupA, groupB, t1, t2, t3]
  exact ⟨hvalid, transitionGroupCompressionHostTable_validates table hvalid⟩

end ABTransitionGroupCompression
