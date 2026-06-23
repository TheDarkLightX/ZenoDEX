import Std

/-!
# Settlement Allowlist Coverage

Small formal surface for settlement price-attestation source allowlists.
If a consumer allowlist drops a required source, the coverage predicate fails
and the verifier should reject for the missing required source.
-/

namespace TauSwap
namespace SettlementAllowlistCoverage

def RequiredSourcesCovered (required consumer : List String) : Prop :=
  ∀ source, source ∈ required -> source ∈ consumer

def MissingRequiredSource (required consumer : List String) : Prop :=
  ∃ source, source ∈ required ∧ source ∉ consumer

def RejectForMissingRequiredSource (required consumer : List String) : Prop :=
  MissingRequiredSource required consumer

theorem missing_required_source_iff_not_covered
    (required consumer : List String) :
    MissingRequiredSource required consumer ↔ ¬ RequiredSourcesCovered required consumer := by
  unfold MissingRequiredSource RequiredSourcesCovered
  constructor
  · rintro ⟨source, hin, hnotin⟩ h
    exact hnotin (h source hin)
  · intro h
    exact Classical.byContradiction fun h' => h fun source hin =>
      Classical.byContradiction fun hnotin => h' ⟨source, hin, hnotin⟩

theorem oracle_b_missing_from_narrower_consumer_allowlist :
    RejectForMissingRequiredSource ["oracle:a", "oracle:b"] ["oracle:a"] := by
  exact ⟨"oracle:b", by decide, by decide⟩

theorem missing_oracle_b_blocks_required_source_coverage :
    ¬ RequiredSourcesCovered ["oracle:a", "oracle:b"] ["oracle:a"] := by
  exact fun h => by
    have hb := h "oracle:b" (by decide)
    contradiction

theorem narrower_consumer_allowlist_rejects_and_fails_coverage :
    RejectForMissingRequiredSource ["oracle:a", "oracle:b"] ["oracle:a"]
      ∧ ¬ RequiredSourcesCovered ["oracle:a", "oracle:b"] ["oracle:a"] := by
  exact And.intro
    oracle_b_missing_from_narrower_consumer_allowlist
    missing_oracle_b_blocks_required_source_coverage

end SettlementAllowlistCoverage
end TauSwap
