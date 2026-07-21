import Proofs.DeterministicParallelExecution
import Proofs.TypedDeterministicParser
import Proofs.ZenoLedgerDisjointWrites

/-!
# ZenoDEX theorem-ledger formal surface

This module intentionally groups the connective proofs introduced by the
literature-to-code review with the repository's existing concrete disjoint-write
result.  Importing it checks that the abstract patch theorem, typed parser
boundary, and concrete key-write theorem coexist in one pinned Lean environment.

No theorem in this module upgrades a runtime implementation automatically.  The
runtime must still discharge its concrete parser round trip, footprint
soundness, immutable-snapshot, canonical-join, and atomic-commit obligations.
-/

namespace ZenoDEX.TheoremLedger

/-- The theorem-ledger module is a proof integration point, not a new axiom. -/
theorem integration_surface_checked : True := by
  trivial

end ZenoDEX.TheoremLedger
