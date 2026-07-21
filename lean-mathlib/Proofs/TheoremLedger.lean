import Proofs.DeterministicParallelExecution
import Proofs.TypedDeterministicParser

/-!
# ZenoDEX theorem-ledger formal surface

This module groups the two connective proof developments introduced by the
literature-to-code review.  Importing it checks that the typed parser boundary
and abstract independent-patch semantics coexist in one pinned Lean environment.

The repository's older concrete `ZenoLedgerDisjointWrites` development remains a
separate proof surface.  This integration module does not make its compilation a
premise of the new parser and patch results.

No theorem here upgrades a runtime implementation automatically.  The runtime
must still discharge its concrete parser round trip, footprint soundness,
immutable-snapshot, canonical-join, and atomic-commit obligations.
-/

namespace ZenoDEX.TheoremLedger

/-- The module checks imports while introducing no additional trusted premise. -/
theorem integration_surface_checked : True := by
  trivial

end ZenoDEX.TheoremLedger
