import Proofs.DeterministicParallelExecution
import Proofs.ReadWriteStableParallel
import Proofs.TypedDeterministicParser

/-!
# ZenoDEX theorem-ledger formal surface

This module groups the connective proof developments introduced by the
literature-to-code review and the Research Kernel/Morph/ESSO continuation.
Importing it checks that:

* the typed deterministic parser boundary;
* abstract immutable-patch permutation invariance; and
* the stronger sound-footprint/read-write noninterference theorem

coexist in one pinned Lean environment.

The repository's older concrete `ZenoLedgerDisjointWrites` development remains a
separate proof surface.  No theorem here upgrades a runtime implementation
automatically.  The runtime must still discharge concrete parser round trips,
footprint-extractor soundness, immutable-snapshot binding, canonical joins,
atomic storage/outbox commitment, and cross-implementation refinement.
-/

namespace ZenoDEX.TheoremLedger

/-- The module checks imports while introducing no additional trusted premise. -/
theorem integration_surface_checked : True := by
  trivial

end ZenoDEX.TheoremLedger
