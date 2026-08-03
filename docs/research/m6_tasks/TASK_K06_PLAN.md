# FCIS M6 task K06 plan

TASK_ID: K06
STATUS: TESTED_RESEARCH_ONLY_UNMOUNTED

1. Freeze the K03 policy and scan roots.
2. Regenerate current D05 topology and K01 inventory roots.
3. Recheck the J07 authority-switch and target-profile roots.
4. Construct the exact K06 policy and disabled feature flag.
5. Mint one verifier-owned terminal legacy seal.
6. Apply the point-of-use target-only runtime gate.
7. Preserve forged, mutated, stale, crossed-root, phase, and legacy-writer
   rejection witnesses.
8. Record exact implementation identities and source hashes.

K04 is intentionally not silently rebound by this task. Its prior packet fails
the current D05 regeneration check, so K07 remains blocked on a separate K04
repair before a deployment audit can be claimed.
