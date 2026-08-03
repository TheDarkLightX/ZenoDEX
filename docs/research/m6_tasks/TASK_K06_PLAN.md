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

K04 was intentionally not silently rebound by this task. Its prior packet
failed the current D05 regeneration check at the K06 freeze and was then
repaired separately at functional head
`26da7c198a43e0c248cd5823d98c6ce3037c2813` with docs receipt
`547901913c2090d19507b8b993f88276ff7f6a62`. Deployment audit and mounted
claims remain open for K07.
