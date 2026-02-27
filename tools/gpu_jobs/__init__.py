"""GPU/accelerator-assisted *off-chain* job tooling.

These tools are used to:
- search/score large candidate sets efficiently (optionally on GPU),
- emit small, deterministic witnesses/certificates,
- and rely on cheap, deterministic verifiers (Tau or Python replay) before
  anything is promoted to consensus-critical logic.
"""

