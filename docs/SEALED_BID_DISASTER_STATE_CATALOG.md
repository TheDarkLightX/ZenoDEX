# Sealed-Bid Disaster State Catalog

This catalog names the bounded sealed-bid failure states that matter for production hardening and records how the current ESSO kernels discharge them.

Scope:
- `src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml`
- `src/kernels/dex/sealed_bid_non_reveal_bond_v1.yaml`

Method:
- export the ESSO kernels to standalone Python refs,
- replay a concrete predecessor trace into the last risky state,
- confirm that exactly one accepted action remains,
- require that action to move the FSM into `Complete`.

Tool:
- [sealed_bid_disaster_catalog.py](../tools/sealed_bid_disaster_catalog.py)

Named disasters:

1. `empty_auction_deadlock`
- Model: `sealed_bid_commit_reveal_gate_v1`
- Shape: commit window closes with `commit_count = 0` and no remaining legal transition.
- Discharge action: `finalize_empty_auction`

2. `no_reveal_deadlock`
- Model: `sealed_bid_commit_reveal_gate_v1`
- Shape: at least one commitment exists, reveal window closes with `reveal_count = 0`, and settlement must not open.
- Discharge action: `finalize_no_reveal_auction`

3. `empty_bond_deadlock`
- Model: `sealed_bid_non_reveal_bond_v1`
- Shape: no bonded commits exist after the commit window, so bond accounting must terminate without entering reveal/slash flows.
- Discharge action: `finalize_empty_bonds`

What this catalog does not claim:
- It is not a full liveness proof for all future sealed-bid mechanisms.
- It does not prove economic adequacy of the bond size.
- It does not replace the inductive safety proof; it complements it by covering known terminal-path hazards that invariants alone do not express.
