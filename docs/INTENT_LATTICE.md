# Intent Lattice & Equivalence Harness (Draft)

This project uses an **intent lattice** to bridge the gap between “spec is valid” and “spec matches intended behavior.”

## What is an Intent Lattice?
A ladder of intent levels, each stronger than the last:
1. **Well-formedness** - outputs defined, types consistent, no contradictions.
2. **Safety invariants** - no underflows, no stale oracles, bounds respected.
3. **Accounting invariants** - conservation of balances, fee splits sum correctly.
4. **Behavioral intent** - exact swap math, state transition equivalence.
5. **Equivalence** - spec == formal model (proof-level assurance).

Each level is a **formal predicate**. We check:
- `Spec ⇒ Intent_L1 ⇒ Intent_L2 ⇒ Intent_L3 …`

## Why this helps
- Lets us **prove the most important properties first**.
- Makes audits compositional (module by module).
- Surfaces gaps when specs don’t imply intended invariants.

## Equivalence Harness
We ship a harness that provides:
- **Trace analysis** (Tau execution vs Python model)
- **Optional Z3 equivalence checks** (if z3-solver is installed)
- **Intent checks** (spec must imply high-level safety predicates)

### Run
```bash
python3 tools/intent_harness.py --spec all --mode both --traces 50
```

### Notes
- Z3 checks require `z3-solver`.
- Trace checks require a Tau binary (`external/tau-lang/build-Release/tau`).

## Next steps
- Add intent layers for more specs (settlement, governance, fee modules).
- Formalize a “golden model” for settlement and batch clearing.
