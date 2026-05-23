# Disaster Class Closure Packets

This document explains `tools/disaster_class_closure_packets.json`.

The taxonomy crosswalk says which public failure families map to which ZenoDEX
disaster axes. The closure packets add the next layer: a bad-trace predicate and
the theorem obligations needed before a broad "immune to this class" claim is
valid.

## Current Status

Checked result:

```text
packet_count = 20
crosswalk_entry_count = 20
covered_crosswalk_entry_count = 20
missing_packet_count = 0
extra_packet_count = 0
exact_axis_binding_count = 20
total_bad_trace_condition_count = 60
total_closure_obligation_count = 40
crosswalk_known_axis_count = 125
crosswalk_mapped_axis_count = 125
```

Every public-seeded family in the crosswalk now has:

- a named `BadTrace` predicate;
- a state scope;
- at least three predicate conditions;
- mapping obligations;
- rejection obligations;
- exact binding to the axes listed in the taxonomy crosswalk.

## Proof Shape

The desired theorem has three pieces:

```text
ClassClosure(C) :=
  forall trace, BadTrace_C(trace) -> exists axis in Axes(C), Covers(axis, trace)
```

Every bad trace in class `C` is represented by at least one local ZenoDEX axis.

```text
AxisRejection(C) :=
  forall trace axis,
    Covers(axis, trace) and AxisRejected(axis, trace)
      -> not AcceptedBadTrace(trace)
```

When an axis covers a bad trace and the current implementation rejects that
axis, the bad trace cannot be accepted.

```text
Immunity(C) :=
  ClassClosure(C) and AxisRejection(C)
    -> forall trace, BadTrace_C(trace) -> not AcceptedBadTrace(trace)
```

A class-level immunity claim is valid only after both the coverage theorem and
the rejection theorem are discharged for that class.

## What Is Proved Now

The current packets prove no universal class immunity by themselves. They make
the proof obligations explicit and checkable.

The current checked claim is:

```text
crosswalk family exists -> closure packet exists
closure packet exists -> bad-trace predicate and obligations are declared
closure packet axes = crosswalk axes
crosswalk axes = current disaster-search axes for that family
```

The repo now has a mechanical path from broad public attack families to local
bad-trace predicates and local replay/proof obligations. That is the bridge
needed before the stronger theorem can be proved class by class.

## Replay

Run the checker:

```bash
python3 tools/check_disaster_class_closure_packets.py
```

JSON output:

```bash
python3 tools/check_disaster_class_closure_packets.py --format json
```

The checker also invokes the taxonomy-crosswalk checker. It fails if:

- the crosswalk is invalid;
- a crosswalk family lacks a closure packet;
- a closure packet references a missing crosswalk family;
- a packet has no formal bad-trace predicate;
- a predicate has too few state fields or conditions;
- obligations omit mapping or rejection duties.

## How To Promote A Packet

Promotion path:

1. Turn `BadTrace_C` into a formal trace predicate in Lean, ESSO, TLA+, or a
   bounded executable model.
2. Prove or model-check the class-closure theorem:
   `BadTrace_C(trace) -> exists axis, Covers(axis, trace)`.
3. Prove or replay the axis-rejection theorem against the runtime guard.
4. Link the proof or replay receipt into the packet.
5. Only then claim class-level immunity under the declared model bounds.

This keeps public claims honest: taxonomy mapping is not immunity; closure plus
rejection evidence is.

## Lean Rule

The generic proof rule is machine-checked in
[`lean-mathlib/Proofs/DisasterClassClosure.lean`](../lean-mathlib/Proofs/DisasterClassClosure.lean).

It proves:

```text
ClassClosure(C) and AxisRejectionComplete(C) and AxisRejectionSound(C)
  -> ClassImmune(C)
```

It also proves the counterexample-search form:

```text
BadTrace_C(trace) and AcceptedBadTrace(trace)
  -> exists covering axis that was not rejected
```

This gives fuzzing and proof search a precise target: any accepted bad trace
must either break the class-closure mapping or expose a local axis whose
rejection guard is incomplete.
