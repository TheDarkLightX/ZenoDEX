---
title: math_object_innovation_v195
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v195
---

# v195 Assumption-Change Override Packet Language

## Structural Target

```text
assumption_change_override_packet_language_v1
```

This cycle sharpens the v194 override branch. It searches for the smallest
exact witness language in which an assumption-change override is locally
checkable on a bounded adversarial corpus.

```text
Good(packet) <-> every required override atom is true
```

In plain English: an override packet is accepted only when it binds the right
domain, surface, cap reference, nonce, signer threshold, registry root, epoch,
and no-user-net-claim acknowledgement.

## Bounded Domain

The corpus contains:

- `13` override packets,
- `2` valid packets,
- `11` invalid packets,
- `8` candidate atoms.

Required atoms:

- `domain_ok`
- `surface_binding_ok`
- `cap_reference_ok`
- `assumption_nonce_fresh`
- `signer_threshold_ok`
- `registry_root_ok`
- `epoch_freshness_ok`
- `no_user_net_ack_ok`

## Acceptance Rules

```text
Exact(L) := accepts_L(packet) <-> expected_good(packet)
```

In plain English: a language is exact only if it accepts both good packets and
rejects every adversarial packet in the bounded corpus.

```text
PrivateWitness(atom) := an invalid packet fails only that atom
```

In plain English: every required atom is forced because removing it would accept
at least one concrete bad packet.

## Claim Tier

```text
tier = symbolic_state_compiler
oracle_dependent = true
```

This is a bounded witness-language result. It is not a cryptographic
implementation and does not prove all governance attacks impossible.

## Replay

```bash
python3 experiments/math_object_innovation_v195/run_cycle.py
pytest -q experiments/math_object_innovation_v195/test_v195_cycle.py
```

## Current Result

```text
packet_count = 13
valid_packet_count = 2
invalid_packet_count = 11
atom_count = 8
forced_atom_count = 8
minimal_exact_language_count = 1
minimal_exact_atom_count = 8
total_override_language_invariant_failures = 0
```

Weaker languages such as text-only, authority-only, fresh-authority-only, and
cap-and-ack-only all false-accept adversarial packets. The full eight-atom
packet language is the unique minimal exact language on this corpus.
