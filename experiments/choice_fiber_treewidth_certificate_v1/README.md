# Choice-fiber treewidth coverage certificate V1

This bounded reference verifier connects two earlier research objects:

1. a canonical named pseudo-Boolean polynomial whose semantic and exact
   lineage identities remain separate;
2. a canonical ZRPF subcube certificate whose leaves exactly partition the
   admitted choice cube.

For every subcube leaf, the verifier substitutes its fixed signs into the
exact polynomial, derives a filled elimination graph from one complete order,
and computes exact separator messages. It then pairs the scope and its result
inside one leaf-evidence value and reuses the ZRPF coverage checker to establish
that every complete assignment belongs to exactly one leaf.

The final result is

```text
global minimum = minimum of the exact leaf minima.
```

The verifier derives all bags, separators, parents, factor owners, message
tables, and the ZRPF ordinal manifest. Those values are not caller inputs.

## Exact contract

The untrusted request contains only:

```text
claim context root
exact named polynomial
complete elimination order
canonical subcube coverage plan
exact verifier profile
```

The verifier returns an immutable outcome containing the fully replayable
evidence and a small structurally minted receipt:

```text
VerifiedTreewidthCoverageV1(
  verification_subject_root,
  evidence_root,
  result_root,
)
```

The receipt always reports:

```text
authority    = NONE
claim_status = BOUNDED_RESEARCH_ONLY
backend      = PYTHON_REFERENCE_REPLAY
```

Python constructor privacy is only a process-local structural boundary. A
consumer crossing a process or durability boundary must retain the exact
request and run `reverify_treewidth_coverage`. A claim about the executing
verifier source additionally requires the external `check_packet` gate, which
compares loaded source bytes with the digest declared by the verifier profile.
Runtime replay does not self-attest mutable Python code. No cryptographic
receipt is implemented here.

## Resource profile

The exact verifier admits at most 256 named choices and 256 subcube leaves.
The derived induced width is capped at 12. Aggregate message cells, work units,
fill probes, projection visits, coefficient magnitude, and independent
brute-force oracle work all have explicit fail-closed limits. The preflight
runs before message enumeration.

The retained complexity is

```text
message cells <= sum over leaves and vertices of 2^separator_size
```

so this is fixed-parameter exact verification for small induced width. It does
not claim an optimal elimination order or general polynomial-time behavior.

## Replay

From the repository root:

```bash
python3 -m pytest -q \
  experiments/choice_fiber_treewidth_certificate_v1/test_treewidth_certificate.py
python3 -m experiments.choice_fiber_treewidth_certificate_v1.run_experiment
python3 -m experiments.choice_fiber_treewidth_certificate_v1.check_packet
python3 -m ruff check experiments/choice_fiber_treewidth_certificate_v1
python3 -m ruff format --check experiments/choice_fiber_treewidth_certificate_v1
python3 -m mypy --strict --explicit-package-bases \
  experiments/choice_fiber_treewidth_certificate_v1/treewidth_certificate.py \
  experiments/choice_fiber_robustness_v1/named_choice_fiber.py \
  experiments/zrpf_choice_subcube_coverage_v1/subcube_certificate.py
```

## Claim boundary

Tree decomposition, variable elimination, junction-tree messages,
pseudo-Boolean optimization, and subcube aggregation are established methods.
This exact source, scope, lineage, and coverage integration is useful research
engineering. It supports no novelty, cryptographic soundness, universal
compactness, M6 completion, governance authority, settlement authority, or
production-readiness claim.

ZRPF may prove computation. ZenoLedger remains the only component permitted to
select and publish an economic head.
