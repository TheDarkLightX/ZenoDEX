---
title: ZenoDEX Derivative Claim Reconciliation
type: research
date: 2026-09-08
---

# ZenoDEX Derivative Claim Reconciliation

This note corrects the status posture for zero-based registry records 123 through 135 on
the current integration subject. It records evidence availability only. A
disputed status here means the historical assertion is unsubstantiated on this
subject; it does not prove that the described runtime behavior is impossible.

## Subject and provenance

The inspected integration subject is commit
6b6d9289586c19d9b35492137af3baf1369c1ff8. The historical evidence source is
9e0659870f88753dda339d1ffdce1d18d054ae34, with the candidate restoration at
fda433cb5beef0eb159737c0ee0871bc54dbc144. The candidate's matrix/source
artifacts originate at 7ebcead64bc1e28ff54ec8912748b6950dbccf15; the same
matrix/source-document blobs also occur at 71c03e443.

The candidate adds 28 direct registry evidence files. Each direct candidate
blob is byte-identical to the corresponding 9e0659870 blob. Key SHA-256 values
are:

| artifact | SHA-256 |
| --- | --- |
| matrix JSON | 14a16865bd0ea9fb25a90b7783301ddb340adbc684c154a83fb83744cfcbf13c |
| matrix Markdown | 20f4643696b08fae65b37a572ef5dec182e3dcc93dbf75a7cab2c87bdae4aef1 |
| required matrix source document | dfa22bcee603393c42bb11ad9ff560bdb739c3be0c03d4ee92bbca13670f478e |
| current funding-rate source | 9fbc84ecca745b13183aac8045b9db76b6be5b9af4c7ac9508b093afd587f2d7 |
| current curve-selection source | a5b7989f3a9161942da6fc2fdf349719a2835557e7c23700596b068de23fab2a |
| current IL-futures source | 4c96e5f62bfc6e8f8084c9e80ff38f7ac45abc88e9d16853b0132cbcb4f402af |

The candidate commit also carries registry/checker changes and a new generic
receipt module. Those are separate review subjects and were not restored here.

## Corrected registry posture

Records 123 through 135 now have status disputed. Every record ID, command,
file reference, and original historical assertion is preserved. Each statement
starts with a scope sentence identifying its missing evidence. For records
124 through 131, the scope sentence names the missing helper evidence and the
number of missing named pytest nodes:

| record group | missing named nodes or direct evidence |
| --- | ---: |
| funding witness helper, claim 124 | 4 pytest nodes and helper evidence |
| authorized funding helper, claim 125 | 3 pytest nodes and helper evidence |
| production funding dispatcher, claim 126 | 4 pytest nodes and helper evidence |
| curve revenue receipt helper, claim 127 | 3 pytest nodes and helper evidence |
| curve fee/winner receipts, claim 128 | 5 pytest nodes and helper evidence |
| curve pool-event replay, claim 129 | 6 pytest nodes and helper evidence |
| IL reserve/reference receipts, claim 130 | 5 pytest nodes and helper evidence |
| IL settlement authority, claim 131 | 3 pytest nodes and helper evidence |
| generic receipt envelope, claim 132 | source and test files missing |
| FIRE stdlib packet tests, claim 133 | 6 test files missing |
| FIRE release gate, claim 134 | 8 gate/test files missing |
| perps integration gate, claim 135 | 8 assurance scripts missing |

The 33 named nodes are absent from the current funding-rate, curve-selection,
and IL-futures test modules. Their runtime source files are unchanged from the
historical evidence subject. The generic receipt source named by claims 131 and
132 is absent and is not wired into the current IL module.

## Direct missing-path inventory

The 28 unique direct paths named by records 123 through 135 are:

~~~text
docs/derivatives/DERIVATIVES_AUTHORIZATION_COVERAGE_MATRIX.json
docs/derivatives/DERIVATIVES_AUTHORIZATION_COVERAGE_MATRIX.md
src/core/derivative_settlement_receipts.py
tests/core/test_derivative_settlement_receipts.py
tests/kernels/test_cal_fire_logic_package_receipt_binding.py
tests/kernels/test_fire_acceptance_receipt_v1.py
tests/kernels/test_fire_compiler_registry_v1.py
tests/kernels/test_fire_formal_assurance_claims.py
tests/kernels/test_fire_kernel_settlement_v1.py
tests/kernels/test_fire_ledger_adapter_v1.py
tests/kernels/test_fire_object_package_v1.py
tests/kernels/test_fire_release_assurance.py
tests/kernels/test_fire_settlement_apply_report_v1.py
tests/kernels/test_fire_settlement_packet_v1.py
tests/kernels/test_fire_verifier_rules_spec.py
tests/test_derivatives_authorization_matrix.py
tools/check_derivatives_authorization_matrix.py
tools/check_fire_formal_assurance_claims.py
tools/check_fire_release_assurance.py
tools/run_fire_assurance_gate.sh
tools/run_perp_apply_funding_auto_assurance_gate.sh
tools/run_perp_clearinghouse_market_params_assurance_gate.sh
tools/run_perp_market_version_prefix_assurance_gate.sh
tools/run_perp_runtime_risk_gate_assurance_gate.sh
tools/run_perp_signed_surface_assurance_gate.sh
tools/run_perp_submission_auth_assurance_gate.sh
tools/run_perp_tau_ingress_schema_tau_gate.sh
tools/run_perp_tau_ingress_stream_assurance_gate.sh
~~~

The matrix checker also names
docs/derivatives/CERTIFIED_FINANCIAL_MATH_OBJECTS.md, and the FIRE checks
name additional CAL, Lean, receipt, kernel, formal-test, and tool files. These
28 transitive dependencies are present in 9e0659870 and absent from the
candidate tree. They require a separate exact-closure review.

## Unsupported all-area result

The historical matrix data declares all five areas authorization-complete with
27 covered requirements and two explicitly disputed claims. The checker checks
that matrix, registry statuses and source-document presence. It does not verify the named
pytest nodes, import the three market modules, or confirm that helper
constructors are mounted. Therefore a historical matrix replay reporting
areas=5, requirements=27, open_requirements=0, disputed_claims=2 would be an
artifact-consistency result, not valid evidence that all five runtime lanes are
covered on this subject. The corrected disputed statuses make that stale
all-area posture visible in the registry.

## Reproduction and next step

On the current subject, the authoritative registry command is:

~~~text
PYTHONDONTWRITEBYTECODE=1 python3 tools/check_claims_registry.py
~~~

It currently exits 1 with:

~~~text
claims registry invalid: claims[123].evidence.files missing: tools/check_derivatives_authorization_matrix.py
~~~

Independent integration review compared the parsed registry before and after
the correction: all IDs, evidence fields, original statement suffixes and
unaffected records are unchanged. It confirmed the 28 missing direct paths and
33 absent named test definitions, and checked all 56 scoped direct/transitive
provenance entries against Git blobs. This is an evidence-availability review;
it does not execute the missing historical tests. The registry checker remains
unchanged and its failure above remains visible.

After an independently reviewed evidence subject is selected, run the existing
recorded commands without changing them:

~~~text
python3 tools/check_derivatives_authorization_matrix.py
python3 -m py_compile tools/check_derivatives_authorization_matrix.py tests/test_derivatives_authorization_matrix.py
pytest -q tests/test_derivatives_authorization_matrix.py
bash tools/run_fire_assurance_gate.sh
bash tools/run_perps_evidence.sh
~~~

The next task is actual semantic repair and named test implementation for
claims 124 through 131, or a qualified historical recovery whose source,
dependency closure, and runtime bindings are independently replayed. Claim 132
may be reviewed as a generic envelope claim only if its wording remains
separate from IL integration. No production runtime behavior, lane completion,
whole-core completion, or release authorization follows from this status
correction.
