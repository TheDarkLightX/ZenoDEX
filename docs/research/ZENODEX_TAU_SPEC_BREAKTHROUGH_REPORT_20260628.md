# ZenoDEX Tau Specification Breakthrough Report - 2026-06-28

## Executive Result

Research Kernel run `zenodex-tau-spec-breakthrough-20260628` produced a
supported Tau-specification breakthrough set for ZenoDEX:

- `tauspec_ebrm_frontier_selection_certificate_v1.tau` selects high-value Tau
  specs from a bounded candidate pool using replay status, invalid-accept
  count, profile budget, novelty, projected facts, and negative-case rejection.
- `ab_cow_exact_solver_envelope_v1.tau` covers work items 1 and 2: AB ordering
  and CoW matching certificates.
- `route_split_window_certificate_v1.tau` gates a local-window route-split
  certificate with bounded full-oracle parity.
- `oracle_polytope_frontier_envelope_v1.tau` gates exact one-field oracle
  economic-security intervals with boundary replay and explicit assumptions.
- `frontier_certificate_menu_v1.tau` gives the shared one-hot certificate menu
  that lets these optimizer and mechanism-design envelopes use the same Tau
  admission shape.

Authority boundary: Tau validates host-projected certificate facts. It does not
authorize settlement, oracle updates, governance changes, or state transitions.

## Supported Research Kernel Claims

| claim | status | promotion |
| --- | --- | --- |
| Solver-portfolio Tau certificate for AB and CoW | `SUPPORTED` | prior run promotion in `zenodex-tau-spec-breakthrough-20260628` |
| AB/CoW exact solver envelope dependency | `SUPPORTED` | `promotion_233f1ef2cbc44af8` |
| Route-split window certificate dependency | `SUPPORTED` | `promotion_322dec008d1a43d6` |
| TauSpec EBRM frontier selector | `SUPPORTED` | prior run promotion in `zenodex-tau-spec-breakthrough-20260628` |
| Bounded oracle-polytope certificate | `SUPPORTED` | `promotion_711299be76c04e01` |

The oracle-polytope lane first produced an overbroad atom that was deliberately
refuted by Cartesian-box counterexamples. The promoted claim is the bounded
version: one varied field at a time, boundary-wall replay, point-verifier
parity, explicit MEV/probability assumptions, and no oracle-update authority.

## What Tau Language Adds

Tau is useful here because it makes high-value optimizer claims carry a small,
auditable proof surface:

1. One-hot mode selection prevents mixed certificate modes.
2. Required host facts are explicit and fail closed when missing.
3. No-authority rails are checked in the same certificate as replay facts.
4. Negative cases become executable Tau traces, not prose-only caveats.
5. Different algorithms can share one certificate menu while keeping their
   arithmetic in deterministic host verifiers.

The practical design pattern is:

```text
host verifier facts + bounded replay + no-authority fact -> Tau certificate admit
```

The certificate admit is advisory. The deterministic ZenoDEX kernel still owns
execution, state roots, balances, oracle updates, and settlement.

## Work Item 1: AB Ordering

`ab_cow_exact_solver_envelope_v1.tau` now gates the AB ordering track with these
host-projected facts:

- optimizer mode is exactly AB ordering;
- objective binding is present;
- full-state DP or bounded brute-force scope is declared;
- brute-force or DP parity is present for the bounded replay lane;
- deterministic tie handling is declared;
- balance, reserve, and slippage facts are present;
- resource budget and fallback bounds are explicit;
- the certificate has no settlement authority.

Research boundary: a compressed one-record Held-Karp state was rejected as unsafe
for integer CPMM AB ordering. The supported direction is full-state subset DP or
bounded exact replay, with fallback after the declared state cap.

## Work Item 2: CoW Matching

The CoW part of `ab_cow_exact_solver_envelope_v1.tau` gates the clean assignment
subcase:

- uncoupled sender-capacity scope is required;
- objective and deterministic tie facts are bound;
- assignment or bounded exact parity evidence is required;
- grouped sender-capacity batches must use a separate bounded search or
  fail-closed fallback;
- the Tau output cannot settle the batch by itself.

Research boundary: Hungarian-style assignment is the right reformulation for the
uncoupled CoW pair problem. Arbitrary grouped-capacity CoW matching is not
claimed polynomial under this spec.

## Oracle Polytope Certificate

The new supported bounded oracle claim uses
`oracle_polytope_frontier_envelope_v1.tau`.

Replay evidence:

- `python3 tools/zenodex_oracle_polytope_compiler_20260627.py`
  - `ok true`
  - `intervals=17`
  - `boundary_samples=68`
- `python3 tools/zenodex_oracle_polytope_box_refuter_20260627.py`
  - `ok true`
  - `cartesian_promotion_refuted true`
  - `counterexample_count=3`
- `python3 tools/zenodex_oracle_assumption_boundary_refuter_20260627.py`
  - `ok true`
  - `case_count=8`
  - `false_declared_admit_count=7`
  - `computed_false_admit_count=0`

The certificate admits only when interval nonemptiness, honest challenge
profitability, frivolous-dispute deterrence, slash coverage, point-verifier
parity, boundary-wall replay, external-assumption disclosure, no update
authority, and fail-closed defaults all hold.

Non-claims:

- no Cartesian interval product;
- no truth estimator;
- no MEV estimator;
- no replacement for the pointwise verifier;
- no oracle-update authority.

## Verification

Focused replay passed:

```bash
python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py
python3 tools/zenodex_tau_route_split_window_breakthrough_20260628.py
python3 tools/zenodex_oracle_polytope_compiler_20260627.py
python3 tools/zenodex_oracle_polytope_box_refuter_20260627.py
python3 tools/zenodex_oracle_assumption_boundary_refuter_20260627.py
pytest -q tests/test_zenodex_ab_cow_algorithm_breakthrough_20260627.py tests/tau/test_zenodex_tau_route_split_window_breakthrough_20260628.py
pytest -q tests/test_zenodex_oracle_polytope_compiler_20260627.py tests/test_zenodex_oracle_polytope_box_refuter_20260627.py tests/test_zenodex_oracle_assumption_boundary_refuter_20260627.py tests/tau/test_zenodex_tau_breakthrough_specs_20260627.py
```

Observed focused pytest results:

- AB/CoW and route-split bundle: `4 passed in 20.17s`
- Oracle polytope bundle: `12 passed in 18.33s`

## Next Frontier

Research Kernel frontier after these promotions is mostly negative-trace replay:

- mutate each required certificate fact and require rejection;
- keep AB compressed-state claims out of the supported set until a state
  equivalence proof exists;
- keep grouped-capacity CoW under bounded exact search or fallback;
- extend the oracle-polytope compiler from one-field intervals to a coupled
  region only if cross-field inequalities or an exact region verifier are added.
