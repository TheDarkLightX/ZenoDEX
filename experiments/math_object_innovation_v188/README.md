# v188 Gasper-Cone Jacobi Turan Orientation

## Structural Target

This cycle repairs the v186 asymmetric Jacobi Turan failure by testing a
cone-sensitive endpoint normalization.

For rational `alpha,beta >= 0`, define the shifted Jacobi polynomial:

```text
J_{n,alpha,beta}(x) = P_n^(alpha,beta)(2*x - 1)
```

The right-endpoint normalized form is:

```text
R_n^+(x) = J_n(x) / J_n(1)
```

The left-endpoint normalized form is:

```text
R_n^-(x) = J_n(x) / J_n(0)
```

The tested Turan obligation is:

```text
forall x in [0,1],
  R_n(x)^2 - R_{n-1}(x) * R_{n+1}(x) >= 0
```

The candidate recognizer is:

```text
if beta >= alpha:
  use right endpoint normalization
else:
  use left endpoint normalization
```

This is motivated by the Jacobi Turan parameter-cone literature. DLMF
§18.14(ii) lists the Jacobi Turan-type inequality with Gasper as a reference,
and the surrounding literature states the normalized-at-1 cone in terms of
`beta >= alpha`.

## Bounded Domain

- Parameters:
  - `(alpha,beta)` in
    `{(0,0), (1/2,0), (0,1/2), (1,0), (0,1), (1,2), (2,1),
      (1/2,3/2), (3/2,1/2), (2,3), (3,2), (1,1), (2,2),
      (1/3,2/3), (2/3,1/3), (0,2), (2,0), (1/2,2),
      (2,1/2), (3,5), (5,3)}`.
- Degree index:
  - discovery: `1 <= n <= 10`,
  - holdout: `11 <= n <= 18`.
- Certificate candidates:
  - equal Bernstein subdivisions in `{1,2,4,8,16,32,64,128}`.
- Negative controls:
  - constant `-1`,
  - `x - 1/2` over `[0,1]`,
  - negative oriented Turan at `(alpha,beta,n)=(1,2,4)`,
  - negative oriented Turan at `(alpha,beta,n)=(2,1,5)`.

## What Is Being Compared

The scan records four anchor choices:

- `right`: normalized at `x = 1`, expected only when `beta >= alpha`.
- `left`: normalized at `x = 0`, expected only when `alpha >= beta`.
- `oriented`: choose the endpoint compatible with the parameter cone.
- `wrong`: choose the opposite endpoint for strict asymmetric pairs.

The important distinction is between certificate failure and mathematical
falsification. The v186 failure was not just a weak Bernstein certificate. The
strict wrong-endpoint cases have exact negative endpoint values.

## Claim Tier

`symbolic_state_compiler`.

This cycle produces a bounded theorem-recognizer shape plus exact certificates.
It does not prove Gasper's full theorem. It gives a practical dispatch rule:
inside the cone, emit a compact Bernstein certificate; outside the cone, do not
try to rescue the formula by subdividing more.

## Run

```bash
python3 run_cycle.py
pytest -q test_cycle.py
```

`run_cycle.py` invokes `run_cycle.jl`, writes `generated/raw.tsv`, and builds
`generated/report.json`.

## Reference Anchors

- DLMF inequalities for classical orthogonal polynomials:
  `https://dlmf.nist.gov/18.14`
- DLMF Chapter 18, classical orthogonal polynomial conventions:
  `https://dlmf.nist.gov/18`
- Gasper/Szego Jacobi Turan cone references, used as theorem-search guidance,
  not as local proof evidence.
