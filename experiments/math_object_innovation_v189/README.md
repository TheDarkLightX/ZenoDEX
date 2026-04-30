# v189 Jacobi Turan Endpoint Obstruction Formula

## Structural Target

This cycle extracts the exact endpoint obstruction behind the v188
Gasper-cone orientation rule.

Let:

```text
C(n,gamma) = binom(n + gamma, n)
```

For right-endpoint normalization:

```text
R_n^+(x) = P_n^(alpha,beta)(2*x - 1) / P_n^(alpha,beta)(1)
```

the opposite endpoint is:

```text
R_n^+(0) = (-1)^n * C(n,beta) / C(n,alpha)
```

The Turan value at `x=0` is:

```text
T_n^+(0)
  = R_n^+(0)^2 - R_{n-1}^+(0) * R_{n+1}^+(0)
  = (C(n,beta)/C(n,alpha))^2
    * (beta - alpha) / ((n + alpha + 1) * (n + beta))
```

For left-endpoint normalization:

```text
R_n^-(x) = P_n^(alpha,beta)(2*x - 1) / P_n^(alpha,beta)(-1)
```

the mirrored endpoint formula is:

```text
T_n^-(1)
  = R_n^-(1)^2 - R_{n-1}^-(1) * R_{n+1}^-(1)
  = (C(n,alpha)/C(n,beta))^2
    * (alpha - beta) / ((n + beta + 1) * (n + alpha))
```

For `alpha,beta >= 0` and `n >= 1`, the denominators are positive. Therefore:

```text
sign(T_n^+(0)) = sign(beta - alpha)
sign(T_n^-(1)) = sign(alpha - beta)
```

This explains why the strict wrong endpoint in v188 is not a certificate
weakness. It is mathematically false at the endpoint.

## Bounded Domain

The Julia replay checks direct endpoint evaluation against the closed formula
for:

- `alpha,beta` in `{0, 1/3, 1/2, 2/3, 1, 3/2, 2, 3, 5}`,
- `1 <= n <= 64`,
- both right and left endpoint normalizations.

That gives `10368` exact rational rows.

## Claim Tier

`symbolic_state_compiler`.

The formula is a proof-shaped local theorem and an executable recognizer
prefilter. It is not the full Jacobi Turan theorem inside the cone.

## Run

```bash
python3 run_cycle.py
pytest -q test_cycle.py
```

`run_cycle.py` invokes `run_cycle.jl`, writes `generated/raw.tsv`, and builds
`generated/report.json`.

## Lean Promotion

The algebraic endpoint-ratio skeleton has a checked Lean packet:

- `lean-mathlib/Proofs/JacobiTuranEndpointObstruction.lean`
- `lean-mathlib/proof_receipts/jacobi_turan_endpoint_obstruction_v1.json`

Closed theorem surface:

- `right_endpoint_obstruction_formula`
- `left_endpoint_obstruction_formula`
- `right_endpoint_obstruction_nonneg_of_alpha_le_beta`
- `right_endpoint_obstruction_negative_of_beta_lt_alpha`
- `left_endpoint_obstruction_nonneg_of_beta_le_alpha`
- `left_endpoint_obstruction_negative_of_alpha_lt_beta`

Checker:

```bash
cd ../../lean-mathlib
lake env lean Proofs/JacobiTuranEndpointObstruction.lean
```

This proves the small ratio identity behind the endpoint obstruction and the
sign consequences used by a fail-closed cone prefilter. It still does not prove
full interval positivity inside the Gasper cone.

## Reference Anchors

- DLMF Chapter 18, Jacobi polynomial conventions:
  `https://dlmf.nist.gov/18`
- DLMF §18.14(ii), Turan-type inequalities:
  `https://dlmf.nist.gov/18.14`
- Gasper/Szego parameter-cone literature, used as theorem-shape guidance.
