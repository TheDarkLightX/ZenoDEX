# Mathematical assessment and ranking

## 1. Exact object

Let `I` be a finite, canonically ordered set of named choices. A named
choice-fiber polynomial is

```text
f(epsilon) = sum over S subset I of c[S] product over i in S epsilon[i]
epsilon[i] in {-1, +1}.
```

Every syntactic occurrence names a base choice and a polarity. Two occurrences
with the same base identity share one coordinate. Distinct base identities are
independent only under the uniform assignment projection used by this packet.
Repeated factors reduce by `epsilon[i]^2 = 1`, so monomial multiplication is
symmetric difference.

The reference model maintains four distinct identities:

```text
choice manifest root   closed base choices and occurrence aliases
semantic root          unique named multilinear function
lineage root           exact ordered source-term decomposition
complete root          manifest + semantic function + lineage
```

Equal semantic roots do not imply equal provenance.

## 2. Established mathematics

This object is a pseudo-Boolean function in its unique multilinear form, or a
Fourier-Walsh polynomial after choosing the `{-1,+1}` basis. The affine case is
also close to correlation-sensitive affine arithmetic, with discrete signs in
place of interval-valued noise symbols.

Primary boundaries:

- Ryan O'Donnell, *Analysis of Boolean Functions*, Fourier expansion:
  <https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf>
- Endre Boros and Peter Hammer, *Pseudo-Boolean Optimization*:
  <https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/2001/2001-33.html>
- Jorge Stolfi and Luiz de Figueiredo, correlation-sensitive affine arithmetic:
  <https://www.ic.unicamp.br/~stolfi/EXPORT/projects/affine-arith/Welcome.html>
- Exact dynamic programming on tree-structured graphical models:
  <https://web.stanford.edu/~montanar/TEACHING/Stat375/notes-old/lecture-2.pdf>
- Algebraic and functional decision diagrams provide alternative canonical
  compressed representations:
  <https://ojs.aaai.org/index.php/AAAI/article/download/4140/4018>

Consequently, neither the polynomial nor the minimization algorithms support a
novelty claim. The exact source/authority binding is an engineering combination
that would require a much deeper prior-art review before even a provisional
novelty hypothesis.

## 3. Exact compression theorems

### Affine theorem

For

```text
f(epsilon) = c + sum_i h[i] epsilon[i],
```

the exact minimum is

```text
min f = c - sum_i abs(h[i]).
```

Choose `epsilon[i] = -1` when `h[i] >= 0`, and `+1` otherwise. Each coordinate
is independent and attains its individual lower bound. Construction and
verification are linear in the number of choices and terms.

### Pairwise-forest theorem

For

```text
f(epsilon) = c + sum_i h[i] epsilon[i]
               + sum_(i,j) J[i,j] epsilon[i] epsilon[j]
```

whose nonzero interaction graph is a forest, root each component canonically.
For a node `v` and fixed parent-side sign `s`, define

```text
DP[v,s] = h[v] s
          + sum over children u min over t in {-1,+1}
              (DP[u,t] + J[v,u] s t).
```

Induction on subtree height proves that `DP[v,s]` is its exact conditional
minimum. Summing the independently minimized roots and adding `c` gives the
global minimum. The table and verifier are linear in vertices and edges.

### Disconnected-component theorem

If the interaction hypergraph has components `C_1,...,C_k`, every nonconstant
term belongs to exactly one component. Therefore

```text
min f = c + sum_j min f restricted to C_j.
```

Exhaustive verification costs

```text
sum_j 2^|C_j| * local_term_count[j]
```

instead of `2^n`. This remains exponential in the largest component.

### Hardness boundary

General pairwise minimization includes weighted Max-Cut. For signs `epsilon`,

```text
cut(epsilon) = sum_(i,j) w[i,j] (1 - epsilon[i] epsilon[j]) / 2.
```

Maximizing this cut is equivalent to minimizing the corresponding quadratic
sign polynomial. No general polynomial-size exact certificate or verifier is
claimed. Treewidth-based dynamic programming is the established next extension.

## 4. Permanent falsifiers

The experiment retains four decisive mutants:

1. Correlation erasure: `1 + x - y` has minimum `-1` for independent `x,y`
   and minimum `1` when both occurrences share one identity.
2. Dropped nonlinear interaction: `2 + x + y - 3xy` has true minimum `-3`;
   its affine projection has minimum `0`.
3. Dropped cycle edge: `2 + xy + yz - 3xz` has minimum `-3`; deleting the
   closing interaction produces a forest with minimum `0`. The forest gate
   must reject the original cycle.
4. Repointed certificate: a certificate bound to one exact manifest and
   polynomial rejects under a changed coefficient or occurrence namespace.

These show that compact syntax without correlation identity or interaction
closure can falsely certify a governance policy as robust.

## 5. Duplex-number claim boundary

The flat expression `a +/- b_1 +/- ... +/- b_n` is exactly the affine fragment.
It represents labeled assignments, possibly with duplicate numerical values.
It does not represent every finite symmetric set. For example, suppose

```text
{+/-1, +/-2, +/-4, +/-8} = {+/-b +/-c +/-d}.
```

Take nonnegative `b,c,d` and let `b+c+d=8`. The other three absolute values
would be `|8-2b|`, `|8-2c|`, and `|8-2d|`, hence `1,2,4` in some order. This
would require a signed sum of `1,2,4` to equal `-8`, but every such signed sum
is odd and has magnitude at most `7`. Contradiction.

Multiplication also exits the affine fragment because it creates interaction
monomials. Retaining those monomials is exact; discarding them is an
approximation that requires a separate bound.

## 6. Alignment and governance use

For a fixed, authenticated choice manifest, let `f(epsilon)` be the safety or
alignment margin under stakeholder choices, coalition behavior, oracle states,
or bounded market shocks. The certificate establishes

```text
minimum over all admitted epsilon of f(epsilon) >= required_margin.
```

This is useful when the model is affine, tree-structured, bounded-treewidth, or
decomposes into small independent coalitions. The certificate does not establish
that the model is complete, that an open population is Sybil-resistant, or that
the coefficients represent real utility. Those are separate premises.

Recommended division:

```text
Tau / formal logic      judges the constitutional predicates
choice-fiber polynomial evaluates bounded numerical scenario families
ZenoLedger              owns roster, occurrence, and evidence lineage
ZRPF                    may aggregate coverage of disjoint scenario fibers
deterministic verifier  recomputes the certificate and owns acceptance
```

## 7. Ranked result

1. **High utility: shared-choice-identity-safe scenario language.** It prevents
   shared and independently enumerated choices from being silently
   interchanged.
2. **High utility: pairwise-forest robustness certificate.** It changes exact
   verification from exponential to linear on a meaningful structural class.
3. **Moderate utility: component-factor certificate.** It gives fixed-parameter
   exact verification when coalition blocks remain small.
4. **Potential ZRPF utility: disjoint-fiber aggregation.** Each component can
   be proved separately and combined after exact coverage and disjointness
   checks. This integration remains unimplemented.
5. **Low novelty: generic named polynomial.** Its mathematical content is
   established pseudo-Boolean/Fourier-Walsh optimization.
6. **Unsafe/useless as stated: universal compact circuit verification.** Dense
   nonlinear interactions recover NP-hard optimization and can force
   exponential representations.

Final classification:

```text
USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL
```

Preserve it as research and test-generation infrastructure. Do not mount it as
M6, settlement, governance, or promotion authority.
