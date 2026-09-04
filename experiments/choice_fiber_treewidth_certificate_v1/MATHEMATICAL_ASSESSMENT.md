# Mathematical assessment

## 1. Object

Let `I` be a finite ordered choice manifest and let

```text
f(epsilon) = sum over S subset I of c[S] product over i in S epsilon[i]
epsilon[i] in {-1,+1}.
```

A scope `q` fixes a subset `F` of the coordinates. Its exact projection is

```text
S_free = S minus F
c_q[S_free] += c[S] * product over i in S intersect F of q[i].
```

Equal projected monomials are coalesced. Zero totals disappear from the
semantic projection, while a separate lineage root retains every contributing
source term and substitution.

## 2. Scope substitution theorem

For every complete assignment `epsilon` extending `q`,

```text
f(epsilon) = f_q(epsilon restricted to I minus F).
```

Proof: split each monomial product into its fixed and free factors. The fixed
product is absorbed into `c_q`; summing all source terms that reach the same
free monomial preserves the total. This proof also explains why deleting a
fixed factor or forgetting its sign is unsound.

The retained counterexample is

```text
f(x,y) = 1 - y + xy
q fixes x = -1
f_q(y) = 1 - 2y
minimum = -1.
```

## 3. Derived elimination decomposition

For each nonconstant projected term, connect all of its choices into a primal
clique. Given a full order of the free choices, eliminate each choice `v_i`:

```text
N_i      = live filled neighbors of v_i
B_i      = {v_i} union N_i
parent_i = earliest later choice in N_i, or the synthetic root
```

Before removing `v_i`, fill `N_i` into a clique. A term is owned by its
earliest-eliminated choice. Its complete support lies in that owner's bag.
The fill construction also gives the running-intersection property, with
separator `N_i` carried to the parent bag.

The verifier derives this structure. It proves only that the supplied order
has induced width at most the profile limit. It does not prove minimum
treewidth.

## 4. Separator-message theorem

For a node `i` and separator assignment `a`, define

```text
m_i(a) = min over s in {-1,+1} of
           local_owned_factors(a, v_i=s)
         + sum over children j of m_j((a, v_i=s) restricted to N_j).
```

Induction over the derived elimination forest proves that `m_i(a)` is the
exact conditional minimum of all factors in the subtree rooted at `i`.
Adding the projected constant and the root messages yields the exact scoped
minimum. Ties retain the lexicographically least manifest-ordered assignment.

Separator conditioning is essential. For

```text
f(y,z) = y + z + yz,
```

the exact minimum is `-1`. Independently minimizing overlapping owner bags and
adding those values reports the impossible lower value `-3`.

## 5. Coverage aggregation theorem

Let the subcubes `C_1,...,C_L` form an exact partition of the complete choice
cube. Then

```text
min over epsilon of f(epsilon)
  = min over leaves l of min over epsilon in C_l of f(epsilon).
```

The existing canonical ZRPF coverage checker proves the finite set partition.
This verifier derives its ordinal manifest from the polynomial manifest and
uses one structurally paired `(scope, scoped result)` leaf value. Separate
parallel scope and result tuples are not admitted.

## 6. Complexity and hardness boundary

For leaf `l`, let `w_l` be the induced width and `n_l` the free-choice count.
The message-cell bound is

```text
C_l = sum_i 2^|N_i| <= n_l * 2^w_l.
```

Runtime also includes local-factor evaluation, assignment reconstruction, fill
derivation, and exact coverage checking. All leaf work is charged against one
aggregate request budget.

General pairwise pseudo-Boolean minimization includes weighted Max-Cut, so no
general compact exact result follows from this packet. The useful class is
bounded induced width, possibly distributed across exact subcube fibers.

## 7. Prior-art and value assessment

The mathematical ingredients are established:

- pseudo-Boolean optimization and multilinear representations;
- variable elimination and tree decompositions;
- junction-tree or bucket-elimination dynamic programming;
- exact set partitions and recursive subcube aggregation.

Useful references include:

- Boros and Hammer, *Pseudo-Boolean Optimization*:
  <https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/2001/2001-33.html>
- O'Donnell, *Analysis of Boolean Functions*:
  <https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf>
- Dechter, *Bucket Elimination: A Unifying Framework for Reasoning*:
  <https://www.ics.uci.edu/~dechter/publications/r8.pdf>

The result is valuable because it closes exact identity and coverage seams
between two existing ZenoDEX research objects. No present evidence supports a
novelty claim.

## 8. Promotion boundary

The Python verifier provides deterministic bounded evidence. It assumes Python
process integrity and has no cryptographic receipt backend. Its declared source
digest becomes source evidence only when the separate packet checker validates
the loaded file bytes. Runtime replay cannot attest its own mutable code. It neither proves
that a model is a complete constitution nor authorizes a governance decision.
It must remain outside settlement and publication authority.

Final classification:

```text
USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL
BOUNDED_RESEARCH_ONLY
Authority: NONE
```
