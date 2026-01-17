import Proofs.MSTCertificateNoImprovingExchange

/-!
MST certificate “main statement” (Mathlib-backed, step 6)

This file packages the certificate we use in our MST checker domain into a single Lean predicate.

We still have not completed the full global theorem “certificate ⇒ minimum spanning tree among all
spanning trees”; that requires a full exchange-sequence / induction-on-symmetric-difference
development. What we *do* have mechanized here is the strongest local optimality fact:

> For every off-tree edge (u,v), the certificate implies there is no beneficial 1-edge exchange on
> the unique u-v path.

This predicate + local theorem is already enough to:
- justify the checker logic in the corresponding Python checker, and
- serve as the lemma layer for the eventual global optimality theorem.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} [DecidableEq V]

variable (G T : SimpleGraph V) (w : Sym2 V → Nat)

/- MST certificate predicate for a candidate tree `T ≤ G`, parameterized by a tree proof.
   (We avoid any `admit`/`sorry` by making the tree hypothesis explicit.) -/
def CertificateWithTree (hT : T.IsTree) : Prop :=
  T ≤ G ∧
  (∀ u v : V, u ≠ v → G.Adj u v → ¬ T.Adj u v →
    maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v))

theorem CertificateWithTree.noImprovingExchange
    (hT : T.IsTree)
    (hcert : CertificateWithTree (G := G) (T := T) (w := w) hT)
    {u v : V} (huv : u ≠ v)
    (hG : G.Adj u v) (hTuv : ¬ T.Adj u v)
    {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) (w := w) hT u v) :
    w e ≤ w s(u, v) := by
  rcases hcert with ⟨h_le, hbound⟩
  have hcert_uv : maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v) :=
    hbound u v huv hG hTuv
  exact no_improving_exchange_along_path (T := T) (w := w) hT u v hcert_uv he

end MST
end TauSwap
