import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

/-- **Kőnig's theorem** (vertex-cover form) for a finite bipartite graph given by its edge set
`E ⊆ A × B`. A *matching* is a set of edges `M ⊆ E` on which both projections are injective
(no two edges share a left endpoint or a right endpoint). If every matching in `E` has at most
`k` edges, then there is a *vertex cover* `KA ⊆ A`, `KB ⊆ B` (every edge of `E` has its left
endpoint in `KA` or its right endpoint in `KB`) with `|KA| + |KB| ≤ k`. -/
theorem konig {A B : Type*} (E : Finset (A × B)) (k : ℕ)
    (hk : ∀ M ⊆ E, Set.InjOn Prod.fst (M : Set (A × B)) →
      Set.InjOn Prod.snd (M : Set (A × B)) → M.card ≤ k) :
    ∃ KA : Finset A, ∃ KB : Finset B,
      (∀ e ∈ E, e.1 ∈ KA ∨ e.2 ∈ KB) ∧ KA.card + KB.card ≤ k := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
