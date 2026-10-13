import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

theorem lemma_3_2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (T : Finset (I × J)) (D : Matrix I J ℝ) (hD : ∀ i j, (i, j) ∉ T → D i j = 0)
    (hmax : ∀ D' : Matrix I J ℝ, (∀ i j, (i, j) ∉ T → D' i j = 0) → D'.rank ≤ D.rank)
    (x : J → ℝ) (hx : D.mulVec x = 0) (y : I → ℝ) (hy : D.transpose.mulVec y = 0)
    (s : I) (j : J) (hsj : (s, j) ∈ T) : x j * y s = 0 := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
