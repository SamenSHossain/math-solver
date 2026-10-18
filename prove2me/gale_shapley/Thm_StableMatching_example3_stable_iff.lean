import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem example3_stable_iff (μ : Matching 3) :
    example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1]) := by sorry

end StableMatching
