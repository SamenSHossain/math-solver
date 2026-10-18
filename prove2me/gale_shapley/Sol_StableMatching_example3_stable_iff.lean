import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

namespace StableMatching.GSEx

set_option maxRecDepth 100000 in
/-- Exhaustive check over all `3! = 6` matchings of the Wikipedia example: exactly the
matchings `A–Y, B–Z, C–X`, `A–X, B–Y, C–Z` and `A–Z, B–X, C–Y` are stable. -/
theorem example3_stable_iff_all : ∀ μ : Matching 3,
    (example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1])) := by
  decide

end StableMatching.GSEx

open StableMatching.GSEx in
theorem solution (μ : Matching 3) :
    example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1]) :=
  example3_stable_iff_all μ
