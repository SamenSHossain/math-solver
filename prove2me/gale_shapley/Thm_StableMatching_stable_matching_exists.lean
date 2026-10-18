import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem stable_matching_exists {n : ℕ} (I : Instance n) :
    ∃ μ : Matching n, I.IsStable μ := by sorry

end StableMatching
