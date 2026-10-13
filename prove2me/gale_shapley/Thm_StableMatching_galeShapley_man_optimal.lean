import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_man_optimal {n : ℕ} (I : Instance n) (μ₀ μ : Matching n)
    (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ) (m : Fin n) :
    I.manRank m (μ₀ m) ≤ I.manRank m (μ m) := by sorry

end StableMatching
