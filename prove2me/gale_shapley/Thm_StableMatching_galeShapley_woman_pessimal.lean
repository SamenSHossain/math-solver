import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_woman_pessimal {n : ℕ} (I : Instance n) (μ₀ μ : Matching n)
    (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ) (w : Fin n) :
    I.womanRank w (μ.symm w) ≤ I.womanRank w (μ₀.symm w) := by sorry

end StableMatching
