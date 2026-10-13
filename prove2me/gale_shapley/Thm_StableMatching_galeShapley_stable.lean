import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_stable {n : ℕ} (I : Instance n) :
    ∃ μ : Matching n, I.IsGSOutcome μ ∧ I.IsStable μ := by sorry

end StableMatching
