import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_not_truthful_women :
    ∃ (n : ℕ) (I I' : Instance n) (w : Fin n) (μ μ' : Matching n),
      I.WomanDeviation I' w ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      I.womanPrefers w (μ'.symm w) (μ.symm w) := by sorry

end StableMatching
