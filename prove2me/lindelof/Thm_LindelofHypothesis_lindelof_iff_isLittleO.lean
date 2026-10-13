import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_iff_isLittleO :
    RiemannVonMangoldt.LindelofHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] (fun t : ℝ => t ^ ε) := by sorry

end LindelofHypothesis
