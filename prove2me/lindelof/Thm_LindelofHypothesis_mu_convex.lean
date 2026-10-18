import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_convex :
    ∃ f : ℝ → ℝ, ConvexOn ℝ Set.univ f ∧ ∀ σ : ℝ, mu σ = (f σ : EReal) := by sorry

end LindelofHypothesis
