import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem sum_galeVectors_eq_zero {n d m : ℕ} (a : Fin n → (Fin d → ℝ))
    (g : Fin n → (Fin m → ℝ)) (hg : IsGaleTransform a g) :
    ∑ i, g i = 0 ∧ ∀ k : Fin d, ∑ i, a i k • g i = 0 := by sorry

end GaleTransform
