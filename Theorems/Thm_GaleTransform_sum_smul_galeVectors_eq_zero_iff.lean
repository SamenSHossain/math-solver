import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem sum_smul_galeVectors_eq_zero_iff {n d m : ℕ} (a : Fin n → (Fin d → ℝ))
    (g : Fin n → (Fin m → ℝ)) (hg : IsGaleTransform a g) (c : Fin n → ℝ) :
    ∑ i, c i • g i = 0 ↔ ∃ f : (Fin d → ℝ) →ᵃ[ℝ] ℝ, ∀ i, f (a i) = c i := by sorry

end GaleTransform
