import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem exists_linearEquiv_of_isGaleTransform {n d m m' : ℕ} (a : Fin n → (Fin d → ℝ))
    (g : Fin n → (Fin m → ℝ)) (g' : Fin n → (Fin m' → ℝ))
    (hg : IsGaleTransform a g) (hg' : IsGaleTransform a g') :
    ∃ L : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m' → ℝ), ∀ i, g' i = L (g i) := by sorry

end GaleTransform
