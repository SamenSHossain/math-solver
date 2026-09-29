import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem combEquiv_of_galeDiagram {n d d' m m' : ℕ} (a : Fin n → (Fin d → ℝ))
    (a' : Fin n → (Fin d' → ℝ)) (g : Fin n → (Fin m → ℝ)) (g' : Fin n → (Fin m' → ℝ))
    (hg : IsGaleTransform a g) (hg' : IsGaleTransform a' g')
    (L : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m' → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (h : ∀ i, g' i = lam i • L (g i)) :
    CombEquiv a a' (Equiv.refl (Fin n)) := by sorry

end GaleTransform
