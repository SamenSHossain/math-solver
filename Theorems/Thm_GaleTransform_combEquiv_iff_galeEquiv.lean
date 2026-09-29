import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem combEquiv_iff_galeEquiv {n d d' m m' : ℕ} (a : Fin n → (Fin d → ℝ))
    (a' : Fin n → (Fin d' → ℝ)) (g : Fin n → (Fin m → ℝ)) (g' : Fin n → (Fin m' → ℝ))
    (hg : IsGaleTransform a g) (hg' : IsGaleTransform a' g') (σ : Fin n ≃ Fin n) :
    CombEquiv a a' σ ↔ GaleEquiv g g' σ := by sorry

end GaleTransform
