import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem galeCond_smul_map_iff {n m m' : ℕ} (g : Fin n → (Fin m → ℝ))
    (L : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m' → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (T : Set (Fin n)) :
    GaleCond (fun i => lam i • L (g i)) T ↔ GaleCond g T := by sorry

end GaleTransform
