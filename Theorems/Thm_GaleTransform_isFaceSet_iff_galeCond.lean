import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem isFaceSet_iff_galeCond {n d m : ℕ} (a : Fin n → (Fin d → ℝ))
    (g : Fin n → (Fin m → ℝ)) (hg : IsGaleTransform a g) (S : Set (Fin n)) (hS : S ≠ Set.univ) :
    IsFaceSet a S ↔ GaleCond g Sᶜ := by sorry

end GaleTransform
