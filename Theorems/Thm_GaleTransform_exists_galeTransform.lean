import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem exists_galeTransform {n d : ℕ} (a : Fin n → (Fin d → ℝ)) :
    ∃ g : Fin n → (Fin (Module.finrank ℝ (affDep a)) → ℝ), IsGaleTransform a g := by sorry

end GaleTransform
