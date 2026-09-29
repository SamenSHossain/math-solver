import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem finrank_affDep {n d : ℕ} (a : Fin n → (Fin d → ℝ)) (hn : 0 < n) :
    Module.finrank ℝ (affDep a) + Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 1 = n := by sorry

end GaleTransform
