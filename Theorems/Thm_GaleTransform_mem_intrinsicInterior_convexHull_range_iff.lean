import Definitions.Def_GaleTransform_Defs
import Mathlib

namespace GaleTransform

theorem mem_intrinsicInterior_convexHull_range_iff {ι : Type*} [Fintype ι] {m : ℕ}
    (p : ι → (Fin m → ℝ)) (x : Fin m → ℝ) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range p)) ↔
      ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • p i = x := by sorry

end GaleTransform
