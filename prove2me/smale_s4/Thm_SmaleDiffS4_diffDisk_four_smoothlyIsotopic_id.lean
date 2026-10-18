import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4

/-- **Smale's question for `D⁴`, isotopy form.** Every diffeomorphism of `D⁴` rel boundary is
smoothly isotopic to the identity rel boundary: there is a jointly smooth `F : ℝ × ℝ⁴ → ℝ⁴` with
`F(0,·) = id`, `F(1,·) = f`, and `F(t,·)` a diffeomorphism of `D⁴` rel boundary for every
`t ∈ [0,1]`. -/
theorem diffDisk_four_smoothlyIsotopic_id (f : DiffDisk 4) :
    ∃ F : ℝ × E 4 → E 4, ContDiff ℝ ∞ F ∧ (∀ x, F (0, x) = x) ∧ (∀ x, F (1, x) = f.1 x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ g : DiffDisk 4, ∀ x, g.1 x = F (t, x) := by
  sorry

end SmaleDiffS4
