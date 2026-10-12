import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4

/-- **Smooth isotopies are paths in the `C^∞` topology.** If `F : ℝ × ℝⁿ → ℝⁿ` is jointly smooth
and `g t` is a diffeomorphism of `Dⁿ` rel boundary equal to `F(t,·)` for every `t ∈ [0,1]`, then
`t ↦ g t` is continuous for the `C^∞` topology on `Diff(Dⁿ rel ∂)`. -/
theorem continuous_of_smoothIsotopy (n : ℕ) (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F)
    (g : Set.Icc (0 : ℝ) 1 → DiffDisk n) (hg : ∀ t x, (g t).1 x = F ((t : ℝ), x)) :
    Continuous g := by
  sorry

end SmaleDiffS4
