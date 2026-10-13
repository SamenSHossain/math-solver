import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman field is closed.** Wherever `r > 0`, the Kerr–Newman field `F = dA` satisfies the
homogeneous Maxwell equation (Bianchi identity) `∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0`. -/
theorem kerrNewman_field_closed (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ l μ ν, coordPartial (fun z => kerrNewmanField a e z μ ν) l y
      + coordPartial (fun z => kerrNewmanField a e z ν l) μ y
      + coordPartial (fun z => kerrNewmanField a e z l μ) ν y = 0 := by
  sorry

end NoHair
