import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman satisfies the Einstein equation.** Wherever `r > 0`, the Einstein tensor of the
Kerr–Newman metric equals the (8π-scaled) Maxwell stress tensor of the Kerr–Newman field. -/
theorem kerrNewman_einstein (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  sorry

end NoHair
