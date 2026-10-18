import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman satisfies the Einstein equation with Maxwell source.** Wherever `r > 0`, the
Einstein tensor of the Kerr–Newman metric equals `2 (F_{μα} F_ν{}^α - ¼ g_{μν} F_{αβ} F^{αβ})`. -/
theorem kerrNewman_einstein (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  sorry

end NoHair
