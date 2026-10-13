import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Kerr–Newman satisfies the source-free Maxwell equation.** Wherever `r > 0`,
`∂_μ (√|det g| F^{μν}) = 0` for the Kerr–Newman metric `g` and field `F`. -/
theorem kerrNewman_maxwell (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(kerrNewmanMetric m a e z).det|
        * raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) z μ ν) μ y = 0 := by
  sorry

end NoHair
