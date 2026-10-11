import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- Flat-space source-free Maxwell equations for the Kerr–Newman potential in Kerr–Schild
coordinates: `∂_μ (η^{μα} η^{νβ} F_{αβ}) = 0` wherever the Kerr–Schild radius is positive. -/
theorem kerrNewman_flat_maxwell (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => ∑ α, ∑ β, minkowski μ α * minkowski ν β * kerrNewmanField a e z α β) μ y = 0 := by
  sorry

end NoHair
