import Mathlib
import Definitions.Def_NoHair_kerrNewman
import Definitions.Def_NoHair_KerrNewmanEinstein_Assembly

set_option autoImplicit false

open NoHair in
/-- The Einstein equation for the Kerr–Newman metric and field in Kerr–Schild coordinates,
assembled in the definition chain `NoHair_KerrNewmanEinstein_Base` … `Assembly`. -/
theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν :=
  NoHair.KNE.kerrNewman_einstein_holds m a e y hy
