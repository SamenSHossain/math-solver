import Mathlib
import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_kerrNewman_einstein
import Theorems.Thm_NoHair_kerrNewman_maxwell
import Theorems.Thm_NoHair_kerrNewman_field_closed

open scoped ContDiff Manifold BigOperators
open Set Matrix NoHair
set_option autoImplicit false

/-- The Einstein–Maxwell system is the conjunction of the Einstein equation, the source-free
Maxwell equation and closedness of `F`; each is supplied by one child lemma. -/
theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    EinsteinMaxwellAt (kerrNewmanMetric m a e) (kerrNewmanField a e) y :=
  ⟨kerrNewman_einstein m a e y hy, kerrNewman_maxwell m a e y hy, kerrNewman_field_closed a e y hy⟩
