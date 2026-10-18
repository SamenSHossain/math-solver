import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_christoffel (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k = Gam a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k := by
  sorry

end NoHair.KNE
