import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Christoffel

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k = Gam a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k :=
  NoHair.KNE.chr_closed m a e z hz i j k
