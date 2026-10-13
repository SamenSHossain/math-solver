import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci3
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci4

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    RicS a m e R K1 K2 K3 W 1 1 = RicA a m e R K1 K2 K3 W 1 1 ∧
    RicS a m e R K1 K2 K3 W 1 2 = RicA a m e R K1 K2 K3 W 1 2 :=
  ⟨NoHair.KNE.ricS_11 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_12 a m e R K1 K2 K3 W hrel hW⟩
