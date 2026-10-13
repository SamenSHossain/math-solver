import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_ricci_b (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    RicS a m e R K1 K2 K3 W 1 1 = RicA a m e R K1 K2 K3 W 1 1 ∧
    RicS a m e R K1 K2 K3 W 1 2 = RicA a m e R K1 K2 K3 W 1 2 := by
  sorry

end NoHair.KNE
