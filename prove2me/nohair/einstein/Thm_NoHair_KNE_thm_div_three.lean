import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_div_three (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 3 3 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 3 ν σ) 3 y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) 3 ν σ) := by
  sorry

end NoHair.KNE
