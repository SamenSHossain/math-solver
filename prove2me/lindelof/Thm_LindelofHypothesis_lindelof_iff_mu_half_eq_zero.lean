import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_iff_mu_half_eq_zero : RiemannVonMangoldt.LindelofHypothesis ↔ mu (1 / 2) = 0 := by sorry

end LindelofHypothesis
